/*
 * Copyright (C) 2018 Wang Haitao. All rights reserved.
 *
 * This file is released under the GPL.
 * WHT added: modified from slru in dm-cache,
 * slru author Joe Thornber <dm-devel@redhat.com>
 */

#include "dm-cache-background-tracker.h"
#include "dm-cache-policy-internal.h"
#include "dm-cache-policy.h"
#include "dm.h"

#include <linux/hash.h>
#include <linux/jiffies.h>
#include <linux/module.h>
#include <linux/mutex.h>
#include <linux/vmalloc.h>
#include <linux/math64.h>

#define DM_MSG_PREFIX "cache-policy-lru"

/*----------------------------------------------------------------*/

struct entry {
	unsigned hash_next:28;
	unsigned prev:28;
	unsigned next:28;
	bool dirty:1;
	bool allocated:1;
	bool sentinel:1;
	bool pending_work:1;
	bool hot:1;
	dm_cbn_t dbn;

	dm_oblock_t oblock;
};

/*----------------------------------------------------------------*/

#define INDEXER_NULL ((1u << 28u) - 1u)

/*
 * An entry_space manages a set of entries that we use for the queues.
 * The clean and dirty queues share entries, so this object is separate
 * from the queue itself.
 */
struct entry_space {
	struct entry *begin;
	struct entry *end;
};

static int space_init(struct entry_space *es, unsigned nr_entries)
{
	if (!nr_entries) {
		es->begin = es->end = NULL;
		return 0;
	}

	es->begin = vzalloc(sizeof(struct entry) * nr_entries);
	if (!es->begin)
		return -ENOMEM;

	es->end = es->begin + nr_entries;
	return 0;
}

static void space_exit(struct entry_space *es)
{
	vfree(es->begin);
}

static struct entry *__get_entry(struct entry_space *es, unsigned block)
{
	struct entry *e;

	e = es->begin + block;
	BUG_ON(e >= es->end);

	return e;
}

static unsigned to_index(struct entry_space *es, struct entry *e)
{
	BUG_ON(e < es->begin || e >= es->end);
	return e - es->begin;
}

static struct entry *to_entry(struct entry_space *es, unsigned block)
{
	if (block == INDEXER_NULL)
		return NULL;

	return __get_entry(es, block);
}

/*----------------------------------------------------------------*/

struct ilist {
	unsigned nr_elts;	/* excluding sentinel entries */
	unsigned head, tail;
};

static void l_init(struct ilist *l)
{
	l->nr_elts = 0;
	l->head = l->tail = INDEXER_NULL;
}

static struct entry *l_head(struct entry_space *es, struct ilist *l)
{
	return to_entry(es, l->head);
}

static struct entry *l_tail(struct entry_space *es, struct ilist *l)
{
	return to_entry(es, l->tail);
}

static struct entry *l_next(struct entry_space *es, struct entry *e)
{
	return to_entry(es, e->next);
}

static struct entry *l_prev(struct entry_space *es, struct entry *e)
{
	return to_entry(es, e->prev);
}

static bool l_empty(struct ilist *l)
{
	return l->head == INDEXER_NULL;
}

static void l_add_head(struct entry_space *es, struct ilist *l, struct entry *e)
{
	struct entry *head = l_head(es, l);

	e->next = l->head;
	e->prev = INDEXER_NULL;

	if (head)
		head->prev = l->head = to_index(es, e);
	else
		l->head = l->tail = to_index(es, e);

	if (!e->sentinel)
		l->nr_elts++;
}

static void l_add_tail(struct entry_space *es, struct ilist *l, struct entry *e)
{
	struct entry *tail = l_tail(es, l);

	e->next = INDEXER_NULL;
	e->prev = l->tail;

	if (tail)
		tail->next = l->tail = to_index(es, e);
	else
		l->head = l->tail = to_index(es, e);

	if (!e->sentinel)
		l->nr_elts++;
}

static void l_del(struct entry_space *es, struct ilist *l, struct entry *e)
{
	struct entry *prev = l_prev(es, e);
	struct entry *next = l_next(es, e);

	if (prev)
		prev->next = e->next;
	else
		l->head = e->next;

	if (next)
		next->prev = e->prev;
	else
		l->tail = e->prev;

	if (!e->sentinel)
		l->nr_elts--;
}

static struct entry *l_pop_tail(struct entry_space *es, struct ilist *l)
{
	struct entry *e;

	for (e = l_tail(es, l); e; e = l_prev(es, e))
		if (!e->sentinel) {
			l_del(es, l, e);
			return e;
		}

	return NULL;
}

/*----------------------------------------------------------------*/

/* lru queue struct */
struct queue {
	struct entry_space *es;
	unsigned nr_elts;
	struct ilist qs;
};

/* init the lru queue */
static void q_init(struct queue *q, struct entry_space *es)
{
	q->es = es;
	q->nr_elts = 0;
	l_init(&q->qs);
}

/* get the number of elements in lru queue */
static unsigned q_size(struct queue *q)
{
	return q->nr_elts;
}

/* Insert an entry to the back of the queue */
static void q_push(struct queue *q, struct entry *e)
{
	BUG_ON(e->pending_work);

	if (!e->sentinel)
		q->nr_elts++;

	l_add_tail(q->es, &q->qs, e);
}

/* Insert an entry to the front of the queue */
static void q_push_front(struct queue *q, struct entry *e)
{
	BUG_ON(e->pending_work);

	if (!e->sentinel)
		q->nr_elts++;

	l_add_head(q->es, &q->qs, e);
}

/* delete an entry from queue */
static void q_del(struct queue *q, struct entry *e)
{
	l_del(q->es, &q->qs, e);
	if (!e->sentinel)
		q->nr_elts--;
}

/* Return the oldest entry */
static struct entry *q_peek(struct queue *q, bool can_cross_sentinel)
{
	struct entry *e;

	for (e = l_head(q->es, &q->qs); e; e = l_next(q->es, e)) {
		if (e->sentinel) {
			if (can_cross_sentinel)
				continue;
			else
				break;
		}

		return e;
	}

	return NULL;
}

/*----------------------------------------------------------------*/

/* record the statistic of lru */
struct stats {
	unsigned hits;
	unsigned misses;
};

static void stats_init(struct stats *s)
{
	s->hits = 0u;
	s->misses = 0u;
}

static void stats_reset(struct stats *s)
{
	s->hits = s->misses = 0u;
}

static void stats_hit(struct stats *s)
{
	s->hits++;
}

static void stats_miss(struct stats *s)
{
	s->misses++;
}

/*----------------------------------------------------------------*/

/* hash table for lru */
struct lru_hash_table {
	struct entry_space *es;
	unsigned long long hash_bits;
	unsigned *buckets;
};

/*
 * All cache entries are stored in a chained hash table.  To save space we
 * use indexing again, and only store indexes to the next entry.
 */
static int h_init(struct lru_hash_table *ht, struct entry_space *es, unsigned nr_entries)
{
	unsigned i, nr_buckets;

	ht->es = es;
	nr_buckets = roundup_pow_of_two(max(nr_entries / 4u, 16u));
	ht->hash_bits = __ffs(nr_buckets);

	ht->buckets = vmalloc(sizeof(*ht->buckets) * nr_buckets);
	if (!ht->buckets)
		return -ENOMEM;

	for (i = 0; i < nr_buckets; i++)
		ht->buckets[i] = INDEXER_NULL;

	return 0;
}

static void h_exit(struct lru_hash_table *ht)
{
	vfree(ht->buckets);
}

static struct entry *h_head(struct lru_hash_table *ht, unsigned bucket)
{
	return to_entry(ht->es, ht->buckets[bucket]);
}

static struct entry *h_next(struct lru_hash_table *ht, struct entry *e)
{
	return to_entry(ht->es, e->hash_next);
}

static void __h_insert(struct lru_hash_table *ht, unsigned bucket, struct entry *e)
{
	e->hash_next = ht->buckets[bucket];
	ht->buckets[bucket] = to_index(ht->es, e);
}

static void h_insert(struct lru_hash_table *ht, struct entry *e)
{
	unsigned h = hash_64(from_oblock(e->oblock), ht->hash_bits);
	__h_insert(ht, h, e);
}

static struct entry *__h_lookup(struct lru_hash_table *ht, unsigned h, dm_oblock_t oblock,
				struct entry **prev)
{
	struct entry *e;
	*prev = NULL;
	for (e = h_head(ht, h); e; e = h_next(ht, e)) {
		if (e->oblock == oblock)
			return e;
		*prev = e;
	}
	return NULL;
}

static void __h_unlink(struct lru_hash_table *ht, unsigned h,
		       struct entry *e, struct entry *prev)
{
	if (prev)
		prev->hash_next = e->hash_next;
	else
		ht->buckets[h] = e->hash_next;
}

/*
 * Also moves each entry to the front of the bucket.
 */
static struct entry *h_lookup(struct lru_hash_table *ht, dm_oblock_t oblock)
{
	struct entry *e, *prev;
	unsigned h = hash_64(from_oblock(oblock), ht->hash_bits);

	e = __h_lookup(ht, h, oblock, &prev);
	if (e && prev) {
		/*
		 * Move to the front because this entry is likely
		 * to be hit again.
		 */
		__h_unlink(ht, h, e, prev);
		__h_insert(ht, h, e);
	}
	return e;
}

static void h_remove(struct lru_hash_table *ht, struct entry *e)
{
	unsigned h = hash_64(from_oblock(e->oblock), ht->hash_bits);
	struct entry *prev;

	/*
	 * The down side of using a singly linked list is we have to
	 * iterate the bucket to remove an item.
	 */
	e = __h_lookup(ht, h, e->oblock, &prev);
	if (e)
		__h_unlink(ht, h, e, prev);
}

/*----------------------------------------------------------------*/

/* allocator for hash entry */
struct entry_alloc {
	struct entry_space *es;
	unsigned begin;
	unsigned nr_allocated;
	struct ilist free;
};

static void init_allocator(struct entry_alloc *ea, struct entry_space *es,
			   unsigned begin, unsigned end)
{
	unsigned i;

	ea->es = es;
	ea->nr_allocated = 0u;
	ea->begin = begin;

	l_init(&ea->free);
	for (i = begin; i != end; i++)
		l_add_tail(ea->es, &ea->free, __get_entry(ea->es, i));
	
}

static void init_entry(struct entry *e)
{
	e->hash_next = INDEXER_NULL;
	e->next = INDEXER_NULL;
	e->prev = INDEXER_NULL;
	e->dirty = true;	/* FIXME: audit */
	e->allocated = true;
	e->sentinel = false;
	e->pending_work = false;
}

static struct entry *alloc_entry(struct entry_alloc *ea)
{
	struct entry *e;

	if (l_empty(&ea->free))
		return NULL;

	e = l_pop_tail(ea->es, &ea->free);
	init_entry(e);
	ea->nr_allocated++;

	return e;
}

/* This assumes the cblock hasn't already been allocated */
static struct entry *alloc_particular_entry(struct entry_alloc *ea, unsigned i)
{
	struct entry *e = __get_entry(ea->es, ea->begin + i);

	BUG_ON(e->allocated);

	l_del(ea->es, &ea->free, e);
	init_entry(e);
	ea->nr_allocated++;

	return e;
}

static void free_entry(struct entry_alloc *ea, struct entry *e)
{
	BUG_ON(!ea->nr_allocated);
	BUG_ON(!e->allocated);

	ea->nr_allocated--;
	e->allocated = false;
	l_add_tail(ea->es, &ea->free, e);
}

static bool allocator_empty(struct entry_alloc *ea)
{
	return l_empty(&ea->free);
}

static unsigned get_index(struct entry_alloc *ea, struct entry *e)
{
	return to_index(ea->es, e) - ea->begin;
}

static struct entry *get_entry(struct entry_alloc *ea, unsigned index)
{
	return __get_entry(ea->es, ea->begin + index);
}

/*----------------------------------------------------------------*/

#define WRITEBACK_PERIOD (10ul * HZ)
#define DEMOTE_PERIOD (60ul * HZ)
#define CACHE_UPDATE_PERIOD (60ul * HZ)

struct lru_policy {
	struct dm_cache_policy policy;

	/* protects everything */
	spinlock_t lock;
	dm_cbn_t cache_size;
	dm_cbn_t hot_cache_size;
	dm_cbn_t cold_cache_size;
	sector_t cache_block_size;
	uint32_t hot_level;
	unsigned long *hot_cache_bits;  /* monitor hot cache device allocation */
	unsigned long *cold_cache_bits; /* monitor cold cache device allocation */

	struct entry_space es;
	struct entry_alloc writeback_sentinel_alloc;
	struct entry_alloc demote_sentinel_alloc;
	struct entry_alloc cache_alloc;
	unsigned long *cache_hit_bits;

	/*
	 * We maintain two queues of entries.  The cache proper,
	 * consisting of a clean and dirty queue, containing the currently
	 * active mappings.
	 */
	struct queue clean;
	struct queue dirty;
	struct stats cache_stats;

	/*
	 * Keeps track of time, incremented by the core.  We use this to
	 * avoid attributing multiple hits within the same tick.
	 */
	unsigned tick;

	/*
	 * The hash tables allows us to quickly find an entry by origin
	 * block.
	 */
	struct lru_hash_table table;

	bool current_writeback_sentinels;
	unsigned long next_writeback_period;

	bool current_demote_sentinels;
	unsigned long next_demote_period;
	unsigned long next_cache_period;

	struct background_tracker *bg_work;

	bool migrations_allowed;
};

/*----------------------------------------------------------------*/

static struct entry *get_sentinel(struct entry_alloc *ea, bool which)
{
	return get_entry(ea,which);
}

static struct entry *writeback_sentinel(struct lru_policy *lru)
{
	return get_sentinel(&lru->writeback_sentinel_alloc, lru->current_writeback_sentinels);
}

static struct entry *demote_sentinel(struct lru_policy *lru)
{
	return get_sentinel(&lru->demote_sentinel_alloc, lru->current_demote_sentinels);
}

static void __update_writeback_sentinels(struct lru_policy *lru)
{
	struct queue *q = &lru->dirty;
	struct entry *sentinel;

	sentinel = writeback_sentinel(lru);
	q_del(q, sentinel);
	q_push(q, sentinel);
}

static void __update_demote_sentinels(struct lru_policy *lru)
{
	struct queue *q = &lru->clean;
	struct entry *sentinel;

	sentinel = demote_sentinel(lru);
	q_del(q, sentinel);
	q_push(q, sentinel);
}

static void update_sentinels(struct lru_policy *lru)
{
	if (time_after(jiffies, lru->next_writeback_period)) {
		lru->next_writeback_period = jiffies + WRITEBACK_PERIOD;
		lru->current_writeback_sentinels = !lru->current_writeback_sentinels;
		__update_writeback_sentinels(lru);
	}

	if (time_after(jiffies, lru->next_demote_period)) {
		lru->next_demote_period = jiffies + DEMOTE_PERIOD;
		lru->current_demote_sentinels = !lru->current_demote_sentinels;
		__update_demote_sentinels(lru);
	}
}

static void __sentinels_init(struct lru_policy *lru)
{
	struct entry *sentinel;

	sentinel = writeback_sentinel(lru);
	q_push(&lru->dirty, sentinel);

	sentinel = demote_sentinel(lru);
	q_push(&lru->clean, sentinel);
}

static void sentinels_init(struct lru_policy *lru)
{
	lru->next_writeback_period = jiffies + WRITEBACK_PERIOD;
	lru->next_demote_period = jiffies + DEMOTE_PERIOD;

	lru->current_writeback_sentinels = false;
	lru->current_demote_sentinels = false;
	__sentinels_init(lru);

	lru->current_writeback_sentinels = !lru->current_writeback_sentinels;
	lru->current_demote_sentinels = !lru->current_demote_sentinels;
	__sentinels_init(lru);
}

/*----------------------------------------------------------------*/

static void del_queue(struct lru_policy *lru, struct entry *e)
{
	q_del(e->dirty ? &lru->dirty : &lru->clean, e);
}

static void push_queue(struct lru_policy *lru, struct entry *e)
{
	if (e->dirty)
		q_push(&lru->dirty, e);
	else
		q_push(&lru->clean, e);
}

// !h, !q, a -> h, q, a
static void push(struct lru_policy *lru, struct entry *e)
{
	h_insert(&lru->table, e);
	if (!e->pending_work)
		push_queue(lru, e);
}

static void push_queue_front(struct lru_policy *lru, struct entry *e)
{
	if (e->dirty)
		q_push_front(&lru->dirty, e);
	else
		q_push_front(&lru->clean, e);
}

static void push_front(struct lru_policy *lru, struct entry *e)
{
	h_insert(&lru->table, e);
	if (!e->pending_work)
		push_queue_front(lru, e);
}

static dm_cblock_t infer_cblock(struct lru_policy *lru, struct entry *e)
{
	dm_cblock_t cblock;
	cblock.cbn = to_cbn(get_index(&lru->cache_alloc, e));
	cblock.dbn = e->dbn;
	cblock.hot = e->hot;
	return cblock;
}

static void requeue(struct lru_policy *lru, struct entry *e)
{
	/*
	 * Pending work has temporarily been taken out of the queues.
	 */
	if (e->pending_work)
		return;

	/* set the hit bit */
	if (!test_and_set_bit(from_cblock(infer_cblock(lru, e)), lru->cache_hit_bits)) {
		if (!e->dirty) {
			/* if the entry is clean, then move it to the front of clean queue */
			q_del(&lru->clean, e);
			q_push(&lru->clean, e);
			return;
		}
		else
		{
			/* if the entry is dirty, then move it to the front of dirty queue */
			q_del(&lru->dirty, e);
			q_push(&lru->dirty, e);
			return;
		}

	}
}

static void end_cache_period(struct lru_policy *lru)
{
	if (time_after(jiffies, lru->next_cache_period)) {
		clear_bitset(lru->cache_hit_bits, from_cbn(lru->cache_size));
		stats_reset(&lru->cache_stats);
		lru->next_cache_period = jiffies + CACHE_UPDATE_PERIOD;
	}
}

/*----------------------------------------------------------------*/

/*
 * Targets are given as a percentage.
 */
#define CLEAN_TARGET 25u
#define FREE_TARGET 25u

static unsigned percent_to_target(struct lru_policy *lru, unsigned p)
{
	return from_cbn(lru->cache_size) * p / 100u;
}

static bool clean_target_met(struct lru_policy *lru, bool idle)
{
	/*
	 * Cache entries may not be populated.  So we cannot rely on the
	 * size of the clean queue.
	 */
	if (idle) {
		/*
		 * We'd like to clean everything.
		 */
		return q_size(&lru->dirty) == 0u;
	}

	/*
	 * If we're busy we don't worry about cleaning at all.
	 */
	return true;
}

static bool free_target_met(struct lru_policy *lru)
{
	unsigned nr_free;

	nr_free = from_cbn(lru->cache_size) - lru->cache_alloc.nr_allocated;
	return (nr_free + btracker_nr_demotions_queued(lru->bg_work)) >=
		percent_to_target(lru, FREE_TARGET);
}

/*----------------------------------------------------------------*/

static void mark_pending(struct lru_policy *lru, struct entry *e)
{
	BUG_ON(e->sentinel);
	BUG_ON(!e->allocated);
	BUG_ON(e->pending_work);
	e->pending_work = true;
}

static void clear_pending(struct lru_policy *lru, struct entry *e)
{
	BUG_ON(!e->pending_work);
	e->pending_work = false;
}

static void queue_writeback(struct lru_policy *lru)
{
	int r;
	struct policy_work work;
	struct entry *e;

	e = q_peek(&lru->dirty, !lru->migrations_allowed);
	if (e) {
		mark_pending(lru, e);
		q_del(&lru->dirty, e);

		work.op = POLICY_WRITEBACK;
		work.oblock = e->oblock;
		work.cblock = infer_cblock(lru, e);

		r = btracker_queue(lru->bg_work, &work, NULL);
		WARN_ON_ONCE(r); // FIXME: finish, I think we have to get rid of this race.
	}
}

static void queue_demotion(struct lru_policy *lru)
{
	struct policy_work work;
	struct entry *e;

	if (unlikely(WARN_ON_ONCE(!lru->migrations_allowed)))
		return;

	e = q_peek(&lru->clean, true);
	if (!e) {
		if (!clean_target_met(lru, true))
			queue_writeback(lru);
		return;
	}

	mark_pending(lru, e);
	q_del(&lru->clean, e);

	work.op = POLICY_DEMOTE;
	work.oblock = e->oblock;
	work.cblock = infer_cblock(lru, e);
	btracker_queue(lru->bg_work, &work, NULL);
}

static void queue_promotion(struct lru_policy *lru, dm_oblock_t oblock,
			    struct policy_work **workp)
{
	struct entry *e;
	struct policy_work work;

	if (!lru->migrations_allowed)
		return;

	if (allocator_empty(&lru->cache_alloc)) {
		/*
		 * We always claim to be 'idle' to ensure some demotions happen
		 * with continuous loads.
		 */
		if (!free_target_met(lru))
			queue_demotion(lru);
		return;
	}

	if (btracker_promotion_already_present(lru->bg_work, oblock))
		return;

	/*
	 * We allocate the entry now to reserve the cblock.  If the
	 * background work is aborted we must remember to free it.
	 */
	e = alloc_entry(&lru->cache_alloc);
	BUG_ON(!e);
	e->pending_work = true;
	work.op = POLICY_PROMOTE;
	work.oblock = oblock;
	work.cblock = infer_cblock(lru, e);
	/* set hot bit according position in queue */

	if (work.cblock.cbn >= lru->hot_level)
	{
		e->hot = false;
		/* find a empty block on cold cache device */
		e->dbn = find_first_zero_bit(lru->cold_cache_bits, lru->cold_cache_size);
		if (test_and_set_bit(e->dbn, lru->cold_cache_bits))
			DMERR("queue_promotion: fail to set cold bit for e.dbn = %u", e->dbn);

	}
	else 
	{
		e->hot = true;
		/* find a empty block on hot cache device */
		e->dbn = find_first_zero_bit(lru->hot_cache_bits, lru->hot_cache_size);
		if (test_and_set_bit(e->dbn, lru->hot_cache_bits))
			DMERR("queue_promotion: fail to set hot bit for e.dbn = %u", e->dbn);
	}
	btracker_queue(lru->bg_work, &work, workp);
}

/*----------------------------------------------------------------*/

enum promote_result {
	PROMOTE_NOT,
	PROMOTE_TEMPORARY,
	PROMOTE_PERMANENT
};

/*
 * Converts a boolean into a promote result.
 */
static enum promote_result maybe_promote(bool promote)
{
	return promote ? PROMOTE_PERMANENT : PROMOTE_NOT;
}

static enum promote_result should_promote(struct lru_policy *lru, struct entry *hs_e,
					  int data_dir, bool fast_promote)
{
	if (data_dir == WRITE) {
		if (!allocator_empty(&lru->cache_alloc) && fast_promote)
			return PROMOTE_TEMPORARY;

		return maybe_promote(true);
	} else
		return maybe_promote(true);
}


/*----------------------------------------------------------------*/

/*
 * Public interface, via the policy struct.  See dm-cache-policy.h for a
 * description of these.
 */

static struct lru_policy *to_lru_policy(struct dm_cache_policy *p)
{
	return container_of(p, struct lru_policy, policy);
}

static dm_cbn_t lru_get_nrblock(struct dm_cache_policy *p)
{
	dm_cbn_t r;
	unsigned long flags;
	struct lru_policy *lru = to_lru_policy(p);

	spin_lock_irqsave(&lru->lock, flags);
	r = to_cbn(lru->cache_size);
	spin_unlock_irqrestore(&lru->lock, flags);

	return r;
}

static void lru_destroy(struct dm_cache_policy *p)
{
	struct lru_policy *lru = to_lru_policy(p);

	btracker_destroy(lru->bg_work);
	h_exit(&lru->table);
	free_bitset(lru->cache_hit_bits);
	space_exit(&lru->es);
	kfree(lru);
}

/*----------------------------------------------------------------*/

static int __lookup(struct lru_policy *lru, dm_oblock_t oblock, dm_cblock_t *cblock,
		    int data_dir, bool fast_copy,
		    struct policy_work **work, bool *background_work)
{
	struct entry *e;
	enum promote_result pr;

	*background_work = false;

	e = h_lookup(&lru->table, oblock);
	if (e) {
		stats_hit(&lru->cache_stats);
		requeue(lru, e);
		*cblock = infer_cblock(lru, e);
		return 0;

	} else {
		stats_miss(&lru->cache_stats);
		pr = should_promote(lru, e, data_dir, fast_copy);
		if (pr != PROMOTE_NOT) {
			queue_promotion(lru, oblock, work);
			*background_work = true;
		}

		return -ENOENT;
	}
}

static int lru_lookup(struct dm_cache_policy *p, dm_oblock_t oblock, dm_cblock_t *cblock,
		      int data_dir, bool fast_copy,
		      bool *background_work)
{
	int r;
	unsigned long flags;
	struct lru_policy *lru = to_lru_policy(p);

	spin_lock_irqsave(&lru->lock, flags);
	r = __lookup(lru, oblock, cblock,
		     data_dir, fast_copy,
		     NULL, background_work);
	spin_unlock_irqrestore(&lru->lock, flags);

	return r;
}

static int lru_lookup_with_work(struct dm_cache_policy *p,
				dm_oblock_t oblock, dm_cblock_t *cblock,
				int data_dir, bool fast_copy,
				struct policy_work **work)
{
	int r;
	bool background_queued;
	unsigned long flags;
	struct lru_policy *lru = to_lru_policy(p);

	spin_lock_irqsave(&lru->lock, flags);
	r = __lookup(lru, oblock, cblock, data_dir, fast_copy, work, &background_queued);
	spin_unlock_irqrestore(&lru->lock, flags);

	return r;
}

static int lru_get_background_work(struct dm_cache_policy *p, bool idle,
				   struct policy_work **result)
{
	int r;
	unsigned long flags;
	struct lru_policy *lru = to_lru_policy(p);

	spin_lock_irqsave(&lru->lock, flags);
	r = btracker_issue(lru->bg_work, result);
	if (r == -ENODATA) {
		if (!clean_target_met(lru, idle)) {
			queue_writeback(lru);
			r = btracker_issue(lru->bg_work, result);
		}
	}
	spin_unlock_irqrestore(&lru->lock, flags);

	return r;
}

/*
 * We need to clear any pending work flags that have been set, and in the
 * case of promotion free the entry for the destination cblock.
 */
static void __complete_background_work(struct lru_policy *lru,
				       struct policy_work *work,
				       bool success)
{
	struct entry *e = get_entry(&lru->cache_alloc,
				    from_cblock(work->cblock));

	switch (work->op) {
	case POLICY_PROMOTE:
		// !h, !q, a
		clear_pending(lru, e);
		if (success) {
			e->oblock = work->oblock;
			push(lru, e);
			// h, q, a
		} else {
			free_entry(&lru->cache_alloc, e);
			// !h, !q, !a
		}
		break;

	case POLICY_DEMOTE:
		// h, !q, a
		if (success) {
			h_remove(&lru->table, e);
			free_entry(&lru->cache_alloc, e);
			// !h, !q, !a
		} else {
			clear_pending(lru, e);
			push_queue(lru, e);
			// h, q, a
		}
		break;

	case POLICY_WRITEBACK:
		// h, !q, a
		clear_pending(lru, e);
		push_queue(lru, e);
		// h, q, a
		break;
	}

	btracker_complete(lru->bg_work, work);
}

static void lru_complete_background_work(struct dm_cache_policy *p,
					 struct policy_work *work,
					 bool success)
{
	unsigned long flags;
	struct lru_policy *lru = to_lru_policy(p);

	spin_lock_irqsave(&lru->lock, flags);
	__complete_background_work(lru, work, success);
	spin_unlock_irqrestore(&lru->lock, flags);
}

// in_hash(oblock) -> in_hash(oblock)
static void __lru_set_clear_dirty(struct lru_policy *lru, dm_cblock_t cblock, bool set)
{
	struct entry *e = get_entry(&lru->cache_alloc, from_cblock(cblock));

	if (e->pending_work)
		e->dirty = set;
	else {
		del_queue(lru, e);
		e->dirty = set;
		push_queue(lru, e);
	}
}

static void lru_set_dirty(struct dm_cache_policy *p, dm_cblock_t cblock)
{
	unsigned long flags;
	struct lru_policy *lru = to_lru_policy(p);

	spin_lock_irqsave(&lru->lock, flags);
	__lru_set_clear_dirty(lru, cblock, true);
	spin_unlock_irqrestore(&lru->lock, flags);
}

static void lru_clear_dirty(struct dm_cache_policy *p, dm_cblock_t cblock)
{
	struct lru_policy *lru = to_lru_policy(p);
	unsigned long flags;

	spin_lock_irqsave(&lru->lock, flags);
	__lru_set_clear_dirty(lru, cblock, false);
	spin_unlock_irqrestore(&lru->lock, flags);
}

static int lru_load_mapping(struct dm_cache_policy *p,
			    dm_oblock_t oblock, dm_cblock_t cblock,
			    bool dirty, uint32_t hint, bool hint_valid)
{
	struct lru_policy *lru = to_lru_policy(p);
	struct entry *e;

	e = alloc_particular_entry(&lru->cache_alloc, from_cblock(cblock));
	e->oblock = oblock;
	e->dirty = dirty;
	e->pending_work = false;

	/* WHT added: set hot bit and cache device block number for entry */
	e->hot = cblock.hot;
	e->dbn = cblock.dbn;
	/* we allocate correspondind block to entry, so we need to mark it through
	 * seting bit to 1
	 */
	if (e->hot)
		set_bit(e->dbn, lru->hot_cache_bits);
	else
		set_bit(e->dbn, lru->cold_cache_bits);
	/*
	 * When we load mappings we push ahead of both sentinels in order to
	 * allow demotions and cleaning to occur immediately.
	 */
	push_front(lru, e);

	return 0;
}

static int lru_invalidate_mapping(struct dm_cache_policy *p, dm_cbn_t cblock)
{
	struct lru_policy *lru = to_lru_policy(p);
	struct entry *e = get_entry(&lru->cache_alloc, from_cbn(cblock));

	if (!e->allocated)
		return -ENODATA;

	// FIXME: what if this block has pending background work?
	/* we want to remove this entry, so we mark its cache block bit to 0 so as 
	 * to make it available for allocation. 
	 */
	if (e->hot)
		clear_bit(e->dbn, lru->hot_cache_bits);
	else
		clear_bit(e->dbn, lru->cold_cache_bits);
	del_queue(lru, e);
	h_remove(&lru->table, e);
	free_entry(&lru->cache_alloc, e);
	return 0;
}

static uint32_t lru_get_hint(struct dm_cache_policy *p, dm_cbn_t cblock)
{
	struct lru_policy *lru = to_lru_policy(p);
	struct entry *e = get_entry(&lru->cache_alloc, from_cbn(cblock));

	if (!e->allocated)
		return 0;

	return 1;
}

static dm_cbn_t lru_residency(struct dm_cache_policy *p)
{
	dm_cbn_t r;
	unsigned long flags;
	struct lru_policy *lru = to_lru_policy(p);

	spin_lock_irqsave(&lru->lock, flags);
	r = to_cbn(lru->cache_alloc.nr_allocated);
	spin_unlock_irqrestore(&lru->lock, flags);

	return r;
}

static void lru_tick(struct dm_cache_policy *p, bool can_block)
{
	struct lru_policy *lru = to_lru_policy(p);
	unsigned long flags;

	spin_lock_irqsave(&lru->lock, flags);
	lru->tick++;
	update_sentinels(lru);
	end_cache_period(lru);
	spin_unlock_irqrestore(&lru->lock, flags);
}

static void lru_allow_migrations(struct dm_cache_policy *p, bool allow)
{
	struct lru_policy *lru = to_lru_policy(p);
	lru->migrations_allowed = allow;
}

/* Init the policy plugin interface function pointers. */
static void init_policy_functions(struct lru_policy *lru)
{
	lru->policy.get_nrblock = lru_get_nrblock;
	lru->policy.destroy = lru_destroy;
	lru->policy.lookup = lru_lookup;
	lru->policy.lookup_with_work = lru_lookup_with_work;
	lru->policy.get_background_work = lru_get_background_work;
	lru->policy.complete_background_work = lru_complete_background_work;
	lru->policy.set_dirty = lru_set_dirty;
	lru->policy.clear_dirty = lru_clear_dirty;
	lru->policy.load_mapping = lru_load_mapping;
	lru->policy.invalidate_mapping = lru_invalidate_mapping;
	lru->policy.get_hint = lru_get_hint;
	lru->policy.residency = lru_residency;
	lru->policy.tick = lru_tick;
	lru->policy.allow_migrations = lru_allow_migrations;
}

static struct dm_cache_policy *__lru_create(dm_cbn_t hot_cache_size,
		                dm_cbn_t cold_cache_size,
					    sector_t origin_size,
					    sector_t cache_block_size,
					    bool migrations_allowed)
{
	unsigned i;
	unsigned nr_sentinels_per_queue = 128u;
	unsigned total_sentinels = 2u * nr_sentinels_per_queue;
	struct lru_policy *lru = kzalloc(sizeof(*lru), GFP_KERNEL);

	if (!lru)
		return NULL;

    /* WHT added: use bitsets to manage block allocation for hot cache and
     * cold cache device.
     */
	lru->hot_level = hot_cache_size;
    lru->hot_cache_size = hot_cache_size;
	lru->cold_cache_size = cold_cache_size;
	/* allocate hot cache bitset */
	lru->hot_cache_bits = alloc_bitset(lru->hot_cache_size); 
	if (!lru->hot_cache_bits) {
		DMERR("couldn't allocate hot cache bitset");
		return NULL;
	}
	/* allocate cold cache bitset */
	lru->cold_cache_bits = alloc_bitset(lru->cold_cache_size); 
	if (!lru->hot_cache_bits) {
		DMERR("couldn't allocate cold cache bitset");
		return NULL;
	}

	init_policy_functions(lru);
	lru->cache_size = hot_cache_size + cold_cache_size;
	lru->cache_block_size = cache_block_size;

	if (space_init(&lru->es, total_sentinels + from_cbn(lru->cache_size))) {
		DMERR("couldn't initialize entry space");
		goto bad_pool_init;
	}

	init_allocator(&lru->writeback_sentinel_alloc, &lru->es, 0, nr_sentinels_per_queue);
	for (i = 0; i < nr_sentinels_per_queue; i++)
		get_entry(&lru->writeback_sentinel_alloc, i)->sentinel = true;

	init_allocator(&lru->demote_sentinel_alloc, &lru->es, nr_sentinels_per_queue, total_sentinels);
	for (i = 0; i < nr_sentinels_per_queue; i++)
		get_entry(&lru->demote_sentinel_alloc, i)->sentinel = true;

	init_allocator(&lru->cache_alloc, &lru->es,
		       total_sentinels, total_sentinels + from_cbn(lru->cache_size));

	if (from_cbn(lru->cache_size)) {
		lru->cache_hit_bits = alloc_bitset(from_cbn(lru->cache_size));
		if (!lru->cache_hit_bits) {
			DMERR("couldn't allocate cache hit bitset");
			goto bad_alloc_table;
		}
		clear_bitset(lru->cache_hit_bits, from_cbn(lru->cache_size));
	} else
		lru->cache_hit_bits = NULL;

	lru->tick = 0;
	spin_lock_init(&lru->lock);

	q_init(&lru->clean, &lru->es);
	q_init(&lru->dirty, &lru->es);
	stats_init(&lru->cache_stats);

	if (h_init(&lru->table, &lru->es, from_cbn(lru->cache_size)))
		goto bad_alloc_table;

	sentinels_init(lru);

	lru->next_cache_period = jiffies;

	lru->bg_work = btracker_create(10240); /* FIXME: hard coded value */
	if (!lru->bg_work)
		goto bad_alloc_table;

	lru->migrations_allowed = migrations_allowed;

	return &lru->policy;

bad_alloc_table:
	free_bitset(lru->cache_hit_bits);
bad_pool_init:
	kfree(lru);

	return NULL;
}

static struct dm_cache_policy *lru_create(dm_cbn_t hot_cache_size,
		              dm_cbn_t cold_cache_size,
					  sector_t origin_size,
					  sector_t cache_block_size)
{
	return __lru_create(hot_cache_size, cold_cache_size, origin_size, cache_block_size, true);
}


static struct dm_cache_policy *lru_cleaner_create(dm_cbn_t hot_cache_size,
		              dm_cbn_t cold_cache_size,
					  sector_t origin_size,
					  sector_t cache_block_size)
{
	return __lru_create(hot_cache_size, cold_cache_size, origin_size, cache_block_size, false);
}

/*----------------------------------------------------------------*/

static struct dm_cache_policy_type lru_policy_type = {
	.name = "lru",
	.version = {1, 0, 0},
	.hint_size = 4,
	.owner = THIS_MODULE,
	.create = lru_create
};

static struct dm_cache_policy_type lru_cleaner_policy_type = {
	.name = "lru_cleaner",
	.version = {1, 0, 0},
	.hint_size = 4,
	.owner = THIS_MODULE,
	.create = lru_cleaner_create
};

static int __init lru_init(void)
{
	int r;

	r = dm_cache_policy_register(&lru_policy_type);
	if (r) {
		DMERR("register failed %d", r);
		goto out_lru;
	}

	r = dm_cache_policy_register(&lru_cleaner_policy_type);
	if (r) {
		DMERR("register failed %d", r);
		goto out_lru_cleaner;
	}
	return 0;

out_lru_cleaner:
	dm_cache_policy_unregister(&lru_cleaner_policy_type);
out_lru:
	dm_cache_policy_unregister(&lru_policy_type);
	return -ENOMEM;
}

static void __exit lru_exit(void)
{
	dm_cache_policy_unregister(&lru_cleaner_policy_type);
	dm_cache_policy_unregister(&lru_policy_type);
}

module_init(lru_init);
module_exit(lru_exit);

MODULE_AUTHOR("Wang Haitao <brucewanght@gmail.com>");
MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("lru cache policy");

