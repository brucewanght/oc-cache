/*
 * Copyright (C) 2012 Red Hat, Inc.
 *
 * This file is released under the GPL.
 */

#ifndef DM_CACHE_BLOCK_TYPES_H
#define DM_CACHE_BLOCK_TYPES_H

#include "persistent-data/dm-block-manager.h"

/*----------------------------------------------------------------*/

/*
 * It's helpful to get sparse to differentiate between indexes into the
 * origin device, indexes into the cache device, and indexes into the
 * discard bitset.
 */

typedef dm_block_t __bitwise dm_oblock_t;
typedef uint32_t __bitwise dm_cblock_t;

#ifdef CONFIG_DM_MULTI_USER
/* dm_cache_block struct record the logical number of cache block 
 * and if this block is hot. For now, false means cold and true means hot. 
 * The cbn is cache block logical number on hot device or cold device.
 */
typedef uint32_t __bitwise dm_cbn_t;
typedef struct
{
	dm_cbn_t cbn;   /* cache block number in policy and metadata */
	dm_cbn_t dbn;   /* cache block number on cache device */
	bool hot;       /* cache block heat, for now 0 means cold, 1 means hot */
}dm_cblock_t;

/* we modified the dm_cblock_t struct, so we need some new auxiliary functions */
static inline dm_cblock_t to_cblock(dm_cbn_t cbn, dm_cbn_t dbn, bool hot)
{
	dm_cblock_t cblock;
	cblock.cbn = cbn;
	cblock.dbn = dbn;
	cblock.hot = hot;
	return cblock;
}

static inline dm_cbn_t to_cbn(uint32_t b)
{
	return (__force dm_cbn_t) b;
}

static inline uint32_t from_cbn(dm_cbn_t b)
{
	return (__force uint32_t) b;
}

/* return logical cache block number from dm_cblock_t */
static inline dm_cbn_t from_cblock(dm_cblock_t b)
{
	return (__force dm_cbn_t)(b.cbn);
}
#else
typedef dm_block_t __bitwise dm_dblock_t;

static inline dm_oblock_t to_oblock(dm_block_t b)
{
	return (__force dm_oblock_t) b;
}

static inline dm_block_t from_oblock(dm_oblock_t b)
{
	return (__force dm_block_t) b;
}
#endif

static inline dm_cblock_t to_cblock(uint32_t b)
{
	return (__force dm_cblock_t) b;
}

static inline uint32_t from_cblock(dm_cblock_t b)
{
	return (__force uint32_t) b;
}

static inline dm_dblock_t to_dblock(dm_block_t b)
{
	return (__force dm_dblock_t) b;
}

static inline dm_block_t from_dblock(dm_dblock_t b)
{
	return (__force dm_block_t) b;
}

#endif /* DM_CACHE_BLOCK_TYPES_H */
