/* GLIB - Library of useful routines for C programming
 * Copyright (C) 1995-1997  Peter Mattis, Spencer Kimball and Josh MacDonald
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.         See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, see <http://www.gnu.org/licenses/>.
 */

/*
 * Modified by the GLib Team and others 1997-2000.  See the AUTHORS
 * file for a list of people on the GLib Team.  See the ChangeLog
 * files for a list of changes.  These files are distributed with
 * GLib at ftp://ftp.gtk.org/pub/gtk/.
 */

/*
 * MT safe
 */

#include "config.h"

#include <execinfo.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <signal.h>
#include <locale.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/timerfd.h>
#include <sys/types.h>

#define uthash_malloc(_s) g_metrics_allocation_block_store_allocate_with_name (metrics_allocation_block_store, _s, "uthash_malloc")
#define uthash_free(_p,_s) g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, _p)
#include <uthash.h>
#include <utlist.h>
#include <utstring.h>

#include "glib-init.h"
#include "galloca.h"
#include "gbacktrace.h"
#include "gcharset.h"
#include "gconvert.h"
#include "genviron.h"
#include "gfileutils.h"
#include "gmain.h"
#include "gmem.h"
#include "gmetrics.h"
#include "gprintfint.h"
#include "gtestutils.h"
#include "gthread.h"
#include "gstdio.h"
#include "gstrfuncs.h"
#include "gstring.h"
#include "gtimer.h"

#include <sys/types.h>
#include <sys/syscall.h>
#include <unistd.h>

#include <zlib.h>

extern void *__libc_malloc (size_t size);
extern void *__libc_realloc (void *ptr, size_t size);
extern void *__libc_calloc (size_t num, size_t size);
extern void __libc_free (void *ptr);
typedef struct _GMetricsConfig GMetricsConfig;
typedef struct _GMetricsAllocationHeader GMetricsAllocationHeader;
typedef union _GMetricsAllocationBlock GMetricsAllocationBlock;
typedef struct _GMetricsAllocation GMetricsAllocation;
typedef struct _GMetricsAllocationBlockStore GMetricsAllocationBlockStore;
typedef struct _GMetricsAllocationBlockStoreIter GMetricsAllocationBlockStoreIter ;
typedef struct _GMetricsAllocationBlocksIter GMetricsAllocationBlocksIter;
typedef struct _GMetricsListNode GMetricsListNode;

#define round_to_multiple(n, m) (((n) + (((m) - 1))) & ~((m) - 1))

struct _GMetricsConfig
{
  char log_dir[1024];
  char skipped_metrics[512];
  guint collection_interval;
  int stack_trace_size;
  gsize max_allocation_block_stores;
  gsize allocation_block_store_size;
  gsize dedicated_allocation_block_store_threshold;
  guint32 metrics_enabled : 1;
};

struct _GMetricsFile
{
  gzFile gzipped_file;
  char *static_format_string;
  char *variadic_format_string;
  gdouble now;
  gulong generation;
};

struct _GMetricsAllocationHeader
{
  char name[32];
  guint32 is_freed;
  gsize number_of_blocks;
  GMetricsAllocationBlock *previous_block;
};

union _GMetricsAllocationBlock
{
  GMetricsAllocationHeader header;
  char payload[64];
};

struct _GMetricsAllocation
{
  GMetricsAllocationBlock header_block;
  GMetricsAllocationBlock payload_blocks[0];
};

struct _GMetricsAllocationBlockStore
{
  char name[128];
  char thread_name[32];
  GMetricsStackTrace *stack_trace;
  int map_fd;
  union
  {
    char *map_address;
    GMetricsAllocationBlock *blocks;
  };
  gsize size;
  gsize number_of_blocks;
  gsize number_of_allocations;
  GMetricsAllocationBlock *last_block_allocated;
  gsize total_bytes_allocated;
  guint32 is_dedicated : 1;
  guint32 is_thread_default : 1;
};

struct _GMetricsAllocationBlockStoreIter
{
  GMetricsListIter list_iter;
};

struct _GMetricsAllocationBlocksIter
{
  GMetricsAllocationBlockStore *block_store;
  GMetricsAllocationBlock *starting_block;
  GMetricsAllocationBlock *previous_block;
  gsize items_examined;
};

static void g_metrics_allocation_blocks_iter_init_after_block (GMetricsAllocationBlocksIter *iter,
                                                               GMetricsAllocationBlockStore *block_store,
                                                               GMetricsAllocationBlock      *block);
static gboolean g_metrics_allocation_blocks_iter_next (GMetricsAllocationBlocksIter  *iter,
                                                       GMetricsAllocationBlock      **next_block);

static volatile gboolean needs_flush;
static int timeout_fd = -1;
GMetricsList *timeout_handlers;
G_LOCK_DEFINE_STATIC (timeouts);
static GMetricsAllocationBlockStore store_for_allocation_block_stores;
G_LOCK_DEFINE_STATIC (allocation_block_stores);
static GMetricsAllocationBlockStore *metrics_allocation_block_store;
static __thread GMetricsList block_store_stack;
static GMetricsList allocation_block_stores;
static GMetricsFile *allocation_block_store_metrics_file;
G_LOCK_DEFINE_STATIC (allocations);

static GMetricsConfig metrics_config;

static void
int_to_string (guint64  integer,
               char    *string,
               gsize    string_size)
{
  gsize i, j, bytes_used;
  char swap_byte;

  bytes_used = 0;
  while (integer != 0 && bytes_used < string_size)
    {
      string[bytes_used++] = (integer % 10) + '0';
      integer /= 10;
    }
  string[bytes_used] = '\0';

  j = bytes_used - 1;
  for (i = 0; i < j; i++, j--)
    {
      swap_byte = string[i];
      string[i] = string[j];
      string[j] = swap_byte;
    }
}

gboolean
g_metrics_enabled (void)
{
  return metrics_config.metrics_enabled;
}

static gsize
g_metrics_allocation_block_store_get_index_of_block (GMetricsAllocationBlockStore  *block_store,
                                                     GMetricsAllocationBlock *block)
{
  return block - block_store->blocks;
}

static gboolean
g_metrics_allocation_block_store_validate_block (GMetricsAllocationBlockStore *block_store,
                                                 GMetricsAllocationBlock      *block)
{
  GMetricsAllocation *allocation;
  GMetricsAllocationHeader *header;

  allocation = (GMetricsAllocation *) block;
  header = &allocation->header_block.header;

  if (header->number_of_blocks == 0)
    return FALSE;

  if (header->number_of_blocks > block_store->number_of_blocks)
    return FALSE;

  if (header->previous_block != NULL)
    {
      GMetricsAllocationHeader *previous_header;
      previous_header = (GMetricsAllocationHeader *) header->previous_block;

      if (previous_header->number_of_blocks == 0)
        return FALSE;

      if (previous_header->number_of_blocks > block_store->number_of_blocks)
        return FALSE;

      if (header->previous_block + previous_header->number_of_blocks != block)
        return FALSE;
    }

  if (block + header->number_of_blocks < block_store->blocks + block_store->number_of_blocks)
    {
      GMetricsAllocationBlock *next_block;
      GMetricsAllocationHeader *next_header;

      next_block = block + header->number_of_blocks;
      next_header = (GMetricsAllocationHeader *) next_block;

      if (next_header->number_of_blocks == 0)
        return FALSE;

      if (next_header->number_of_blocks > block_store->number_of_blocks)
        return FALSE;

      if (next_header->previous_block != block)
        return FALSE;
    }

  return TRUE;
}

static void
g_metrics_allocation_block_store_claim_allocation (GMetricsAllocationBlockStore *block_store,
                                                   GMetricsAllocation           *allocation)
{
  GMetricsAllocationHeader *header;
  GMetricsAllocationBlock *block;

  header = &allocation->header_block.header;
  block = (GMetricsAllocationBlock *) allocation;

  header->is_freed = FALSE;
  block_store->total_bytes_allocated += header->number_of_blocks * sizeof (GMetricsAllocationBlock);
  block_store->number_of_allocations++;
  if (block_store->last_block_allocated < block)
    block_store->last_block_allocated = block;

  g_metrics_allocation_block_store_validate_block (block_store, block);
}

static void
consolidate_consecutive_blocks (GMetricsAllocationBlockStore *block_store,
                                GMetricsAllocationBlock      *block,
                                gsize                         blocks_needed)
{
  GMetricsAllocation *allocation = NULL;
  GMetricsAllocationHeader *header;
  GMetricsAllocationBlocksIter look_ahead_iter;
  GMetricsAllocationBlock *look_ahead_block;
  GMetricsAllocationBlock *next_block;

  allocation = (GMetricsAllocation *) block;
  header = &allocation->header_block.header;

  if (header->number_of_blocks >= blocks_needed)
    return;

  g_metrics_allocation_blocks_iter_init_after_block (&look_ahead_iter, block_store, block);
  while (g_metrics_allocation_blocks_iter_next (&look_ahead_iter, &look_ahead_block))
    {
      GMetricsAllocation *look_ahead_allocation;
      GMetricsAllocationHeader *look_ahead_header;

      look_ahead_allocation = (GMetricsAllocation *) look_ahead_block;
      look_ahead_header = &look_ahead_allocation->header_block.header;

      if (look_ahead_block < block)
        break;

      if (!look_ahead_header->is_freed)
        break;

      header->number_of_blocks += look_ahead_header->number_of_blocks;

      if (header->number_of_blocks >= blocks_needed)
        break;
    }

  next_block = block + header->number_of_blocks;

  if (next_block < &block_store->blocks[block_store->number_of_blocks])
    next_block->header.previous_block = block;

  g_metrics_allocation_block_store_validate_block (block_store, block);
}

static void
g_metrics_allocation_block_store_release_allocation (GMetricsAllocationBlockStore *block_store,
                                                     GMetricsAllocation           *allocation)
{
  GMetricsAllocationHeader *header;
  GMetricsAllocationBlock *block, *previous_block;

  header = &allocation->header_block.header;
  block = (GMetricsAllocationBlock *) allocation;

  header->is_freed = TRUE;
  block_store->total_bytes_allocated -= header->number_of_blocks * sizeof (GMetricsAllocationBlock);
  block_store->number_of_allocations--;

  if (block_store->last_block_allocated == block)
    block_store->last_block_allocated = header->previous_block;

  if (block->header.previous_block)
    {
      previous_block = (GMetricsAllocationBlock *) block->header.previous_block;

      if (previous_block->header.is_freed)
          consolidate_consecutive_blocks (block_store,
                                          previous_block,
                                          previous_block->header.number_of_blocks + header->number_of_blocks);
    }
}

static gboolean
g_metrics_allocation_block_store_init (GMetricsAllocationBlockStore *block_store,
                                       const char                   *name,
                                       gsize                         size)
{
  int result;
  char filename[1024] = "";

  strncpy (block_store->name, name, sizeof (block_store->name));
  block_store->size = size;

  snprintf (filename, sizeof (filename) - 1, "/var/tmp/user-%d-for-pid-%d-%s.map", getuid (), getpid (), name);

  unlink (filename);
  block_store->map_fd = open (filename, O_RDWR | O_CREAT, 0644);

  if (block_store->map_fd < 0)
    goto fail;

  result = ftruncate (block_store->map_fd, block_store->size);

  if (result < 0)
    goto fail;

  block_store->map_address = mmap (NULL, block_store->size, PROT_READ | PROT_WRITE, MAP_SHARED, block_store->map_fd, 0);

  if (block_store->map_address == MAP_FAILED)
    goto fail;

  block_store->number_of_blocks = block_store->size / sizeof (GMetricsAllocationBlock);

  block_store->blocks[0].header.number_of_blocks = block_store->number_of_blocks;
  block_store->blocks[0].header.is_freed = TRUE;

  block_store->last_block_allocated = NULL;
  block_store->total_bytes_allocated = 0;
  block_store->number_of_allocations = 0;

  return TRUE;
fail:
  if (block_store->map_fd >= 0)
    {
      close (block_store->map_fd);
      block_store->map_fd = -1;
    }
  block_store->size = 0;
  block_store->map_address = MAP_FAILED;
  return FALSE;
}

void
g_metrics_allocation_block_store_free (GMetricsAllocationBlockStore *block_store)
{
  G_LOCK (allocation_block_stores);
  munmap (block_store->map_address, block_store->size);
  block_store->map_address = MAP_FAILED;
  close (block_store->map_fd);
  block_store->map_fd = -1;
  g_metrics_list_remove_item (&allocation_block_stores, block_store);
  g_metrics_stack_trace_free (block_store->stack_trace);
  g_metrics_allocation_block_store_deallocate (&store_for_allocation_block_stores,
                                               block_store);
  G_UNLOCK (allocation_block_stores);
}

GMetricsAllocationBlockStore *
g_metrics_allocation_block_store_new (const char *name,
                                      gsize       size)
{
  GMetricsAllocationBlockStore *block_store;
  gboolean initialized;
  char thread_name[32] = "thread-";
  pid_t current_thread_id;

  current_thread_id = (pid_t) syscall (SYS_gettid);
  int_to_string (current_thread_id, thread_name + strlen (thread_name), sizeof (thread_name) - strlen (thread_name));

  if (name == NULL)
    name = thread_name;

  G_LOCK (allocation_block_stores);
  block_store = g_metrics_allocation_block_store_allocate_with_name (&store_for_allocation_block_stores,
                                                                     sizeof (GMetricsAllocationBlockStore),
                                                                     __func__);
  G_UNLOCK (allocation_block_stores);

  strncpy (block_store->thread_name, thread_name, sizeof (block_store->thread_name) - 1);

  initialized = g_metrics_allocation_block_store_init (block_store, name, size);

  if (!initialized)
    return NULL;

  G_LOCK(allocation_block_stores);
  if (metrics_allocation_block_store)
    g_metrics_list_add_item (&allocation_block_stores, block_store);
  G_UNLOCK (allocation_block_stores);

  return block_store;
}

static gboolean
g_metrics_allocation_block_store_has_allocation (GMetricsAllocationBlockStore *block_store,
                                                 gpointer                       allocation)
{
  char *allocation_bytes = allocation;
  return allocation_bytes >= block_store->map_address && allocation_bytes < (block_store->map_address + block_store->size);
}

static void
initialize_store_for_allocation_block_stores (void)
{
  g_metrics_allocation_block_store_init (&store_for_allocation_block_stores,
                                         "allocation-block-stores",
                                         metrics_config.max_allocation_block_stores * sizeof (GMetricsAllocationBlockStore));
}

static void
allocate_metrics_block_store (void)
{
  GMetricsAllocationBlockStore *block_store;

  block_store = g_metrics_allocation_block_store_new ("metrics",
                                                      metrics_config.allocation_block_store_size);

  if (block_store == NULL)
    return;

  G_LOCK (allocation_block_stores);
  metrics_allocation_block_store = block_store;
  g_metrics_list_add_item (&allocation_block_stores, metrics_allocation_block_store);
  G_UNLOCK (allocation_block_stores);
}

static void
allocate_thread_default_block_store (void)
{
  GMetricsAllocationBlockStore *block_store;

  block_store = g_metrics_allocation_block_store_new (NULL, metrics_config.allocation_block_store_size);
  block_store->is_thread_default = TRUE;
  g_metrics_push_default_allocation_block_store (block_store);
}

static void
g_metrics_allocation_block_store_iter_init (GMetricsAllocationBlockStoreIter *iter)
{
  g_metrics_list_iter_init (&iter->list_iter, &allocation_block_stores);
}

static gboolean
g_metrics_allocation_block_store_iter_next (GMetricsAllocationBlockStoreIter  *iter,
                                            GMetricsAllocationBlockStore     **block_store)
{
  return g_metrics_list_iter_next (&iter->list_iter, block_store);
}

static void
write_allocation_list (GMetricsAllocationBlockStore *block_store)
{
  GMetricsAllocationBlocksIter iter;
  GMetricsAllocationBlock *block;
  int fd = -1;

  g_metrics_allocation_blocks_iter_init_after_block (&iter, block_store, NULL);
  while (g_metrics_allocation_blocks_iter_next (&iter, &block))
    {
      GMetricsAllocation *allocation;
      GMetricsAllocationHeader *header;

      allocation = (GMetricsAllocation *) block;
      header = (GMetricsAllocationHeader *) &allocation->header_block.header;

      if (header->is_freed)
        continue;

      if (header->name[0] != '\0')
        {
          if (fd == -1)
            {
              char filename[1024] = { 0 };
              strncat (filename, metrics_config.log_dir, sizeof (filename) - 1);
              strncat (filename, "/", sizeof (filename) - 1);
              strncat (filename, block_store->name, sizeof (filename) - 1);
              strncat (filename, "-allocations.list", sizeof (filename) - 1);
              fd = open (filename, O_CREAT | O_TRUNC | O_RDWR, 0644);
            }

          write (fd, header->name, strlen (header->name));
          write (fd, "\n", 1);
        }
    }
  if (fd != -1)
    close (fd);
}

static void
on_allocation_block_stores_metrics_timeout (void)
{
  GMetricsAllocationBlockStoreIter iter;
  GMetricsAllocationBlockStore *block_store = NULL;

  if (!allocation_block_store_metrics_file)
    return;

  G_LOCK (allocation_block_stores);

  G_LOCK (allocations);
  write_allocation_list (metrics_allocation_block_store);
  G_UNLOCK (allocations);

  g_metrics_file_start_record (allocation_block_store_metrics_file);
  g_metrics_allocation_block_store_iter_init (&iter);
  while (g_metrics_allocation_block_store_iter_next (&iter, &block_store))
    {
       const char *stack_trace = NULL;

       if (block_store->map_address == MAP_FAILED)
         continue;

       if (block_store->stack_trace != NULL)
         stack_trace = g_metrics_stack_trace_get_output (block_store->stack_trace);

       g_metrics_file_add_row (allocation_block_store_metrics_file,
                               block_store->name,
                               block_store->number_of_allocations,
                               block_store->total_bytes_allocated,
                               stack_trace?: "");
    }
  g_metrics_file_end_record (allocation_block_store_metrics_file);
  G_UNLOCK (allocation_block_stores);
}

static gsize
get_int_from_environment (const char *variable,
                          gsize       default_value)
{
  const char *value;

  value = getenv (variable);

  if (value == NULL)
    return default_value;

  return strtol (variable, NULL, 10);
}

static void
load_metrics_config_command (void)
{
  static char cmdline[1024] = { 0 };
  const char *requested_command;
  int fd;

  fd = open ("/proc/self/cmdline", O_RDONLY);
  if (fd >= 0)
    {
      read (fd, cmdline, 1023);
      close (fd);
    }

  requested_command = getenv ("G_METRICS_COMMAND")? : "gnome-shell";

  metrics_config.metrics_enabled = g_str_has_suffix (cmdline, requested_command);
}

static void
load_metrics_allocation_config (void)
{
  metrics_config.max_allocation_block_stores = get_int_from_environment ("G_METRICS_MAX_ALLOCATION_BLOCK_STORES", 8192);
  metrics_config.allocation_block_store_size = get_int_from_environment ("G_METRICS_DEFAULT_ALLOCATION_BLOCK_STORE_SIZE", 10485760) * 1024L;
  metrics_config.dedicated_allocation_block_store_threshold = get_int_from_environment ("G_METRICS_DEDICATED_ALLOCATION_BLOCK_STORE_THRESHOLD", 8192);
}

static void
load_metrics_logging_config (void)
{
  const char *log_dir;

  log_dir = getenv ("G_METRICS_LOG_DIR");

  if (log_dir != NULL)
    {
      strncpy (metrics_config.log_dir, log_dir, sizeof (metrics_config.log_dir) - 1);
    }
  else
    {
      const char *cache_dir;
      char process_id[32] = "";

      cache_dir  = getenv ("XDG_CACHE_HOME");

      if (cache_dir != NULL)
        {
          strncat (metrics_config.log_dir, cache_dir, sizeof (metrics_config.log_dir));
        }
      else
        {
          strncat (metrics_config.log_dir, getenv ("HOME"), sizeof (metrics_config.log_dir));
          strncat (metrics_config.log_dir, "/.cache", sizeof (metrics_config.log_dir));
        }
      strncat (metrics_config.log_dir, "/metrics/", sizeof (metrics_config.log_dir));

       int_to_string (getpid (), process_id, sizeof (process_id));

      strncat (metrics_config.log_dir, process_id, sizeof (metrics_config.log_dir));
    }
}

static void
load_metrics_exclusions_config (void)
{
  const char *skipped_metrics;

  skipped_metrics = getenv ("G_METRICS_SKIP");

  if (skipped_metrics != NULL)
    strncpy (metrics_config.skipped_metrics,
             skipped_metrics,
             sizeof (metrics_config.skipped_metrics) - 1);
}

static void
load_metrics_collection_config (void)
{
  metrics_config.collection_interval = get_int_from_environment ("G_METRICS_COLLECTION_INTERVAL", 10);
}

static void
load_metrics_stack_trace_config (void)
{
  metrics_config.stack_trace_size = get_int_from_environment ("G_METRICS_STACK_TRACE_SIZE", 5);
}

static void
load_metrics_config (void)
{
  load_metrics_config_command ();

  if (!metrics_config.metrics_enabled)
    return;

  load_metrics_allocation_config ();
  load_metrics_logging_config ();
  load_metrics_exclusions_config ();
  load_metrics_collection_config ();
  load_metrics_stack_trace_config ();
}

static void
g_metrics_init (void)
{
  static gboolean initialized = 0;

  if (initialized)
    return;

  load_metrics_config ();

  if (!g_metrics_enabled ())
    {
      initialized = TRUE;
      return;
    }

  initialize_store_for_allocation_block_stores ();
  allocate_metrics_block_store ();
  allocate_thread_default_block_store ();

  initialized = TRUE;

  G_LOCK (timeouts);
  if (timeout_handlers == NULL)
    timeout_handlers = g_metrics_list_new ();
  G_UNLOCK (timeouts);
}

static void
g_metrics_allocation_blocks_iter_init_after_block (GMetricsAllocationBlocksIter *iter,
                                                   GMetricsAllocationBlockStore *block_store,
                                                   GMetricsAllocationBlock      *block)
{
  gsize index = 0;
  iter->block_store = block_store;

  if (block != NULL)
    {
      GMetricsAllocation *allocation;
      GMetricsAllocationHeader *header;

      allocation = (GMetricsAllocation *) block;
      header = (GMetricsAllocationHeader *) &allocation->header_block.header;

      index = g_metrics_allocation_block_store_get_index_of_block (block_store, block);
      index += header->number_of_blocks;
      index %= block_store->number_of_blocks;
    }

  iter->starting_block = &block_store->blocks[index];

  iter->previous_block = NULL;
  iter->items_examined = 0;
}

static gboolean
g_metrics_allocation_blocks_iter_next (GMetricsAllocationBlocksIter  *iter,
                                       GMetricsAllocationBlock      **next_block)
{
  GMetricsAllocationBlockStore *block_store;
  GMetricsAllocationBlock *block;

  block_store = iter->block_store;

  if (iter->previous_block == NULL)
    {
      block = iter->starting_block;
    }
  else
    {
      gsize index;
      GMetricsAllocation *previous_allocation;
      GMetricsAllocationHeader *previous_header;

      previous_allocation = (GMetricsAllocation *) iter->previous_block;
      previous_header = &previous_allocation->header_block.header;

      index = g_metrics_allocation_block_store_get_index_of_block (block_store, iter->previous_block);
      index += previous_header->number_of_blocks;
      index %= block_store->number_of_blocks;

      block = &block_store->blocks[index];
    }
  if (block == iter->starting_block && iter->items_examined > 1)
    {
      if (next_block)
        *next_block = NULL;
      return FALSE;
    }

  if (next_block)
    *next_block = block;

  iter->items_examined++;
  iter->previous_block = block;

  return TRUE;
}

static void
g_metrics_allocation_block_store_shrink_allocation (GMetricsAllocationBlockStore *block_store,
                                                    GMetricsAllocation           *allocation,
                                                    gsize                         number_of_blocks)
{
  GMetricsAllocationHeader *header;
  GMetricsAllocationBlock *first_block;
  gsize blocks_left;

  header = &allocation->header_block.header;
  first_block = (GMetricsAllocationBlock *) allocation;

  blocks_left = header->number_of_blocks - number_of_blocks;
  header->number_of_blocks = number_of_blocks;

  if (blocks_left > 0)
    {
      GMetricsAllocationBlock *next_block, *block_after_next;
      GMetricsAllocation *next_allocation;
      GMetricsAllocationHeader *next_header;

      next_block = first_block + number_of_blocks;
      next_allocation = (GMetricsAllocation *) next_block;
      next_header = &next_allocation->header_block.header;

      next_header->number_of_blocks = blocks_left;
      next_header->is_freed = TRUE;
      next_header->previous_block = first_block;

      if (block_store->last_block_allocated == next_block)
        G_BREAKPOINT ();

      block_store->total_bytes_allocated -= next_header->number_of_blocks * sizeof (GMetricsAllocationBlock);

      block_after_next = next_block + next_header->number_of_blocks;

      if (block_after_next < &block_store->blocks[block_store->number_of_blocks])
        {
          GMetricsAllocation *allocation_after_next;
          GMetricsAllocationHeader *header_after_next;

          allocation_after_next = (GMetricsAllocation *) block_after_next;
          header_after_next = &allocation_after_next->header_block.header;
          header_after_next->previous_block = next_block;
        }
    }
}

static GMetricsAllocation *
get_allocation (GMetricsAllocationBlockStore *block_store,
                gsize                         number_of_blocks,
                const char                   *name)
{
  GMetricsAllocationBlocksIter iter;
  GMetricsAllocationBlock *block;
  GMetricsAllocation *allocation = NULL;

  if (block_store->last_block_allocated != NULL && !g_metrics_allocation_block_store_validate_block (block_store, block_store->last_block_allocated))
    block_store->last_block_allocated = NULL;
  g_metrics_allocation_blocks_iter_init_after_block (&iter, block_store, block_store->last_block_allocated);
  while (g_metrics_allocation_blocks_iter_next (&iter, &block))
    {
      GMetricsAllocationHeader *header;

      allocation = (GMetricsAllocation *) block;
      header = &allocation->header_block.header;

      if (!header->is_freed)
        continue;

      consolidate_consecutive_blocks (block_store, block, number_of_blocks);

      if (header->number_of_blocks < number_of_blocks)
        continue;

      g_metrics_allocation_block_store_claim_allocation (block_store, allocation);
      if (header->number_of_blocks > number_of_blocks)
        g_metrics_allocation_block_store_shrink_allocation (block_store, allocation, number_of_blocks);

      break;
    }

  allocation = (GMetricsAllocation *) block;

  if (allocation != NULL && name != NULL)
    {
      GMetricsAllocationHeader *header;
      header = &allocation->header_block.header;
      strncpy (header->name, name, sizeof (header->name) - 1);
    }
  return allocation;
}

static gsize
calculate_blocks_needed_for_size (gsize size)
{
  GMetricsAllocation allocation;
  gsize aligned_size;
  static const gsize payload_block_size = sizeof (GMetricsAllocationBlock);

  aligned_size = sizeof (allocation.header_block) + round_to_multiple (size, payload_block_size);

  return aligned_size / payload_block_size;
}

static GMetricsAllocationBlockStore *
g_metrics_get_thread_default_allocation_block_store (void)
{
  GMetricsAllocationBlockStore *block_store;

  if (!g_metrics_enabled ())
    return NULL;

  block_store = g_metrics_list_get_last_item (&block_store_stack);

  if (block_store == NULL)
    {
      allocate_thread_default_block_store ();
      block_store = g_metrics_list_get_last_item (&block_store_stack);

      if (block_store != NULL)
        block_store->stack_trace = g_metrics_stack_trace_new (4, 5, " -> ");

    }

  return block_store;
}

static GMetricsAllocationBlockStore *
g_metrics_get_allocation_block_store_for_address (gpointer allocation)
{
  GMetricsAllocationBlockStoreIter iter;
  GMetricsAllocationBlockStore *block_store = NULL;

  g_metrics_allocation_block_store_iter_init (&iter);
  while (g_metrics_allocation_block_store_iter_next (&iter, &block_store))
    {
      if (!g_metrics_allocation_block_store_has_allocation (block_store, allocation))
        continue;

      break;
    }

  return block_store;
}

void
g_metrics_push_default_allocation_block_store (GMetricsAllocationBlockStore *block_store)
{
  g_metrics_list_add_item (&block_store_stack, block_store);
}

void
g_metrics_pop_default_allocation_block_store (void)
{
  g_metrics_list_remove_last_item (&block_store_stack);
}

gpointer
g_metrics_allocation_block_store_allocate (GMetricsAllocationBlockStore *block_store,
                                           gsize                         size)
{
  return g_metrics_allocation_block_store_allocate_with_name (block_store, size, NULL);
}

gpointer
g_metrics_allocation_block_store_allocate_with_name (GMetricsAllocationBlockStore *block_store,
                                                     gsize                         size,
                                                     const char                   *name)
{
  GMetricsAllocation *allocation;
  gsize needed_blocks;

  if (block_store->map_address == MAP_FAILED)
    return NULL;

  needed_blocks = calculate_blocks_needed_for_size (size);

  G_LOCK (allocations);
  allocation = get_allocation (block_store, needed_blocks, name);
  G_UNLOCK (allocations);

  if (allocation == NULL)
    G_BREAKPOINT ();

  memset (allocation->payload_blocks, 0, size);
  return (gpointer) allocation->payload_blocks;
}

static gboolean
g_metrics_allocation_block_store_grow_allocation (GMetricsAllocationBlockStore *block_store,
                                                  GMetricsAllocation           *allocation,
                                                  gsize                         number_of_blocks)
{
  GMetricsAllocationHeader *header;
  GMetricsAllocationBlock *first_block;
  gsize old_size;

  header = &allocation->header_block.header;
  first_block = (GMetricsAllocationBlock *) allocation;

  old_size = header->number_of_blocks * sizeof (GMetricsAllocationBlock);
  consolidate_consecutive_blocks (block_store, first_block, number_of_blocks);

  block_store->total_bytes_allocated -= old_size;
  block_store->total_bytes_allocated += header->number_of_blocks * sizeof (GMetricsAllocationBlock);

  if (header->number_of_blocks > number_of_blocks)
    g_metrics_allocation_block_store_shrink_allocation (block_store, allocation, number_of_blocks);

  return header->number_of_blocks == number_of_blocks;
}

static gsize
g_metrics_allocation_get_payload_size (GMetricsAllocation *allocation)
{
  GMetricsAllocationHeader *header;
  header = &allocation->header_block.header;

  return (header->number_of_blocks * sizeof (GMetricsAllocationBlock)) - sizeof (allocation->header_block);
}

gpointer
g_metrics_allocation_block_store_reallocate (GMetricsAllocationBlockStore *block_store,
                                             gpointer                      payload,
                                             gsize                         size)
{
  GMetricsAllocationBlock *payload_blocks;
  GMetricsAllocationBlock *first_block;
  GMetricsAllocation *allocation;
  GMetricsAllocationHeader *header;
  gsize old_size;
  gsize needed_blocks;
  gpointer new_payload;
  gboolean could_grow;

  g_metrics_init ();

  if (!g_metrics_enabled ())
    return __libc_realloc (payload, size);

  if (size == 0)
    {
      g_metrics_allocation_block_store_deallocate (block_store, payload);
      return NULL;
    }

  if (payload == NULL)
    return g_metrics_allocation_block_store_allocate_with_name (block_store, size, __func__);

  G_LOCK (allocations);
  payload_blocks = (GMetricsAllocationBlock *) payload;
  first_block = payload_blocks - offsetof (GMetricsAllocation, payload_blocks) / sizeof (GMetricsAllocationBlock);
  allocation = (GMetricsAllocation *) first_block;
  header = &allocation->header_block.header;
  needed_blocks = calculate_blocks_needed_for_size (size);

  if (needed_blocks == header->number_of_blocks)
    {
      G_UNLOCK (allocations);
      return payload;
    }

  if (needed_blocks < header->number_of_blocks)
    {
      g_metrics_allocation_block_store_shrink_allocation (block_store, allocation, needed_blocks);
      G_UNLOCK (allocations);
      return payload;
    }

  could_grow = g_metrics_allocation_block_store_grow_allocation (block_store, allocation, needed_blocks);

  G_UNLOCK (allocations);

  if (could_grow)
    return payload;

  old_size = g_metrics_allocation_get_payload_size (allocation);

  new_payload = g_metrics_allocation_block_store_allocate_with_name (block_store, size, header->name);
  memcpy (new_payload, payload, old_size);
  g_metrics_allocation_block_store_deallocate (block_store, payload);

  return new_payload;
}

gpointer
g_metrics_allocation_block_store_copy (GMetricsAllocationBlockStore *block_store,
                                       gconstpointer                 allocation,
                                       gsize                         size)
{
  return g_metrics_allocation_block_store_copy_with_name (block_store, allocation, size, __func__);
}

gpointer
g_metrics_allocation_block_store_copy_with_name (GMetricsAllocationBlockStore *block_store,
                                                 gconstpointer                 allocation,
                                                 gsize                         size,
                                                 const char                   *name)
{
  gpointer copy;

  copy = g_metrics_allocation_block_store_allocate_with_name (block_store, size, name);
  memcpy (copy, allocation, size);

  return copy;
}

__attribute__((visibility("default")))
void *
malloc (size_t size)
{
  return g_metrics_allocate (size);
}

__attribute__((visibility("default")))
void *
calloc (size_t nmemb, size_t size)
{
  return g_metrics_allocate (size * nmemb);
}

__attribute__((visibility("default")))
void *realloc (void *ptr, size_t size)
{
  return g_metrics_reallocate (ptr, size);
}

__attribute__((visibility("default")))
void
free (void *ptr)
{
  g_metrics_free (ptr);
}

void
g_metrics_allocation_block_store_deallocate (GMetricsAllocationBlockStore *block_store,
                                             gpointer                      payload)
{
  GMetricsAllocationBlock *payload_blocks;
  GMetricsAllocationBlock *first_block;
  GMetricsAllocation *allocation;
  GMetricsAllocationHeader *header;

  if (!payload)
    return;

  G_LOCK (allocations);
  payload_blocks = (GMetricsAllocationBlock *) payload;
  first_block = payload_blocks - offsetof (GMetricsAllocation, payload_blocks) / sizeof (GMetricsAllocationBlock);

  allocation = (GMetricsAllocation *) first_block;
  header = &allocation->header_block.header;

  if (header->is_freed)
    G_BREAKPOINT ();

  if (!g_metrics_allocation_block_store_validate_block (block_store, first_block))
    G_BREAKPOINT ();

  g_metrics_allocation_block_store_release_allocation (block_store, allocation);
  G_UNLOCK (allocations);

  if (block_store->total_bytes_allocated == 0 && block_store->is_dedicated)
    g_metrics_allocation_block_store_free (block_store);
}

gpointer
g_metrics_allocate (gsize size)
{
  GMetricsAllocationBlockStore *block_store = NULL;
  static gsize counter = 0;

  g_metrics_init ();

  block_store = g_metrics_get_thread_default_allocation_block_store ();
  if (block_store == NULL)
    goto fallback;

  if (block_store->map_address == MAP_FAILED)
    goto fallback;

  if (size >= metrics_config.dedicated_allocation_block_store_threshold)
    {
      GMetricsAllocationBlockStore *dedicated_block_store = NULL;
      char *name;

      asprintf (&name, "allocation-%ld-%ld", size, counter);
      counter++;

      dedicated_block_store = g_metrics_allocation_block_store_new (name, block_store->size);
      g_metrics_free (name);

      if (dedicated_block_store != NULL)
        {
          dedicated_block_store->is_dedicated = TRUE;
          dedicated_block_store->stack_trace = g_metrics_stack_trace_new (4, 5, " -> ");

          return g_metrics_allocation_block_store_allocate (dedicated_block_store, size);
        }
    }

  return g_metrics_allocation_block_store_allocate (block_store, size);

fallback:
  return __libc_calloc (1, size);
}

gpointer
g_metrics_reallocate (gpointer allocation,
                      gsize    size)
{
  GMetricsAllocationBlockStore *block_store = NULL;

  g_metrics_init ();

  block_store = g_metrics_get_allocation_block_store_for_address (allocation);
  if (block_store == NULL)
    goto fallback;

  if (block_store->map_address == MAP_FAILED)
    goto fallback;

  return g_metrics_allocation_block_store_reallocate (block_store, allocation, size);

fallback:
  return __libc_realloc (allocation, size);
}

gpointer
g_metrics_copy (gconstpointer allocation,
                gsize         size)
{
  GMetricsAllocationBlockStore *block_store = NULL;
  gpointer copy;

  g_metrics_init ();

  block_store = g_metrics_get_thread_default_allocation_block_store ();
  if (block_store == NULL)
    goto fallback;

  if (block_store->map_address == MAP_FAILED)
    goto fallback;

  return g_metrics_allocation_block_store_copy (block_store, allocation, size);

fallback:
  copy = __libc_malloc (size);
  memcpy (copy, allocation, size);
  return copy;
}

void
g_metrics_free (gpointer allocation)
{
  GMetricsAllocationBlockStore *block_store = NULL;

  if (!allocation)
    return;

  block_store = g_metrics_get_allocation_block_store_for_address (allocation);

  if (block_store != NULL)
    {
      g_metrics_allocation_block_store_deallocate (block_store, allocation);
      return;
    }

  __libc_free (allocation);
}

static void
g_metrics_file_write (GMetricsFile *metrics_file,
                      const char   *data,
                      gsize         size)
{
  gchar *buf = (gchar *) data;
  gsize to_write = size;

  while (to_write > 0)
    {
      gssize count = gzwrite (metrics_file->gzipped_file, buf, to_write);
      if (count <= 0)
        {
          if (errno != EINTR)
            return;
        }
      else
        {
          to_write -= count;
          buf += count;
        }
    }
}

static void
on_sigusr1 (int signal_number)
{
  needs_flush = TRUE;
}

GMetricsFile *
g_metrics_file_new (const char *name,
                    const char *first_column_name,
                    const char *first_column_format,
                    ...)
{
  GMetricsFile *metrics_file;
  va_list args;
  const char *column_name, *column_format;
  UT_string *format_string = NULL;
  UT_string *header_string = NULL;
  char *filename = NULL;

  g_metrics_init ();

  utstring_new (format_string);
  utstring_new (header_string);
  utstring_printf (header_string, "generation,timestamp,%s", first_column_name);

  va_start (args, first_column_format);
  do
    {
      column_name = va_arg (args, const char *);

      if (column_name == NULL)
        break;

      column_format = va_arg (args, const char *);

      utstring_printf (header_string, ",%s", column_name);
      utstring_printf (format_string, ",%s", column_format);
    }
  while (column_name != NULL);
  va_end (args);

  utstring_printf (header_string, "\n");

  metrics_file = g_metrics_allocation_block_store_allocate_with_name (metrics_allocation_block_store, sizeof (GMetricsFile), __func__);
  asprintf (&metrics_file->static_format_string, "%%lu,%%lf,%s", first_column_format);
  metrics_file->variadic_format_string = strdup (utstring_body (format_string));

  asprintf (&filename,"%s/%s.csv.gz", metrics_config.log_dir, name);
  g_mkdir_with_parents (metrics_config.log_dir, 0755);

  metrics_file->gzipped_file = gzopen (filename, "wbe");
  g_metrics_file_write (metrics_file, utstring_body (header_string), utstring_len (header_string));
  utstring_free (format_string);
  utstring_free (header_string);
  free (filename);

  signal (SIGUSR1, on_sigusr1);

  return metrics_file;
}

void
g_metrics_file_start_record (GMetricsFile *metrics_file)
{
  metrics_file->now = ((long double) g_get_real_time ()) / (1.0 * G_USEC_PER_SEC);
}

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wformat-nonliteral"
void
g_metrics_file_add_row_without_cast (GMetricsFile  *metrics_file,
                                     gconstpointer  first_column_value,
                                     ...)

{
  va_list args;
  gsize row_length = 0, buffer_left = 0, buffer_written = 0;
  char *row;

  row_length += snprintf (NULL, 0, metrics_file->static_format_string, metrics_file->generation, metrics_file->now, first_column_value);

  va_start (args, first_column_value);
  row_length += vsnprintf (NULL, 0, metrics_file->variadic_format_string, args);
  va_end (args);

  row_length++;

  buffer_left = row_length + 1;
  row = g_metrics_allocation_block_store_allocate_with_name (metrics_allocation_block_store, buffer_left, __func__);

  buffer_written += snprintf (row, buffer_left, metrics_file->static_format_string, metrics_file->generation, metrics_file->now, first_column_value);
  buffer_left -= buffer_written;

  va_start (args, first_column_value);
  buffer_written += vsnprintf (row + buffer_written, buffer_left, metrics_file->variadic_format_string, args);
  buffer_left -= buffer_written;
  va_end (args);
  *(row + buffer_written) = '\n';

  g_metrics_file_write (metrics_file, row, row_length);
  g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, row);
}
#pragma GCC diagnostic pop

void
g_metrics_file_end_record (GMetricsFile *metrics_file)
{
  metrics_file->generation++;

  if (needs_flush)
    {
      gzflush (metrics_file->gzipped_file, Z_FULL_FLUSH);
    }
  else if ((metrics_file->generation % 10) == 0)
    {
      gzflush (metrics_file->gzipped_file, Z_PARTIAL_FLUSH);
    }
}

void
g_metrics_file_free (GMetricsFile *metrics_file)
{
  gzclose (metrics_file->gzipped_file);
  free (metrics_file->static_format_string);
  free (metrics_file->variadic_format_string);
  g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, metrics_file);
}

struct _GMetricsTableEntry
{
  UT_hash_handle hh;
  char *name;
  gpointer record;
};

struct _GMetricsTable
{
  gsize record_size;
  GMetricsTableEntry *entries;
};

GMetricsTable *
g_metrics_table_new (gsize record_size)
{
  GMetricsTable *table;

  g_metrics_init ();

  table = g_metrics_allocation_block_store_allocate_with_name (metrics_allocation_block_store, sizeof (GMetricsTable), __func__);
  table->record_size = record_size;

  return table;
}

void
g_metrics_table_set_record (GMetricsTable *metrics_table,
                            const char    *name,
                            gpointer       record)
{
  GMetricsTableEntry *entry = NULL;

  HASH_FIND_STR (metrics_table->entries, name, entry);

  if (entry == NULL)
    {
      entry = g_metrics_allocation_block_store_allocate_with_name (metrics_allocation_block_store, sizeof (GMetricsTableEntry), __func__);
      entry->name = g_metrics_allocation_block_store_copy_with_name (metrics_allocation_block_store, name, strlen (name) + 1, __func__);
      entry->record = g_metrics_allocation_block_store_copy_with_name (metrics_allocation_block_store, record, metrics_table->record_size, __func__);

      HASH_ADD_KEYPTR (hh, metrics_table->entries, entry->name, strlen (entry->name), entry);
    }
  else
    {
      gpointer old_record;
      old_record = entry->record;
      entry->record = g_metrics_allocation_block_store_copy_with_name (metrics_allocation_block_store, record, metrics_table->record_size, __func__);
      g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, old_record);
    }
}

gpointer
g_metrics_table_get_record (GMetricsTable *metrics_table,
                            const char    *name)
{
  GMetricsTableEntry *entry = NULL;

  HASH_FIND_STR (metrics_table->entries, name, entry);

  if (entry == NULL)
    return NULL;

  return entry->record;
}

void
g_metrics_table_remove_record (GMetricsTable *metrics_table,
                               const char    *name)
{

  GMetricsTableEntry *entry = NULL;

  HASH_FIND_STR (metrics_table->entries, name, entry);

  if (entry == NULL)
    return;

  HASH_DEL (metrics_table->entries, entry);
  g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, entry->name);
  g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, entry->record);
  g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, entry);
}

void
g_metrics_table_clear (GMetricsTable *metrics_table)
{
  GMetricsTableEntry *entry = NULL, *next_entry = NULL;

  HASH_ITER (hh, metrics_table->entries, entry, next_entry)
    {
      HASH_DEL (metrics_table->entries, entry);
      g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, entry->name);
      g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, entry->record);
      g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, entry);
    }
}

void
g_metrics_table_free (GMetricsTable *metrics_table)
{
  g_metrics_table_clear (metrics_table);
  g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, metrics_table);
}

void
g_metrics_table_iter_init (GMetricsTableIter *iter,
                           GMetricsTable     *table)
{
  iter->entry = table->entries;
}

static int
comparison_wrapper (GMetricsTableEntry *entry_1,
                    GMetricsTableEntry *entry_2,
                    GCompareFunc        comparison_function)
{
  return comparison_function (entry_1->record, entry_2->record);
}

void
g_metrics_table_sorted_iter_init (GMetricsTableIter *iter,
                                  GMetricsTable     *table,
                                  GCompareFunc       comparison_function)
{
  HASH_SRT_DATA (hh, table->entries, comparison_wrapper, comparison_function);
  iter->entry = table->entries;
}

gboolean
g_metrics_table_iter_next_without_cast (GMetricsTableIter  *iter,
                                        const char        **name,
                                        gpointer           *record)
{
  if (iter->entry == NULL)
    {
      if (name)
        *name = NULL;
      return FALSE;
    }

  if (name)
    *name = (const char *) iter->entry->name;

  if (iter->entry->record == NULL)
    G_BREAKPOINT ();

  if (record)
    *record = iter->entry->record;

  iter->entry = iter->entry->hh.next;
  return TRUE;
}

gboolean
g_metrics_requested (const char *name)
{
  if (!g_metrics_enabled ())
    return FALSE;

  if (strstr (metrics_config.skipped_metrics, name) != NULL)
    return FALSE;

  return TRUE;
}

void
g_metrics_start_timeout (GMetricsTimeoutFunc timeout_handler)
{
  G_LOCK (timeouts);

  if (timeout_fd < 0)
    {
      struct itimerspec timer_spec = { { 0 } };

      timer_spec.it_interval.tv_sec = metrics_config.collection_interval;
      timer_spec.it_value.tv_sec = metrics_config.collection_interval;

      timeout_fd = timerfd_create (CLOCK_MONOTONIC, TFD_NONBLOCK | TFD_CLOEXEC);
      if (timeout_fd >= 0)
        {
          int result;
          result = timerfd_settime (timeout_fd, 0, &timer_spec, NULL);

          if (result < 0)
            {
              close (timeout_fd);
              timeout_fd = -1;
            }
        }
    }

  g_metrics_list_add_item (timeout_handlers, timeout_handler);

  G_UNLOCK (timeouts);
}

static void
init_allocation_block_stores_metrics (void)
{
  static gboolean initialized;
  static gboolean needs_allocation_block_store_metrics;

  if (initialized)
    return;

  initialized = TRUE;
  needs_allocation_block_store_metrics = g_metrics_requested ("allocation-block-stores");

  if (!needs_allocation_block_store_metrics)
    return;

  allocation_block_store_metrics_file = g_metrics_file_new ("allocation-block-stores",
                                                            "name", "%s",
                                                            "number of allocations", "%ld",
                                                            "total size", "%ld",
                                                            "stack trace", "%s",
                                                            NULL);
  g_metrics_start_timeout (on_allocation_block_stores_metrics_timeout);
}

void
g_metrics_run_timeout_handlers (void)
{
  GMetricsListIter iter;
  GMetricsTimeoutFunc handler;

  guint64 number_of_expirations;

  read (timeout_fd, &number_of_expirations, sizeof (number_of_expirations));

  init_allocation_block_stores_metrics ();

  G_LOCK (timeouts);
  g_metrics_list_iter_init (&iter, timeout_handlers);
  while (g_metrics_list_iter_next (&iter, &handler))
    {
      if (handler != NULL)
        handler ();
    }
  G_UNLOCK (timeouts);

  needs_flush = FALSE;
}

struct _GMetricsListNode
{
  gpointer item;
  struct _GMetricsListNode *prev;
  struct _GMetricsListNode *next;
};

struct _GMetricsList
{
  struct _GMetricsListNode *first_node;
  gsize number_of_nodes;
};

GMetricsList *
g_metrics_list_new (void)
{
  GMetricsList *list;

  g_metrics_init ();

  list = g_metrics_allocation_block_store_allocate_with_name (metrics_allocation_block_store, sizeof (GMetricsList), __func__);

  return list;
}

void
g_metrics_list_add_item (GMetricsList *list,
                         gpointer      item)
{
  GMetricsListNode *node;

  node = g_metrics_allocation_block_store_allocate_with_name (metrics_allocation_block_store, sizeof (GMetricsListNode), __func__);
  node->item = item;

  DL_APPEND (list->first_node, node);
  list->number_of_nodes++;
}

void
g_metrics_list_remove_item (GMetricsList *list,
                            gpointer      item_to_remove)
{
  GMetricsListNode *node = NULL;

  DL_SEARCH_SCALAR (list->first_node, node, item, item_to_remove);

  if (node != NULL)
    {
      DL_DELETE (list->first_node, node);
      list->number_of_nodes--;
    }
}

gpointer
g_metrics_list_get_last_item (GMetricsList *list)
{
  GMetricsListNode *last_node = NULL;

  if (list->number_of_nodes == 0)
    return NULL;

  last_node = list->first_node->prev;

  return last_node->item;
}

void
g_metrics_list_remove_last_item (GMetricsList *list)
{
  GMetricsListNode *last_node = NULL;

  if (list->number_of_nodes == 0)
    return;

  last_node = list->first_node->prev;

  DL_DELETE (list->first_node, last_node);
  list->number_of_nodes--;
}

gsize
g_metrics_list_get_length (GMetricsList *list)
{
  return list->number_of_nodes;
}

void
g_metrics_list_free (GMetricsList *list)
{
  GMetricsListNode *node, *next_node;

  DL_FOREACH_SAFE (list->first_node, node, next_node)
    {
      DL_DELETE (list->first_node, node);
      g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, node);
    }
  g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, list);
}

void
g_metrics_list_iter_init (GMetricsListIter *iter,
                          GMetricsList     *list)
{
  iter->node = list->first_node;

  if (iter->node != NULL)
    iter->next_node = iter->node->next;
}

gboolean
g_metrics_list_iter_next_without_cast (GMetricsListIter *iter,
                                       gpointer         *item)
{
  if (iter->node == NULL)
    {
      *item = NULL;
      return FALSE;
    }

  *item = iter->node->item;

  iter->node = iter->next_node;

  if (iter->node != NULL)
    iter->next_node = iter->node->next;
  return TRUE;
}

struct _GMetricsStackTrace
{
  gpointer *frames;
  int start_frame;
  int number_of_frames;
  char *delimiter;
  char *output;
};

GMetricsStackTrace *
g_metrics_stack_trace_new (int start_frame,
                           int number_of_frames,
                           const char *delimiter)
{
  GMetricsStackTrace *stack_trace;
  int total_frames_needed;

  stack_trace = g_metrics_allocation_block_store_allocate_with_name (metrics_allocation_block_store, sizeof (GMetricsStackTrace), __func__);
  total_frames_needed = start_frame + number_of_frames;
  stack_trace->frames = g_metrics_allocation_block_store_allocate_with_name (metrics_allocation_block_store, sizeof (gpointer) * (total_frames_needed), __func__);
  stack_trace->number_of_frames = backtrace (stack_trace->frames, total_frames_needed);
  stack_trace->start_frame = start_frame;
  stack_trace->delimiter = g_metrics_allocation_block_store_copy (metrics_allocation_block_store, delimiter, strlen (delimiter) + 1);

  return stack_trace;
}

const char *
g_metrics_stack_trace_get_output (GMetricsStackTrace *stack_trace)
{
  if (stack_trace->output == NULL)
    {
      UT_string *output_string = NULL;
      char **symbols = NULL;
      int i;

      symbols = backtrace_symbols (stack_trace->frames, stack_trace->number_of_frames);

      if (symbols == NULL)
        return NULL;

      utstring_new (output_string);
      for (i = stack_trace->start_frame; i < stack_trace->number_of_frames; i++)
        utstring_printf (output_string, "%s%s", symbols[i], stack_trace->delimiter);
      stack_trace->output = g_metrics_allocation_block_store_copy (metrics_allocation_block_store, utstring_body (output_string), utstring_len (output_string) + 1);
      utstring_free (output_string);
      g_metrics_free (symbols);
    }

  return stack_trace->output;
}

void
g_metrics_stack_trace_free (GMetricsStackTrace *stack_trace)
{
  if (stack_trace == NULL)
    return;
  g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, stack_trace->frames);
  g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, stack_trace->output);
  g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, stack_trace->delimiter);
  g_metrics_allocation_block_store_deallocate (metrics_allocation_block_store, stack_trace);
}

char *
g_metrics_stack_trace (void)
{
  GMetricsStackTrace *stack_trace;
  const char *output;

  stack_trace = g_metrics_stack_trace_new (2, metrics_config.stack_trace_size, " -> ");
  output = g_metrics_stack_trace_get_output (stack_trace);
  g_metrics_stack_trace_free (stack_trace);

  if (output == NULL)
    return NULL;

  return g_metrics_allocation_block_store_copy (metrics_allocation_block_store, output, strlen (output) + 1);
}

int
g_metrics_get_timeout_fd (void)
{
  return timeout_fd;
}
