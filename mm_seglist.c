#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* =============================================================================== */

team_t team = {
  /* Team name */
  "",
  /* First member's full name */
  "",
  /* First member's email address */
  "",
  /* Second member's full name (leave blank if none) */
  "",
  /* Second member's email address (leave blank if none) */
  ""
};

/* ========================== Function Prototype =============================== */

inline static void* resize_block(void*, size_t);
inline static void* reallocate_block(void*, size_t);
inline static int can_expand(void*, size_t);
inline static void* expand_block(void*, size_t);
inline static void chop_block(void*, size_t);
inline static void* extend_heap(size_t);
inline static void* first_fit(void*, size_t);
inline static void* best_fit(void*, size_t);
inline static void* find_fit(size_t);
inline static void* place(void*, size_t);
inline static void* coalesce(void*);
inline static void link_block(void*);
inline static void unlink_block(void*);
inline static int seg_index(size_t);

/* ========================== Compilation Flags =============================== */

// #define DEBUG                 /* uncomment to turn-on heap checker */

#ifdef DEBUG
  static void mm_check(int);
  static void check_seglist(int, int);
  static int check_free_list(int, int);
  #define heap_check(line) (mm_check(line))
#else
  #define heap_check(line)
#endif
//NOTE at 236: two contiguous free blocks not coalesced 식으로 heap 체크 가능
/* ================================ Macros ===================================== */

#define WSIZE 4                           /* Word size in bytes */
#define DSIZE 8                           /* Double word size in bytes */
#define CHUNKSIZE (1<<8)                  /* Minimum heap allocation size */
#define MIN_BLOCK_SIZE 16                 /* Minimum block size */
#define ALIGNMENT 8                       /* Payload Alignment */
#define DSIZE 8                     /* The Number of lists in the seglist */
#define WTYPE u_int32_t                   /* Word type */
#define BYTE char                         /* Byte type */

/* ------------------------------ Basic Utility ------------------------------- */

/* Move the address ptr by offset bytes */
#define MOVE_BYTE(ptr, offset) ((WTYPE *)((BYTE *)(ptr) + (offset)))
/* Move the address ptr by offset words */
#define MOVE_WORD(ptr, offset) ((WTYPE *)(ptr) + (offset))
/* Read a word from address ptr */
#define READ_WORD(ptr) (*(WTYPE *)(ptr))
/* Write a word value to address ptr */
#define WRITE_WORD(ptr, value) (*(WTYPE *)(ptr) = (value))
/* rounds up size (in bytes) to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
/* Get the maximum of x and y */
#define MAX(x, y) (((x) > (y))? (x) : (y))
/* Get the minimum of x and y */
#define MIN(x, y) (((x) < (y))? (x) : (y))

/* ----------------------- Header/Footer Macros ---------------------------- */

/* Pack the size and allocated-bit into a word */
#define PACK(size, alloc) ((size) | (alloc))
/* Read the size from header/footer word at address Hptr */
#define READ_SIZE(Hptr) (READ_WORD(Hptr) & ~0x7)
/* Read the allocated-bit from header/footer word at address Hptr */
#define READ_ALLOC(Hptr) (READ_WORD(Hptr) & 0x1)
/* Write the size and allocation-bit to the word at address Hptr */
#define WRITE(Hptr, size, alloc) (WRITE_WORD((Hptr), PACK((size), (alloc))))
/* Write the size to the word at address Hptr */
#define WRITE_SIZE(Hptr, size) (WRITE((Hptr), (size), READ_ALLOC(Hptr)))
/* Write allocation-bit to the word at address Hptr */
#define WRITE_ALLOC(Hptr, alloc) (WRITE((Hptr), READ_SIZE(Hptr), (alloc)))

/* ---------------------------- Payload Macros ------------------------------ */

/* Get the header-word pointer from the payload pointer bp */
#define HEADER(bp) (MOVE_WORD(bp, -1))
/* Get the footer-word pointer from the payload pointer bp */
#define FOOTER(bp) (MOVE_BYTE(bp, PAYLOAD_SIZE(bp)))
/* Get next block payload pointer from bp (current payload pointer) */
#define NEXT_BLOCK(bp) (MOVE_BYTE(bp, BLOCK_SIZE(bp)))
/* Get previous block payload pointer from bp (current payload pointer) */
#define PREV_BLOCK(bp) (MOVE_BYTE(bp, - READ_SIZE(MOVE_WORD(bp, -2))))
/* Read the block size at the payload bp */
#define BLOCK_SIZE(bp) (READ_SIZE(HEADER(bp)))
/* Read the payload size at bp */
#define PAYLOAD_SIZE(bp) (BLOCK_SIZE(bp) - DSIZE)
/* Check if the block at the payload bp is free */
#define IS_FREE(bp) (!(READ_ALLOC(HEADER(bp))))

/* Sets the size and allocation-bit to header/footer of block at bp */
#define SET_INFO(bp, size, alloc)\
  ((WRITE(HEADER(bp),(size),(alloc))), \
   (WRITE(FOOTER(bp),(size),(alloc))))

/* Sets the size to header/footer of block at bp */
#define SET_SIZE(bp, size)\
  ((WRITE_SIZE(HEADER(bp),(size))), \
   (WRITE_SIZE(FOOTER(bp),(size))))

/* Sets the allocation-bit to header/footer of block at bp */
#define SET_ALLOC(bp, alloc)\
  ((WRITE_ALLOC(HEADER(bp),(alloc))), \
   (WRITE_ALLOC(FOOTER(bp),(alloc))))

/* Get the predecessor payload address */
#define GET_PREV(bp) ((WTYPE *)(READ_WORD(bp)))
/* Get the successor payload address */
#define GET_NEXT(bp) ((WTYPE *)(READ_WORD(MOVE_WORD(bp, 1))))
/* Set the predecessor payload address to pred_bp */
#define PREV_FBLK(bp, pred_bp) (WRITE_WORD(bp, ((WTYPE) pred_bp)))
/* Set the successor payload address to succ_bp */
#define NEXT_FBLK(bp, succ_bp) (WRITE_WORD(MOVE_WORD(bp, 1), ((WTYPE) succ_bp)))

/* ======================= Private Global Variables ============================== */
// private global variable
static WTYPE** seglist;       /* array of free-list pointers */
/* =========================== Public Functions ================================== */

/* 
 * Initialize the malloc package.
 * return 0 on success, -1 on error.
 */
int mm_init(void) {
  /* Create the initial empty heap */
  void* heap = mem_sbrk((DSIZE + 2) * WSIZE); /* seglist + head + tail */
  if (heap == (void*)-1) return -1;

  seglist = heap;
  heap = MOVE_WORD(heap, DSIZE);
  // initialize the seglist
  for(int i = 0; i < DSIZE; ++i){
    seglist[i] = NULL;
  }

  WRITE(heap, 0, 1);                          /* Head Word */
  WRITE(MOVE_WORD(heap, 1), 0, 1);            /* Tail Word */

  /* Extend the empty heap with a small free block */
  if (extend_heap(4 * MIN_BLOCK_SIZE) == NULL) return -1;
  heap_check(__LINE__);
  return 0;
}

/* 
 *  Allocate an aligned block of memory of at least size bytes
 *  Return address of allocated block on success, NULL on error.
 */
void* mm_malloc(size_t size) {
  if (size == 0) return NULL;
  void* bp;                             /* Payload Pointer */
  size = ALIGN(size + DSIZE);           /* Add header and footer words */
  size = MAX(size, MIN_BLOCK_SIZE);

  /* Search the free list for a fit */
  if ((bp = find_fit(size)) == NULL) {
    /* No fit found, request a block from the memory */
    if (size > CHUNKSIZE){
      bp = extend_heap(size);
    }else{
      bp = extend_heap(4 * CHUNKSIZE);
      chop_block(bp, size);
    }
    if (bp == NULL) return NULL;
  }

  bp = place(bp, size);
  heap_check(__LINE__);
  return bp;
}

/*
 * Free the allocated block at ptr, and coalesce it.
 */
void mm_free(void* ptr) {
  SET_ALLOC(ptr, 0);
  // link_block(ptr);
  coalesce(ptr);
  heap_check(__LINE__);
}

/*
 * # ptr = NULL : allocate block of the given size.
 * # size = 0 : free the given block, return NULL.
 * # else: resize the allocated block at ptr.
 * 
 * Return address of the reallocated block, NULL on error.
 */
void* mm_realloc(void* ptr, size_t size) {
  if (size == 0 || ptr == NULL){
    mm_free(ptr);
    return NULL;
  }else{
    ptr = resize_block(ptr, size);
    heap_check(__LINE__);
    return ptr;
  }
}

/* =========================== Private Functions ================================== */

/*
 * Resize the allocated block at bp to have size bytes
 * Return address of the resized block, NULL on error.
 */
static void* resize_block(void* bp, size_t size) {
  size_t asize = MAX(MIN_BLOCK_SIZE, ALIGN(size + DSIZE));
  size_t bsize = BLOCK_SIZE(bp);
  size_t csize = bsize - asize;

  if (asize > bsize) {
    if (can_expand(bp, asize))
      return expand_block(bp, asize);
    return reallocate_block(bp, size);
  }

  // Split only if the fragment is large enough.
  if (csize >= (MIN_BLOCK_SIZE)){
    SET_INFO(bp, asize, 1);
    void* fp = NEXT_BLOCK(bp);
    SET_INFO(fp, csize, 0);
    link_block(fp);
  }

  return bp;
}

/*
 * Allocate block of the given size, copy content, free old block
 * Return address of the new block, NULL on error.
 */
static void* reallocate_block(void* ptr, size_t size) {
  void *newptr = mm_malloc(size);
  if (newptr == NULL) return NULL;
  // size_t copy_size = MIN(PAYLOAD_SIZE(ptr), size);
  memcpy(newptr, ptr, PAYLOAD_SIZE(ptr));
  mm_free(ptr);
  return newptr;
}

/**
 * checks if the allocated-block at bp can expand to have the given size
 */
static int can_expand(void* bp, size_t size){
  size_t bsize = BLOCK_SIZE(bp);

  for(void* ptr = NEXT_BLOCK(bp); IS_FREE(ptr) ; ptr = NEXT_BLOCK(ptr)){
    bsize += BLOCK_SIZE(ptr);
    if (bsize >= size) return 1;
  }

  for(void* ptr = bp; !READ_ALLOC(MOVE_WORD(ptr, -2)) ; ){
    ptr = PREV_BLOCK(ptr);
    bsize += BLOCK_SIZE(ptr);
    if (bsize >= size) return 1;
  }

  return 0;
}

/**
 * expands the allocated-block at bp until it has the given size
 * return address to the new expanded block
*/
static void* expand_block(void *bp, size_t size) {
  void* cbp = bp;
  size_t bsize = BLOCK_SIZE(bp);

  for(void* ptr = NEXT_BLOCK(bp); IS_FREE(ptr) ; ptr = NEXT_BLOCK(ptr)){
    bsize += BLOCK_SIZE(ptr);
    unlink_block(ptr);
    if (bsize >= size) {
      SET_INFO(cbp, bsize, 1);
      return cbp;
    }
  }

  for(void* ptr = bp; !READ_ALLOC(MOVE_WORD(ptr, -2)) ; ){
    cbp = ptr = PREV_BLOCK(ptr);
    bsize += BLOCK_SIZE(ptr);
    unlink_block(ptr);
    if (bsize >= size) {
      memmove(cbp, bp, PAYLOAD_SIZE(bp));
      SET_INFO(cbp, bsize, 1);
      return cbp;
    }
  }
  return cbp;
}

/**
 * chop the given free-block into a small free-blocks of the given size.
*/
static void chop_block(void* bp, size_t size){
  if ((bp == NULL) || (size < MIN_BLOCK_SIZE)) return;
  size_t bsize = BLOCK_SIZE(bp);
  if ((size + MIN_BLOCK_SIZE) > bsize) return;
  unlink_block(bp);

  while(bsize >= (size + MIN_BLOCK_SIZE)){
    SET_INFO(bp, size, 0);
    link_block(bp);
    bp = NEXT_BLOCK(bp);
    bsize -= size;
  }

  SET_INFO(bp, bsize, 0);
  link_block(bp);
}

/**
 * Add free block with aligned size to the end of the heap.
 * Return address of the added free block, NULL on error.
*/
void* extend_heap(size_t size) {
  WTYPE* bp;
  size = ALIGN(size);
  if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

  SET_INFO(bp, size, 0);                      /* Initialize a free block */
  link_block(bp);
  WRITE(HEADER(NEXT_BLOCK(bp)), 0, 1);        /* New Tail Word */

  return bp;
}

/* Find the first block greater than or equal to size
 * Return address of the first-fit, NULL if no-fit.
*/
static void* first_fit(void* free_list, size_t size) {
  for (void* bp = free_list; bp != NULL ; bp = GET_NEXT(bp)) {
    if (size <= BLOCK_SIZE(bp)) return bp;
  }
  return NULL;
}

/* Find the smallest block greater than or equal to size
 * Return address of the best-fit, NULL if no-fit.
*/
static void* best_fit(void* free_list, size_t size) {
  void* bp;
  void* best = NULL;
  size_t best_size = __SIZE_MAX__;

  for (bp = free_list; bp != NULL ; bp = GET_NEXT(bp)) {
    size_t curr_size = BLOCK_SIZE(bp);
    if ((size <= curr_size) && (curr_size < best_size)){
      best = bp;
    }
  }

  return best;
}

/**
 * Find a free block with size greater than or equal to size.
 * Return address of a fit-block, NULL if no fit.
*/
static void* find_fit(size_t size) {
  for(int i = seg_index(size); i < DSIZE; ++i){
    void* fit = best_fit(seglist[i], size);
    if (fit != NULL) return fit;
  }
  return NULL;
}

/**
 * Allocate the free block at bp.
 * Split the block if the remainder is greater than MIN_BLOCK_SIZE.
 * Returns the address of the allocated block payload
*/
static void* place(void *bp, size_t size) {
  size_t bsize = BLOCK_SIZE(bp);
  size_t csize = bsize - size;

  unlink_block(bp);
  if (csize < MIN_BLOCK_SIZE){
    SET_ALLOC(bp, 1);
  }else{
    SET_INFO(bp, csize, 0);
    link_block(bp);
    bp = NEXT_BLOCK(bp);
    SET_INFO(bp, size, 1);
  }

  return bp;
}

/**
 * Coalesce the current block with its free previous and/or next blocks.
 * Return the address of the coalesced block.
*/
static void* coalesce(void *bp) {
  void* cbp = bp;                            /* coalesced payload pointer */
  void* prev_footer = MOVE_WORD(bp, -2);
  void* next_header = HEADER(NEXT_BLOCK(bp));
  
  size_t prev_alloc = READ_ALLOC(prev_footer);
  size_t next_alloc = READ_ALLOC(next_header);
  size_t size = BLOCK_SIZE(bp);

  if (prev_alloc && next_alloc) {
    link_block(bp);
    return bp;
  }
  // if (!curr_alloc) unlink_block(bp);  //

  if (!next_alloc) {
    size += READ_SIZE(next_header);
    unlink_block(MOVE_WORD(next_header, 1));
  }

  if (!prev_alloc) {
    size += READ_SIZE(prev_footer);
    cbp = PREV_BLOCK(bp);
    unlink_block(cbp);
    // if (curr_alloc) memmove(cbp, bp, PAYLOAD_SIZE(bp));
  }

  SET_INFO(cbp, size, 0);
  link_block(cbp);

  return cbp;
}

/**
 * Add the block at bp to the free-list
*/
static void link_block(void* bp){
  int index = seg_index(BLOCK_SIZE(bp));
  WTYPE* list = seglist[index];
  if (list)
    PREV_FBLK(list, bp);
  NEXT_FBLK(bp, list);
  PREV_FBLK(bp, NULL);
  seglist[index] = bp;
}

/**
 * Remove the block at bp from the free-list 
*/
static void unlink_block(void* bp) {
  int index = seg_index(BLOCK_SIZE(bp));
  WTYPE* prev_bp = GET_PREV(bp);
  WTYPE* next_bp = GET_NEXT(bp);
  if (prev_bp) NEXT_FBLK(prev_bp, next_bp);
  if (next_bp) PREV_FBLK(next_bp, prev_bp);
  if (bp == seglist[index]) seglist[index] = next_bp;
}

/**
 * Returns the index of the seglist that should contain blocks of the given size 
*/
static int seg_index(size_t size){
  if (size <= MIN_BLOCK_SIZE) return 0;
  if (size <= (2 * MIN_BLOCK_SIZE)) return 1;
  if (size <= (4 * MIN_BLOCK_SIZE)) return 2;
  if (size <= (8 * MIN_BLOCK_SIZE)) return 3;
  if (size <= (16 * MIN_BLOCK_SIZE)) return 4;
  if (size <= (64 * MIN_BLOCK_SIZE)) return 5;
  if (size <= (256 * MIN_BLOCK_SIZE)) return 6;
  return 7;
}
