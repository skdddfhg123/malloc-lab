/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define MAX(x, y)           ((x) > (y)? (x) : (y))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT           8 // 할당하는 단위

/* Basic constants and macros */
#define WSIZE               4       /* Word and header.footer size (1bytes) */
#define DSIZE               8       /* Double word size (2bytes) */
#define CHUNKSIZE           (1<<12) /* 4Kb (데이터 섹터 크기) */

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size)         (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE         (ALIGN(sizeof(size_t)))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)   ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp;

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전블럭이 할당되어있는지 여부를 확인하는 변수
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음블럭  =
    size_t size = GET_SIZE(HDRP(bp)); 

    /* case 1: */
    if (prev_alloc && next_alloc)
    {
        return bp;
    }
    /* case 2: */
    else if (prev_alloc && !next_alloc) 
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }
    /* case 3: */
    else if (!prev_alloc && next_alloc) 
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    /* case 4: */
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment*/
    size = (words % 2) ? (words+1) * WSIZE : words *WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header*/
    PUT(HDRP(bp), PACK(size,0));    /* Free block header*/
    PUT(FTRP(bp), PACK(size,0));    /* Free block footer*/
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); /* New epilogue header*/

    return coalesce(bp);  //코올레스

}

static void *find_fit(size_t adjust_size)
{
    /* First-fit search*/
    void *bp;
    //printf("너니??");
    for (bp = heap_listp ; GET_SIZE(HDRP(bp)) > 0 ; bp = NEXT_BLKP(bp))
    {
        //printf("너니");
        if(!GET_ALLOC(HDRP(bp)) && (adjust_size <= GET_SIZE(HDRP(bp))))
        {
            
            return bp;
        }
    }
    return NULL; /* No fit */
}

static void place(void *bp, size_t adjust_size)
{
    size_t cur_size = GET_SIZE(HDRP(bp));

    if ((cur_size - adjust_size) >= (2*DSIZE))
    {
        PUT(HDRP(bp), PACK(adjust_size, 1));
        PUT(FTRP(bp), PACK(adjust_size, 1));
        bp=NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(cur_size - adjust_size, 0));
        PUT(FTRP(bp), PACK(cur_size - adjust_size, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(cur_size, 1));
        PUT(FTRP(bp), PACK(cur_size, 1));
    }
}



/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap*/
    
    if ((heap_listp = mem_sbrk(4*WSIZE))== (void *)-1)
        return -1;

    PUT(heap_listp,0);  /*Alignment padding*/
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); /* Prologue header*/
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); /* Prologue footer*/
    PUT(heap_listp + (3*WSIZE), PACK(0,1));  /* Epilogue header*/
    heap_listp += (2*WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    //printf("afafafdf");
  size_t adjust_size; /* Adjusted(조정가능한) block size*/
  size_t extend_size; /* Amount to extend heap if no fit */
  char *bp;

  /* Ignore spurious requests*/
  // 미친 테케용
  if (size == 0)
    return NULL;

  /* Adjust block size to include overhead(h&f) and alignment reqs. */
  if (size <=DSIZE)
    adjust_size = 2*DSIZE;
  else{
    adjust_size = ALIGN(size) + DSIZE;
  }
    
  
  /* Search the free list for a fit  중요한 부분 */
  if ((bp = find_fit(adjust_size)) != NULL)
  {
    place(bp, adjust_size);
    return bp;
  }

  /* No fit found. Get more memory and place the block*/
  extend_size = MAX(adjust_size, CHUNKSIZE);
  if ((bp = extend_heap(extend_size/WSIZE)) == NULL){
    return NULL;
  }
  place(bp, adjust_size);
  return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp),PACK(size, 0));
    PUT(FTRP(bp),PACK(size, 0));
    coalesce(bp);

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldptr = bp;
    void *newptr;
    size_t copy_size;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copy_size = (size_t)GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copy_size)
      copy_size = size;
    memcpy(newptr, oldptr, copy_size);
    mm_free(oldptr);
    return newptr;
}

///////////////////////////////////////////// explict list //////////////////////////////////////////////////////////
// static char *heap_listp;
// static list_t free_list;

// static void *coalesce(void *bp)
// {
//     // printf("@@@ %p\n", free_list.end);
//     size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전블럭이 할당되어있는지 여부를 확인하는 변수
//     size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음블럭
//     size_t size = GET_SIZE(HDRP(bp));
//     printf("coalesce, %p \n", bp);
//     /* case 1: */
//     if (prev_alloc && next_alloc)
//     {
//         // printf("!!\n");
//         if (free_list.end != free_list.start) {
//             if (bp < free_list.start) {
//                 // 다음 노드의 prev를 나로 변경
//                 PUT(PREV_FBLKP(free_list.start), bp);
//                 // 지금 노드의 next에 다음노드 주소 저장
//                 PUT(NEXT_FBLKP(bp),free_list.start);
//                 //start를 나로
//                 free_list.start=bp;
//                 // 시작 노드의 prev는  end로 써클연결 monster
//                 PUT(PREV_FBLKP(bp),free_list.end);
//             }
//             else if (bp > free_list.end) {
//                 // printf("!!!!!!!!!\n");
//                 // 이전 노드의 next를 나로 변경
//                 PUT(NEXT_FBLKP(free_list.end), bp);
//                 // 지금 노드의 prev에 이전노드 주소 저장
//                 PUT(PREV_FBLKP(bp),free_list.end);
//                 //end를 나로
//                 free_list.end=bp;
//                 // 마지막 노드의 next는 시작점으로 써클연결 monster
//                 PUT(NEXT_FBLKP(bp),free_list.start);
//             }
//             else  {
//                 // printf("!!!\n");
//                 PUT(NEXT_FBLKP(PREV_FBLKP(bp)) , bp);
//                 PUT(PREV_FBLKP(NEXT_FBLKP(bp)) , bp);
//                 // 여기 
//                 PUT(NEXT_FBLKP(bp), NEXT_BLKP(bp));
//                 PUT(PREV_FBLKP(bp), PREV_BLKP(bp)); 
//             }
//         }
//         return bp;
//     }
//     /* case 2: */
//     else if (prev_alloc && !next_alloc) 
//     {
//         // printf("!!\n");
//         char *next = NEXT_BLKP(bp);

//         if (bp < free_list.start) {
//             // 여기
//             PUT(NEXT_FBLKP(bp), NEXT_FBLKP(next));
//             PUT(PREV_FBLKP(bp), PREV_FBLKP(next));
//             free_list.start = bp;
//             PUT(NEXT_FBLKP(free_list.end), bp);
//         }
//         else {
//             //여기
//             PUT(NEXT_FBLKP(bp), NEXT_FBLKP(next));
//             PUT(PREV_FBLKP(bp), PREV_FBLKP(next));
//         }
//         size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
//         PUT(HDRP(bp), PACK(size,0));
//         PUT(FTRP(bp), PACK(size,0));
//     }
//     /* case 3: */
//     else if (!prev_alloc && next_alloc) 
//     {
//         // printf("!!\n");
//         size += GET_SIZE(HDRP(PREV_BLKP(bp)));
//         PUT(FTRP(bp), PACK(size,0));
//         PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
//         bp = PREV_BLKP(bp);
//     }
//     /* case 4: */
//     else
//     {
//         if (NEXT_BLKP(bp) == free_list.end)
//             free_list.end = PREV_BLKP(bp);
//         PUT(NEXT_FBLKP(PREV_BLKP(bp)), NEXT_FBLKP(NEXT_BLKP(bp)));
//         size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
//             GET_SIZE(FTRP(NEXT_BLKP(bp)));
//         PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
//         PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
//         bp = PREV_BLKP(bp);
//     }

//     return bp;
// }

// static void *extend_heap(size_t words)
// {
//     char *bp;
//     size_t size;
    
//     /* Allocate an even number of words to maintain alignment*/
//     size = (words % 2) ? (words+1) * WSIZE : words *WSIZE;
//     if ((bp = mem_sbrk(size)) == (void *)-1)
//         return NULL;


//     /* Initialize free block header/footer and the epilogue header*/
//     PUT(HDRP(bp), PACK(size,0));    /* Free block header*/
//     // 
//     PUT(FTRP(bp), PACK(size,0));    /* Free block footer*/
//     // printf("%p %p \n", bp, PREV_FBLKP(bp));
//     PUT(NEXT_FBLKP(bp), 1);     /*다음 프리블럭 포인터*/
//     PUT(PREV_FBLKP(bp), 1);     /* 이전 프리블럭 포인터*/
//     PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); /* New epilogue header*/

//     /* case 1 : 처음이면*/
//     if (free_list.start ==NULL && free_list.end == NULL) {
//         free_list.start=free_list.end=bp;
//         PUT(NEXT_FBLKP(bp), bp);
//         PUT(PREV_FBLKP(bp), bp);
//     }
//     /* case 2 : 다음에 가용할 리스트가 있다면?*/

//     return coalesce(bp);  //코올레스

// }

// static void *find_fit(size_t adjust_size)
// {
//     // /* First-fit search*/
//     // void *bp;
//     // //printf("너니??");
//     // for (bp = heap_listp ; GET_SIZE(HDRP(bp)) > 0 ; bp = NEXT_BLKP(bp))
//     // {
//     //     //printf("너니");
//     //     if(!GET_ALLOC(HDRP(bp)) && (adjust_size <= GET_SIZE(HDRP(bp))))
//     //     {
            
//     //         return bp;
//     //     }
//     // }
//     // return NULL; /* No fit */

//     /* New search*/
//     char *next=free_list.start;


//     do {
//         if(adjust_size <= GET_SIZE(HDRP(next))) {
//             return next;
//         }
//         next = NEXT_FBLKP(next);
//     } while (next != free_list.end);
    
//     return NULL;
// }

// static void place(void *bp, size_t adjust_size)
// {
//     size_t cur_size = GET_SIZE(HDRP(bp));

//     if ((cur_size - adjust_size) >= (2*DSIZE))
//     {   
//         printf("남는 공간 충분 place, %p \n", bp);
//         PUT(HDRP(bp), PACK(adjust_size, 1));
//         PUT(FTRP(bp), PACK(adjust_size, 1));
//         bp=NEXT_BLKP(bp);
//         PUT(HDRP(bp), PACK(cur_size - adjust_size, 0));
//         PUT(FTRP(bp), PACK(cur_size - adjust_size, 0));
        
//         // 프리 블록 재생성 -> 프리 블록에게 앞뒤 블록 연결
//         // 빈 블록이 하나일 때 
//         if (free_list.start == PREV_BLKP(bp) && free_list.end == PREV_BLKP(bp)) {
//             printf("1!!!!!\n");
//             free_list.start = bp;
//             free_list.end = bp;
//             printf("place%p\n" ,bp);

//         }
//         // if 스타트 지점을 옮겨야 할 때
//         else if (free_list.start == PREV_BLKP(bp)) {
//             printf("2!!!!!\n");
//             free_list.start = bp;
//         }
//         // if 엔드 지점을 옮겨야 할 때
//         else if (free_list.end == PREV_BLKP(bp)) {
//             printf("3!!!!!\n");
//             free_list.end = bp;
//         }

//         PUT(PREV_FBLKP(bp), NEXT_FBLKP(PREV_BLKP(bp)));
//         PUT(NEXT_FBLKP(bp), PREV_FBLKP(NEXT_BLKP(bp)));

//         PUT(PREV_FBLKP(NEXT_FBLKP(bp)), bp);
//         PUT(NEXT_FBLKP(PREV_FBLKP(bp)), bp);
//     }
//     else
//     {
//         // 프리 블록 삭제됨 -> 앞뒤 프리 블록 서로 연결
//         printf("남는 공간 부족 place, %p \n", bp);
//         PUT(HDRP(bp), PACK(cur_size, 1));
//         PUT(FTRP(bp), PACK(cur_size, 1));
//         if (free_list.start == bp && free_list.end == bp) {
//             free_list.end = NULL;
//             free_list.start = NULL;
//         } else {
//             PUT(PREV_FBLKP(bp), NEXT_FBLKP(bp));
//             PUT(NEXT_FBLKP(bp), PREV_FBLKP(bp));
//         }
//     }

// }



// /* 
//  * mm_init - initialize the malloc package.
//  */
// int mm_init(void)
// {
//     /* Create the initial empty heap*/
//     free_list.start = NULL;
//     free_list.end = NULL;
    
//     if ((heap_listp = mem_sbrk(4*WSIZE))== (void *)-1)
//         return -1;
//     PUT(heap_listp,0);  /*Alignment padding*/
//     PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); /* Prologue header*/
//     PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); /* Prologue footer*/
//     PUT(heap_listp + (3*WSIZE), PACK(0,1));  /* Epilogue header*/
//     heap_listp += (2*WSIZE);

//     if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
//         return -1;
//     return 0;
// }

// /* 
//  * mm_malloc - Allocate a block by incrementing the brk pointer.
//  *     Always allocate a block whose size is a multiple of the alignment.
//  */
// void *mm_malloc(size_t size)
// {
//     //printf("afafafdf");
//   size_t adjust_size; /* Adjusted(조정가능한) block size*/
//   size_t extend_size; /* Amount to extend heap if no fit */
//   char *bp;

//     printf("size = %d\n", size);
//   /* Ignore spurious requests*/
//   // 미친 테케용
//   if (size == 0)
//     return NULL;

//   /* Adjust block size to include overhead(h&f) and alignment reqs. */
//   if (size <=DSIZE)
//     adjust_size = 2*DSIZE;
//   else{
//     //  adjust_size = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
//     //  printf("%d %d\n",adjust_size, size);
//     adjust_size = ALIGN(size)+8;  //헤더푸터 추가해줘야되니까 8byte 추가
//   }

//   /* Search the free list for a fit  중요한 부분 */
//   if ((bp = find_fit(adjust_size)) != NULL)
//   {
//     printf("find fit, %p %p\n", free_list.start, bp);
//     //printf("!!!");
//     place(bp, adjust_size);
//     return bp;
//   }
//   /* No fit found. Get more memory and place the block*/
//   printf("Extend heap \n");
//   extend_size = MAX(adjust_size, CHUNKSIZE);
//   if ((bp = extend_heap(extend_size/WSIZE)) == NULL){
//     return NULL;
//   }
//   //printf("!!!!!");
//   place(bp, adjust_size);
//   return bp;
// }

// /*
//  * mm_free - Freeing a block does nothing.
//  */
// void mm_free(void *bp)
// {
//     size_t size = GET_SIZE(HDRP(bp));
//     PUT(HDRP(bp),PACK(size, 0));
//     PUT(FTRP(bp),PACK(size, 0));
//     if (free_list.end == NULL && free_list.start == NULL) {
//         free_list.start = bp;
//         free_list.end = bp;
//     }
//     else {
        
//     }
//     coalesce(bp);
// }

// /*
//  * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
//  */
// void *mm_realloc(void *bp, size_t size)
// {
//     void *oldptr = bp;
//     void *newptr;
//     size_t copy_size;
    
//     newptr = mm_malloc(size);
//     if (newptr == NULL)
//       return NULL;
//     // copy_size = *(size_t *)((char *)oldptr - WSIZE) - 9;
//     copy_size = (size_t)(GET_SIZE(HDRP(oldptr))) - DSIZE;
//      //copy_size = *(size_t *)((char *)oldptr - SIZE_T_SIZE); //
//     if (size < copy_size)
//       copy_size = size;
//     memcpy(newptr, oldptr, copy_size);
//     mm_free(oldptr);
//     return newptr;
// }

///////////////////////////////////seg_list/////////////////////////////////
// #include <stdio.h>
// #include <stdlib.h>
// #include <assert.h>
// #include <unistd.h>
// #include <string.h>

// #include "mm.h"
// #include "memlib.h"

// /* =============================================================================== */

// team_t team = {
//   /* Team name */
//   "",
//   /* First member's full name */
//   "",
//   /* First member's email address */
//   "",
//   /* Second member's full name (leave blank if none) */
//   "",
//   /* Second member's email address (leave blank if none) */
//   ""
// };

// /* ========================== Function Prototype =============================== */

// inline static void* resize_block(void*, size_t);
// inline static void* reallocate_block(void*, size_t);
// inline static int can_expand(void*, size_t);
// inline static void* expand_block(void*, size_t);
// inline static void chop_block(void*, size_t);
// inline static void* extend_heap(size_t);
// inline static void* first_fit(void*, size_t);
// inline static void* best_fit(void*, size_t);
// inline static void* find_fit(size_t);
// inline static void* place(void*, size_t);
// inline static void* coalesce(void*);
// inline static void link_block(void*);
// inline static void unlink_block(void*);
// inline static int seg_index(size_t);

// /* ========================== Compilation Flags =============================== */

// // #define DEBUG                 /* uncomment to turn-on heap checker */

// #ifdef DEBUG
//   static void mm_check(int);
//   static void check_seglist(int, int);
//   static int check_free_list(int, int);
//   #define heap_check(line) (mm_check(line))
// #else
//   #define heap_check(line)
// #endif
// //NOTE at 236: two contiguous free blocks not coalesced 식으로 heap 체크 가능
// /* ================================ Macros ===================================== */

// #define WSIZE 4                           /* Word size in bytes */
// #define DSIZE 8                           /* Double word size in bytes */
// #define CHUNKSIZE (1<<8)                  /* Minimum heap allocation size */
// #define MIN_BLOCK_SIZE 16                 /* Minimum block size */
// #define ALIGNMENT 8                       /* Payload Alignment */
// #define DSIZE 8                     /* The Number of lists in the seglist */
// #define WTYPE u_int32_t                   /* Word type */
// #define BYTE char                         /* Byte type */

// /* ------------------------------ Basic Utility ------------------------------- */

// /* Move the address ptr by offset bytes */
// #define MOVE_BYTE(ptr, offset) ((WTYPE *)((BYTE *)(ptr) + (offset)))
// /* Move the address ptr by offset words */
// #define MOVE_WORD(ptr, offset) ((WTYPE *)(ptr) + (offset))
// /* Read a word from address ptr */
// #define READ_WORD(ptr) (*(WTYPE *)(ptr))
// /* Write a word value to address ptr */
// #define WRITE_WORD(ptr, value) (*(WTYPE *)(ptr) = (value))
// /* rounds up size (in bytes) to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
// /* Get the maximum of x and y */
// #define MAX(x, y) (((x) > (y))? (x) : (y))
// /* Get the minimum of x and y */
// #define MIN(x, y) (((x) < (y))? (x) : (y))

// /* ----------------------- Header/Footer Macros ---------------------------- */

// /* Pack the size and allocated-bit into a word */
// #define PACK(size, alloc) ((size) | (alloc))
// /* Read the size from header/footer word at address Hptr */
// #define READ_SIZE(Hptr) (READ_WORD(Hptr) & ~0x7)
// /* Read the allocated-bit from header/footer word at address Hptr */
// #define READ_ALLOC(Hptr) (READ_WORD(Hptr) & 0x1)
// /* Write the size and allocation-bit to the word at address Hptr */
// #define WRITE(Hptr, size, alloc) (WRITE_WORD((Hptr), PACK((size), (alloc))))
// /* Write the size to the word at address Hptr */
// #define WRITE_SIZE(Hptr, size) (WRITE((Hptr), (size), READ_ALLOC(Hptr)))
// /* Write allocation-bit to the word at address Hptr */
// #define WRITE_ALLOC(Hptr, alloc) (WRITE((Hptr), READ_SIZE(Hptr), (alloc)))

// /* ---------------------------- Payload Macros ------------------------------ */

// /* Get the header-word pointer from the payload pointer bp */
// #define HEADER(bp) (MOVE_WORD(bp, -1))
// /* Get the footer-word pointer from the payload pointer bp */
// #define FOOTER(bp) (MOVE_BYTE(bp, PAYLOAD_SIZE(bp)))
// /* Get next block payload pointer from bp (current payload pointer) */
// #define NEXT_BLOCK(bp) (MOVE_BYTE(bp, BLOCK_SIZE(bp)))
// /* Get previous block payload pointer from bp (current payload pointer) */
// #define PREV_BLOCK(bp) (MOVE_BYTE(bp, - READ_SIZE(MOVE_WORD(bp, -2))))
// /* Read the block size at the payload bp */
// #define BLOCK_SIZE(bp) (READ_SIZE(HEADER(bp)))
// /* Read the payload size at bp */
// #define PAYLOAD_SIZE(bp) (BLOCK_SIZE(bp) - DSIZE)
// /* Check if the block at the payload bp is free */
// #define IS_FREE(bp) (!(READ_ALLOC(HEADER(bp))))

// /* Sets the size and allocation-bit to header/footer of block at bp */
// #define SET_INFO(bp, size, alloc)\
//   ((WRITE(HEADER(bp),(size),(alloc))), \
//    (WRITE(FOOTER(bp),(size),(alloc))))

// /* Sets the size to header/footer of block at bp */
// #define SET_SIZE(bp, size)\
//   ((WRITE_SIZE(HEADER(bp),(size))), \
//    (WRITE_SIZE(FOOTER(bp),(size))))

// /* Sets the allocation-bit to header/footer of block at bp */
// #define SET_ALLOC(bp, alloc)\
//   ((WRITE_ALLOC(HEADER(bp),(alloc))), \
//    (WRITE_ALLOC(FOOTER(bp),(alloc))))

// /* Get the predecessor payload address */
// #define GET_PREV(bp) ((WTYPE *)(READ_WORD(bp)))
// /* Get the successor payload address */
// #define GET_NEXT(bp) ((WTYPE *)(READ_WORD(MOVE_WORD(bp, 1))))
// /* Set the predecessor payload address to pred_bp */
// #define PREV_FBLK(bp, pred_bp) (WRITE_WORD(bp, ((WTYPE) pred_bp)))
// /* Set the successor payload address to succ_bp */
// #define NEXT_FBLK(bp, succ_bp) (WRITE_WORD(MOVE_WORD(bp, 1), ((WTYPE) succ_bp)))

// /* ======================= Private Global Variables ============================== */
// // private global variable
// static WTYPE** seglist;       /* array of free-list pointers */
// /* =========================== Public Functions ================================== */

// /* 
//  * Initialize the malloc package.
//  * return 0 on success, -1 on error.
//  */
// int mm_init(void) {
//   /* Create the initial empty heap */
//   void* heap = mem_sbrk((DSIZE + 2) * WSIZE); /* seglist + head + tail */
//   if (heap == (void*)-1) return -1;

//   seglist = heap;
//   heap = MOVE_WORD(heap, DSIZE);
//   // initialize the seglist
//   for(int i = 0; i < DSIZE; ++i){
//     seglist[i] = NULL;
//   }

//   WRITE(heap, 0, 1);                          /* Head Word */
//   WRITE(MOVE_WORD(heap, 1), 0, 1);            /* Tail Word */

//   /* Extend the empty heap with a small free block */
//   if (extend_heap(4 * MIN_BLOCK_SIZE) == NULL) return -1;
//   heap_check(__LINE__);
//   return 0;
// }

// /* 
//  *  Allocate an aligned block of memory of at least size bytes
//  *  Return address of allocated block on success, NULL on error.
//  */
// void* mm_malloc(size_t size) {
//   if (size == 0) return NULL;
//   void* bp;                             /* Payload Pointer */
//   size = ALIGN(size + DSIZE);           /* Add header and footer words */
//   size = MAX(size, MIN_BLOCK_SIZE);

//   /* Search the free list for a fit */
//   if ((bp = find_fit(size)) == NULL) {
//     /* No fit found, request a block from the memory */
//     if (size > CHUNKSIZE){
//       bp = extend_heap(size);
//     }else{
//       bp = extend_heap(4 * CHUNKSIZE);
//       chop_block(bp, size);
//     }
//     if (bp == NULL) return NULL;
//   }

//   bp = place(bp, size);
//   heap_check(__LINE__);
//   return bp;
// }

// /*
//  * Free the allocated block at ptr, and coalesce it.
//  */
// void mm_free(void* ptr) {
//   SET_ALLOC(ptr, 0);
//   // link_block(ptr);
//   coalesce(ptr);
//   heap_check(__LINE__);
// }

// /*
//  * # ptr = NULL : allocate block of the given size.
//  * # size = 0 : free the given block, return NULL.
//  * # else: resize the allocated block at ptr.
//  * 
//  * Return address of the reallocated block, NULL on error.
//  */
// void* mm_realloc(void* ptr, size_t size) {
//   if (size == 0 || ptr == NULL){
//     mm_free(ptr);
//     return NULL;
//   }else{
//     ptr = resize_block(ptr, size);
//     heap_check(__LINE__);
//     return ptr;
//   }
// }

// /* =========================== Private Functions ================================== */

// /*
//  * Resize the allocated block at bp to have size bytes
//  * Return address of the resized block, NULL on error.
//  */
// static void* resize_block(void* bp, size_t size) {
//   size_t asize = MAX(MIN_BLOCK_SIZE, ALIGN(size + DSIZE));
//   size_t bsize = BLOCK_SIZE(bp);
//   size_t csize = bsize - asize;

//   if (asize > bsize) {
//     if (can_expand(bp, asize))
//       return expand_block(bp, asize);
//     return reallocate_block(bp, size);
//   }

//   // Split only if the fragment is large enough.
//   if (csize >= (MIN_BLOCK_SIZE)){
//     SET_INFO(bp, asize, 1);
//     void* fp = NEXT_BLOCK(bp);
//     SET_INFO(fp, csize, 0);
//     link_block(fp);
//   }

//   return bp;
// }

// /*
//  * Allocate block of the given size, copy content, free old block
//  * Return address of the new block, NULL on error.
//  */
// static void* reallocate_block(void* ptr, size_t size) {
//   void *newptr = mm_malloc(size);
//   if (newptr == NULL) return NULL;
//   // size_t copy_size = MIN(PAYLOAD_SIZE(ptr), size);
//   memcpy(newptr, ptr, PAYLOAD_SIZE(ptr));
//   mm_free(ptr);
//   return newptr;
// }

// /**
//  * checks if the allocated-block at bp can expand to have the given size
//  */
// static int can_expand(void* bp, size_t size){
//   size_t bsize = BLOCK_SIZE(bp);

//   for(void* ptr = NEXT_BLOCK(bp); IS_FREE(ptr) ; ptr = NEXT_BLOCK(ptr)){
//     bsize += BLOCK_SIZE(ptr);
//     if (bsize >= size) return 1;
//   }

//   for(void* ptr = bp; !READ_ALLOC(MOVE_WORD(ptr, -2)) ; ){
//     ptr = PREV_BLOCK(ptr);
//     bsize += BLOCK_SIZE(ptr);
//     if (bsize >= size) return 1;
//   }

//   return 0;
// }

// /**
//  * expands the allocated-block at bp until it has the given size
//  * return address to the new expanded block
// */
// static void* expand_block(void *bp, size_t size) {
//   void* cbp = bp;
//   size_t bsize = BLOCK_SIZE(bp);

//   for(void* ptr = NEXT_BLOCK(bp); IS_FREE(ptr) ; ptr = NEXT_BLOCK(ptr)){
//     bsize += BLOCK_SIZE(ptr);
//     unlink_block(ptr);
//     if (bsize >= size) {
//       SET_INFO(cbp, bsize, 1);
//       return cbp;
//     }
//   }

//   for(void* ptr = bp; !READ_ALLOC(MOVE_WORD(ptr, -2)) ; ){
//     cbp = ptr = PREV_BLOCK(ptr);
//     bsize += BLOCK_SIZE(ptr);
//     unlink_block(ptr);
//     if (bsize >= size) {
//       memmove(cbp, bp, PAYLOAD_SIZE(bp));
//       SET_INFO(cbp, bsize, 1);
//       return cbp;
//     }
//   }
//   return cbp;
// }

// /**
//  * chop the given free-block into a small free-blocks of the given size.
// */
// static void chop_block(void* bp, size_t size){
//   if ((bp == NULL) || (size < MIN_BLOCK_SIZE)) return;
//   size_t bsize = BLOCK_SIZE(bp);
//   if ((size + MIN_BLOCK_SIZE) > bsize) return;
//   unlink_block(bp);

//   while(bsize >= (size + MIN_BLOCK_SIZE)){
//     SET_INFO(bp, size, 0);
//     link_block(bp);
//     bp = NEXT_BLOCK(bp);
//     bsize -= size;
//   }

//   SET_INFO(bp, bsize, 0);
//   link_block(bp);
// }

// /**
//  * Add free block with aligned size to the end of the heap.
//  * Return address of the added free block, NULL on error.
// */
// void* extend_heap(size_t size) {
//   WTYPE* bp;
//   size = ALIGN(size);
//   if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

//   SET_INFO(bp, size, 0);                      /* Initialize a free block */
//   link_block(bp);
//   WRITE(HEADER(NEXT_BLOCK(bp)), 0, 1);        /* New Tail Word */

//   return bp;
// }

// /* Find the first block greater than or equal to size
//  * Return address of the first-fit, NULL if no-fit.
// */
// static void* first_fit(void* free_list, size_t size) {
//   for (void* bp = free_list; bp != NULL ; bp = GET_NEXT(bp)) {
//     if (size <= BLOCK_SIZE(bp)) return bp;
//   }
//   return NULL;
// }

// /* Find the smallest block greater than or equal to size
//  * Return address of the best-fit, NULL if no-fit.
// */
// static void* best_fit(void* free_list, size_t size) {
//   void* bp;
//   void* best = NULL;
//   size_t best_size = __SIZE_MAX__;

//   for (bp = free_list; bp != NULL ; bp = GET_NEXT(bp)) {
//     size_t curr_size = BLOCK_SIZE(bp);
//     if ((size <= curr_size) && (curr_size < best_size)){
//       best = bp;
//     }
//   }

//   return best;
// }

// /**
//  * Find a free block with size greater than or equal to size.
//  * Return address of a fit-block, NULL if no fit.
// */
// static void* find_fit(size_t size) {
//   for(int i = seg_index(size); i < DSIZE; ++i){
//     void* fit = best_fit(seglist[i], size);
//     if (fit != NULL) return fit;
//   }
//   return NULL;
// }

// /**
//  * Allocate the free block at bp.
//  * Split the block if the remainder is greater than MIN_BLOCK_SIZE.
//  * Returns the address of the allocated block payload
// */
// static void* place(void *bp, size_t size) {
//   size_t bsize = BLOCK_SIZE(bp);
//   size_t csize = bsize - size;

//   unlink_block(bp);
//   if (csize < MIN_BLOCK_SIZE){
//     SET_ALLOC(bp, 1);
//   }else{
//     SET_INFO(bp, csize, 0);
//     link_block(bp);
//     bp = NEXT_BLOCK(bp);
//     SET_INFO(bp, size, 1);
//   }

//   return bp;
// }

// /**
//  * Coalesce the current block with its free previous and/or next blocks.
//  * Return the address of the coalesced block.
// */
// static void* coalesce(void *bp) {
//   void* cbp = bp;                            /* coalesced payload pointer */
//   void* prev_footer = MOVE_WORD(bp, -2);
//   void* next_header = HEADER(NEXT_BLOCK(bp));
  
//   size_t prev_alloc = READ_ALLOC(prev_footer);
//   size_t next_alloc = READ_ALLOC(next_header);
//   size_t size = BLOCK_SIZE(bp);

//   if (prev_alloc && next_alloc) {
//     link_block(bp);
//     return bp;
//   }
//   // if (!curr_alloc) unlink_block(bp);  //

//   if (!next_alloc) {
//     size += READ_SIZE(next_header);
//     unlink_block(MOVE_WORD(next_header, 1));
//   }

//   if (!prev_alloc) {
//     size += READ_SIZE(prev_footer);
//     cbp = PREV_BLOCK(bp);
//     unlink_block(cbp);
//     // if (curr_alloc) memmove(cbp, bp, PAYLOAD_SIZE(bp));
//   }

//   SET_INFO(cbp, size, 0);
//   link_block(cbp);

//   return cbp;
// }

// /**
//  * Add the block at bp to the free-list
// */
// static void link_block(void* bp){
//   int index = seg_index(BLOCK_SIZE(bp));
//   WTYPE* list = seglist[index];
//   if (list)
//     PREV_FBLK(list, bp);
//   NEXT_FBLK(bp, list);
//   PREV_FBLK(bp, NULL);
//   seglist[index] = bp;
// }

// /**
//  * Remove the block at bp from the free-list 
// */
// static void unlink_block(void* bp) {
//   int index = seg_index(BLOCK_SIZE(bp));
//   WTYPE* prev_bp = GET_PREV(bp);
//   WTYPE* next_bp = GET_NEXT(bp);
//   if (prev_bp) NEXT_FBLK(prev_bp, next_bp);
//   if (next_bp) PREV_FBLK(next_bp, prev_bp);
//   if (bp == seglist[index]) seglist[index] = next_bp;
// }

// /**
//  * Returns the index of the seglist that should contain blocks of the given size 
// */
// static int seg_index(size_t size){
//   if (size <= MIN_BLOCK_SIZE) return 0;
//   if (size <= (2 * MIN_BLOCK_SIZE)) return 1;
//   if (size <= (4 * MIN_BLOCK_SIZE)) return 2;
//   if (size <= (8 * MIN_BLOCK_SIZE)) return 3;
//   if (size <= (16 * MIN_BLOCK_SIZE)) return 4;
//   if (size <= (64 * MIN_BLOCK_SIZE)) return 5;
//   if (size <= (256 * MIN_BLOCK_SIZE)) return 6;
//   return 7;
// }
