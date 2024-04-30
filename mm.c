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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE   4                               // word, header, footer size (bytes)
#define DSIZE   8                               // double word size (bytes)
#define CHUNKSIZE   (1<<12)                     // heap extension size (bytes)

#define MAX(x, y)   (x > y ? x : y)

#define PACK(size, alloc)   ((size) | (alloc))  // 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴   CS:app 9.9.6에 나온 | 연산이 이거임

#define GET(p)  (*(unsigned int *)p)            // p에 담긴 값을 참조
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // p에 담긴 값을 val로 바꿈

#define GET_SIZE(p) (GET(p) & ~0x7)             // p의 size를 반환
#define GET_ALLOC(p) (GET(p) & 0x1)             // p 중에 할당된 곳을 반환

#define HDRP(bp)    ((char *)(bp) - WSIZE)      // block pointer를 주면 header의 주소를 반환
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // block pointer를 주면 footer의 주소를 반환

#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))       // 현재 block의 pointer를 넣으면 다음 block의 pointer를 반환
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))       // 현재 block의 pointer를 넣으면 이전 block의 pointer를 반환


char * heap_listp;
void *startP = NULL;                            // next fit에서 사용될 bp
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)  return -1;          // 메모리 시스템에서 4워드를 가져오는 데 실패하면 return -1

    PUT(heap_listp, 0);                                                         // 더블 워드 경계로 정렬시키기 위한 미사용 패딩 워드
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));                              // Prologue의 헤더
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));                              // Prologue의 풋터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));                                  // Epilogue의 헤더
    heap_listp += (2 * WSIZE);

    if(extend_heap(CHUNKSIZE / WSIZE) == NULL)  return -1;                      // extend_heap 함수를 통해 힙을 CHUNKSIZE 바이트로 확장하여 초기 가용 블록을 생성

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)                                                     // size : 할당 요청한 크기
{
    size_t asize;                                                                // 실제 할당받을 block size
    size_t extendsize;                                                           // 할당받을 만한 곳이 없을 때 추가할 heap의 크기
    char *bp;

    if(size == 0)   return NULL;                                                 // 할당받을 size가 0이면 그대로 return

    if(size <= DSIZE) asize = 2 * DSIZE;                                         // 할당 요청한 크기가 8바이트보다 작으면 16바이트(더블워드) 정렬 조건을 만족시키기 위해
                                                                                 // 8바이트는 정렬 요건을 위해, 8바이트는 헤더와 풋터를 위해 총 16바이트를 할당해줌
    else asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);               // 8바이트가 넘는 요청에 대해서는 오버헤드 바이트를 추가하고, 가장 가까운 8의 배수로 반올림해줌

    if((bp = find_fit(asize)) != NULL) {                                         // asize 만큼을 할당할 수 있는 곳을 찾으면
        place(bp, asize);                                                        // 해당 pointer가 가리키는 위치에 asize만큼 할당하고 데이터를 위치시킴
        return bp;
    }

    /* 맞는 size의 가용 블록이 없는 경우 */
    extendsize = MAX(asize, CHUNKSIZE);                                          // asize가 CHUNKSIZE보다 크면 asize만큼 추가로 heap 메모리를 받아야함(작으면 고정된 CHUNKSIZE 만큼)
    if((bp = extend_heap(extendsize / WSIZE)) == NULL)  return NULL;             // heap을 추가로 더 받음
    place(bp, asize);                                                            // bp에 asize만큼 위치시킴
    return bp;


    // // 원래 거
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));                                           // free하려는 block의 header에 접근해 size를 알아냄

    PUT(HDRP(ptr), PACK(size, 0));                                               // 헤더에 이 블록이 가용 블록임을 저장함
    PUT(FTRP(ptr), PACK(size, 0));                                               // 풋터에 이 블록이 가용 블록임을 저장함
    coalesce(ptr);                                                               // 이전 블록이 가용 블록이라면 연결함
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/*   coalesce 함수의 내부   */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));                      // 이전 블록이 할당 상태인지 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));                      // 다음 블록이 할당 상태인지 확인
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) { /* Case 1 */                             // 이전 블록, 다음 블록이 모두 할당되어있는 경우
        return bp;
    }

    else if (prev_alloc && !next_alloc) { /* Case 2 */                       // 이전 블록은 할당, 다음 블록이 가용인 경우
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));                               // size를 다음 블록 크기만큼 더함
        PUT(HDRP(bp), PACK(size, 0));                                        // 헤더와 풋터에 해당 정보 저장
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) { /* Case 3 */                       // 이전 블록 가용, 다음 블록이 할당된 경우
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));                               // size를 이전 블록 크기만큼 더함
        PUT(FTRP(bp), PACK(size, 0));                                        // 헤더와 풋터에 해당 정보 저장
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);                                                  // 이전 블록과도 합쳤으므로 block pointer를 이전 블록의 bp로 옮겨줌
    }

    else { /* Case 4 */                                                      // 이전 블록, 다음 블럭 모두 가용 블록인 경우
        size += GET_SIZE(FTRP(PREV_BLKP(bp))) +                              // size를 이전 블록, 다음 블록 크기만큼 더함
        GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                             // 헤더와 풋터에 해당 정보 저장
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);                                                  // 이전 블록과도 합쳤으므로 block pointer를 이전 블록의 bp로 옮겨줌
    }
    startP = bp;
    return bp;
}

/*   extend_heap 함수의 내부   */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;                // 입력받은 word 개수가 짝수면 그대로 WSIZE 곱하고, 홀수면 padding을 위해 1을 더하고 WSIZE 곱함
    if ((long)(bp = mem_sbrk(size)) == -1)                                   // 해당 블록 사이즈만큼 mem_sbrk를 통해 힙 영역을 할당받음
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */                    // 가용 블록의 헤더
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */                    // 가용 블록의 풋터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */          // 새로운 에필로그 헤더

    /* Coalesce if the previous block was free */
    return coalesce(bp);                                                     // 이전 블록이 free라면 연결해주면서 return
}

static void *find_fit(size_t asize) {
    /* First-fit version*/
    // void *bp;

    // for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    //     if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
    //         return bp;
    // }
    // return NULL;

    /* Best-fit version*/
    // void *bp = NULL;
    // void *best;
    // int best_sz = CHUNKSIZE;
    // for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    //     if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
    //         if(best_sz > GET_SIZE(HDRP(bp))) {
    //             best = bp;
    //             best_sz = GET_SIZE(HDRP(bp));
    //         }
    //     }
    // }
    // return bp;

    /* Next-fit version*/
    void *bp;

    if(startP == NULL || startP == heap_listp) {
        startP = heap_listp;
    }
    
    for(bp = startP; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if(!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))) {
            startP = bp;
            return bp;
        }
    }

    for(bp = heap_listp; bp < startP; bp = NEXT_BLKP(bp)) {
        if(!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))) {
            startP = bp;
            return bp;
        }
    }

    return NULL;
}

static void *place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

