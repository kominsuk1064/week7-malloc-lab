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
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8


#define WSIZE 4                 // header/footer 한 칸 크기
#define DSIZE 8                 // 8바이트 기준 단위, header + footer = DSIZE
#define CHUNKSIZE (1 << 12)     // heap 기본 확장 크기

#define PACK(size, alloc) ((size) | (alloc))        // size와 alloc bit를 합쳐 header/footer 값 만들기

#define GET(p) (*(unsigned int *)(p))                   // 주소 p에 있는 header/footer 값 읽기
#define PUT(p, val) (*(unsigned int *)(p) = (val))      // 주소 p에 header/footer 값 쓰기

#define GET_SIZE(p) (GET(p) & ~0x7)     // header/footer에서 크기만 꺼내기
#define GET_ALLOC(p) (GET(p) & 0x1)     // header/footer에서 할당 여부만 꺼내기

#define HDRP(bp) ((char *)(bp) - WSIZE)                             // 현재 block의 header 주소 찾기
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)        // 현재 block의 footer 주소 찾기

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))                   // 다음 block의 payload 시작 주소
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))       // 이전 block의 payload 시작 주소


/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


static char *heap_listp;        // 힙 탐색 시작 기준 포인터
static void *extend_heap(size_t words)
{
    char *bp;           // 새로 확보한 free block의 payload 시작 주소를 담을 포인터
    size_t size;        // 실제로 heap을 얼마나 늘릴지 저장하는 변수

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;       // heap 확장 크기도 8바이트 정렬에 맞추기

    if ((long)(bp = mem_sbrk(size)) == -1)      // size 만큼 heap 늘리기, 성공하면 새로 늘어난 공간 시작 주소를 bp에 저장
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));               // 새 공간은 일단 free block
    PUT(FTRP(bp), PACK(size, 0));               // 같은 정보를 footer에도 기록
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));       // 새로운 heap 끝에 epilogue 다시 세우기

    return coalesce(bp);        // 새 free block 만들기, 필요하면 앞쪽 free block과 합치기, 최종 free block 포인터 반환
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));     // 이전 block footer에서 alloc 상태 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));     // 다음 block header에서 alloc 상태 확인
    size_t size = GET_SIZE(HDRP(bp));       // 현재 free block의 전체 크기를 읽어서 size에 저장

    if (prev_alloc && next_alloc) {             // 앞 alloc, 뒤 alloc
        return bp;
    }
    else if (prev_alloc && !next_alloc) {       // 앞 alloc, 뒤 free
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));      // 다음 block size를 현재 size에 더하기
        PUT(HDRP(bp), PACK(size, 0));               // 합쳐진 큰 block의 header를 현재 block 위치에 기록
        PUT(FTRP(bp), PACK(size, 0));               // 합쳐진 큰 block의 footer를 새 끝 위치에 기록
    }
    else if (!prev_alloc && next_alloc) {       // 앞 free, 뒤 alloc
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));      // 이전 block size를 더함
        PUT(FTRP(bp), PACK(size, 0));               // 합쳐진 큰 block의 footer는 현재 block 끝 쪽에 생김
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    // 합쳐진 큰 block의 header는 이전 block 자리에서 시작
        bp = PREV_BLKP(bp);                         // 최종 free block 시작점은 이전 block 이므로 bp를 옮김
    }
    else {                                      // 앞 free, 뒤 free
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
        GET_SIZE(HDRP(NEXT_BLKP(bp)));              // 이전 block size + 현재 size + 다음 block size 모두 합산
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    // 가장 앞 block 자리에서 새 header 기록
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));    // 가장 뒤 block 끝자리에서 새 footer 기록
        bp = PREV_BLKP(bp);                         // 최종 free block 시작점은 이전 block
    }
    
    return bp;      // 최종적으로 합쳐진 free block의 payload 주소 반환
}

static void *find_fit(size_t asize)
{
    void *bp;       // heap을 순회하면서 각 block의 payload 시작 주소를 가리킬 포인터

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {     // heap 탐색을 heap_listp부터 시작, 현재 block size가 0보다 큰 동안 반복, 현재 block 끝나면 다음 block payload로 이동
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {        // 현재 block이 free이고, 요청 크기를 다음 만큼 크면 할당 가능
            return bp;      // first fit 방식이므로 처음으로 맞는 block 찾자마자 바로 변환
        }
    }

    return NULL;        // heap 끝까지 갔는데도 맞는 free block이 없으면 실패
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));          // 현재 free block의 전체 크기를 읽어서 csize에 저장

    if ((csize - asize) >= (2 * DSIZE)) {       // 현재 free block에서 요청 크기만큼 쓰고 남는 공간이 최소 block 크기 이상이면 split
        PUT(HDRP(bp), PACK(asize, 1));          // 현재 free block의 앞부분을 크기 asize, allocated 상태로 바꿈
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);                     // 방금 배치한 allocated block 다음으로 이동, 그 뒤 남는 공간을 새 free block으로 기록
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else {                                      // 남는 공간이 너무 작으면 쪼개지 말고 block 전체를 allocated
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)       // 힙에서 16바이트 확보
        return -1;

    PUT(heap_listp, 0);                                 // 첫 칸은 padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));      // prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));      // prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));          // epilogue header

    heap_listp += (2 * WSIZE);      // heap_listp를 실제 탐색하기 위한 위치 조정

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)     // heap을 늘려서 첫 free block 만들기
        return -1;

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
        return NULL;
    else
    {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
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
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}