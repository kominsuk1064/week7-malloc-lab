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
    "Minsuk Ko",
    /* First member's email address */
    "kms106418@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// header/footer 한 칸 크기
#define WSIZE 4
// 8바이트 기준 단위, header + footer = DSIZE
#define DSIZE 8
// heap 기본 확장 크기
#define CHUNKSIZE (1 << 12)

// size와 alloc bit를 합쳐 header/footer 값 만들기
#define PACK(size, alloc) ((size) | (alloc))
// 주소 p에 header/footer 값 쓰기
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 주소 p에 있는 header/footer 값 읽기
#define GET(p) (*(unsigned int *)(p))
// header/footer에서 크기만 꺼내기
#define GET_SIZE(p) (GET(p) & ~0x7)
// header/footer에서 할당 여부만 꺼내기
#define GET_ALLOC(p) (GET(p) & 0x1)

// 현재 block의 header 주소 찾기
#define HDRP(bp) ((char *)(bp) - WSIZE)
// 현재 block의 footer 주소 찾기
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음 block의 payload 시작 주소
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
// 이전 block의 payload 시작 주소
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))


// 요청 크기와 기본 확장 크기 중 더 큰 값 선택할 때 사용
#define MAX(x, y) ((x) > (y) ? (x) : (y))


// 힙 탐색 시작 기준 포인터
static char *heap_listp;

// heap을 늘려 새 free block을 만드는 함수
static void *extend_heap(size_t words);
// 인접한 free block들을 합치는 함수
static void *coalesce(void *bp);
// 요청 크기를 만족하는 free block을 찾는 함수
static void *find_fit(size_t asize);
// 요청 크기를 만족하는 free block을 찾는 함수
static void place(void *bp, size_t asize);

/*
 * heap을 늘려 새 free block을 만드는 함수
 * words: 몇 워드(word)만큼 heap을 늘릴지 나타내는 값
 * return: 새로 만들어진 free block(또는 coalesce 후 block)의 payload 포인터, 실패 시 NULL
 */
static void *extend_heap(size_t words)
{
    // 새로 확보한 free block의 payload 시작 주소를 담을 포인터
    char *bp;
    // 실제로 heap을 얼마나 늘릴지 저장하는 변수
    size_t size;

    // heap 확장 크기도 8바이트 정렬에 맞추기
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // size 만큼 heap 늘리기, 성공하면 새로 늘어난 공간 시작 주소를 bp에 저장
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    // 새 공간은 일단 free block
    PUT(HDRP(bp), PACK(size, 0));
    // 같은 정보를 footer에도 기록
    PUT(FTRP(bp), PACK(size, 0));
    // 새로운 heap 끝에 epilogue 다시 세우기
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    // 새 free block 만들기, 필요하면 앞쪽 free block과 합치기, 최종 free block 포인터 반환
    return coalesce(bp);
}

/*
 * 인접한 free block들을 합치는 함수
 * bp: 현재 free 상태인 block의 payload 시작 주소
 * return: 합쳐진 뒤 최종 free block의 payload 포인터
 */
static void *coalesce(void *bp)
{
    // 이전 block footer에서 alloc 상태 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // 다음 block header에서 alloc 상태 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // 현재 free block의 전체 크기를 읽어서 size에 저장
    size_t size = GET_SIZE(HDRP(bp));

    // 앞 alloc, 뒤 alloc
    if (prev_alloc && next_alloc)
    { 
        return bp;
    }

    // 앞 alloc, 뒤 free
    else if (prev_alloc && !next_alloc)
    {                                      
        // 다음 block size를 현재 size에 더하기    
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        // 합쳐진 큰 block의 header를 현재 block 위치에 기록
        PUT(HDRP(bp), PACK(size, 0));
        // 합쳐진 큰 block의 footer를 새 끝 위치에 기록
        PUT(FTRP(bp), PACK(size, 0));
    }
    
    // 앞 free, 뒤 alloc
    else if (!prev_alloc && next_alloc)
    {
        // 이전 block size를 더함         
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        // 합쳐진 큰 block의 footer는 현재 block 끝 쪽에 생김
        PUT(FTRP(bp), PACK(size, 0));
        // 합쳐진 큰 block의 header는 이전 block 자리에서 시작
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

        // 최종 free block 시작점은 이전 block 이므로 bp를 옮김
        bp = PREV_BLKP(bp);
    }

    // 앞 free, 뒤 free
    else
    {
        // 이전 block size + 현재 size + 다음 block size 모두 합산
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));

        // 가장 앞 block 자리에서 새 header 기록
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        // 가장 뒤 block 끝자리에서 새 footer 기록
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        // 최종 free block 시작점은 이전 block
        bp = PREV_BLKP(bp);
    }

    // 최종적으로 합쳐진 free block의 payload 주소 반환
    return bp;
}

/*
 * 요청 크기를 만족하는 free block을 찾는 함수
 * asize: header/footer와 정렬을 포함한 실제 요청 block 크기
 * return: 조건에 맞는 free block의 payload 포인터, 없으면 NULL
 */
static void *find_fit(size_t asize)
{
    // heap을 순회하면서 각 block의 payload 시작 주소를 가리킬 포인터
    void *bp;

    // heap 탐색을 heap_listp부터 시작, 현재 block size가 0보다 큰 동안 반복, 현재 block 끝나면 다음 block payload로 이동
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        // 현재 block이 free이고, 요청 크기를 다음 만큼 크면 할당 가능 
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) 
        {
            // first fit 방식이므로 처음으로 맞는 block 찾자마자 바로 변환   
            return bp;
        }
    }

    // heap 끝까지 갔는데도 맞는 free block이 없으면 실패
    return NULL;
}

/*
 * 요청 크기를 만족하는 free block을 찾는 함수
 * bp: 배치할 대상 free block의 payload 시작 주소
 * asize: 실제로 배치할 block 크기
 * return: 반환값 없음
 */
static void place(void *bp, size_t asize)
{
    // 현재 free block의 전체 크기를 읽어서 csize에 저장
    size_t csize = GET_SIZE(HDRP(bp));

    // 현재 free block에서 요청 크기만큼 쓰고 남는 공간이 최소 block 크기 이상이면 split
    if ((csize - asize) >= (2 * DSIZE))
    {
        // 현재 free block의 앞부분을 크기 asize, allocated 상태로 바꿈                
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        // 방금 배치한 allocated block 다음으로 이동, 그 뒤 남는 공간을 새 free block으로 기록
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }

    // 남는 공간이 너무 작으면 쪼개지 말고 block 전체를 allocated
    else
    { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * 힙의 초기 구조를 세팅
 * return: 성공하면 0, 실패하면 -1
 */
int mm_init(void)
{
    // 힙에서 16바이트 확보
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    // 첫 칸은 padding
    PUT(heap_listp, 0);
    // prologue header
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    // prologue footer
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    // epilogue header
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));

    // heap_listp를 실제 탐색하기 위한 위치 조정
    heap_listp += (2 * WSIZE);

    // heap을 늘려서 첫 free block 만들기
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }

    return 0;
}

/*
 * 요청 크기만큼 메모리 block을 할당
 * size: 사용자가 요청한 payload 크기(byte 단위)
 * return: 할당된 block의 payload 포인터, 실패 시 NULL
 */
void *mm_malloc(size_t size)
{
    // 실제 block 크기
    size_t asize;
    // heap을 얼마나 늘릴지
    size_t extendsize;
    // 찾거나 새로 만든 block의 payload 주소
    char *bp;

    // 사용자가 0바이트 요청하면 그냥 NULL
    if (size == 0) {
        return NULL;
    }

    // 너무 작은 요청은 최소 block 크기로 처리
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    }

    // payload + 관리 정보까지 포함해서, 8바이트 정렬된 실제 block 크기 만들기
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    // find_fit으로 자리찾기
    if ((bp = find_fit(asize)) != NULL)
    {
        // place로 자리 확정하기
        place(bp, asize);
        return bp;
    }

    // 요청 크기와 기본 확장 크기 중 더 큰 걸 heap 확장 크기로 쓰기
    extendsize = MAX(asize, CHUNKSIZE);

    // extend_heap 호출해서 새 free block 만들기        
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) 
        return NULL;

    // 방금 확장해서 얻은 free block에 실제 요청 block 배치, 그 payload 주소 반환
    place(bp, asize);
    return bp;
}

/*
 * 할당된 block을 free 상태로 바꾸고 필요하면 coalesce
 * bp: free할 block의 payload 시작 주소
 */
void mm_free(void *bp)
{
    // 현재 block의 전체 크기 읽기
    size_t size = GET_SIZE(HDRP(bp));

    // 현재 block의 header를 크기 : size, alloc bit : 0으로 다시 쓰기
    PUT(HDRP(bp), PACK(size, 0));
    // 같은 정보도 footer에 쓰기
    PUT(FTRP(bp), PACK(size, 0));
    
    // 현재 block을 free로 바꿨으니 앞뒤 block도 free인지 보고 합칠 수 있으면 합치기
    coalesce(bp);
}

/*
 * 기존 block의 크기를 조정
 * ptr: 기존에 할당받아 사용 중인 block의 payload 시작 주소
 * size: 새로 요청하는 payload 크기(byte 단위)
 * return: 크기 조정 후 사용할 새 payload 포인터, 실패 시 NULL
 */
void *mm_realloc(void *ptr, size_t size)
{
    // realloc(NULL, size)는 malloc(size)와 같음
    if (ptr == NULL) {  
        return mm_malloc(size);
    }

    // 크기를 0으로 줄이라는 요청이면 그냥 free하고 NULL 반환
    if (size == 0) 
    { 
        mm_free(ptr);
        return NULL;
    }

    // 새 크기에 맞는 block을 하나 새로 받기
    void *newptr = mm_malloc(size); 

    // 실패하면 더 할 수 있는 게 없으니 NULL
    if (newptr == NULL)             
        return NULL;

    // 기존 메모리 블록의 전체 크기에서 header와 footer 크기를 빼서, 실제 데이터가 들어 있던 payload 크기
    // HDRP(ptr) = 현재 block의 header 주소
    size_t oldsize = GET_SIZE(HDRP(ptr)) - DSIZE;
    // 새 요청 크기와 이전 payload 크기 중 더 작은 값만큼만 복사
    size_t copysize = size < oldsize ? size : oldsize; 

    // old payload 내용을 new payload로 copysize 만큼 복사
    memcpy(newptr, ptr, copysize); 
    // old block free해서 다시 재사용 가능하게 돌려놓기
    mm_free(ptr);                  

    // 이제부터 사용자는 새 block 사용
    return newptr; 
}