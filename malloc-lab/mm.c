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

// 이 free block의 이전 free block 주소가 들어있는 칸
#define PRED(bp) (*(void **)(bp))
// 이 free block의 다음 free block 주소가 들어있는 칸
#define SUCC(bp) (*(void **)((char *)(bp) + DSIZE))
// DSIZE + pred(8바이트) + succ(8바이트)
#define MINBLOCKSIZE (3 * DSIZE)


// 힙 탐색 시작 기준 포인터
static char *heap_listp;
// free block 연결리스트의 시작 포인터
static void *free_listp;

// heap을 늘려 새 free block을 만드는 함수
static void *extend_heap(size_t words);
// 인접한 free block들을 합치는 함수
static void *coalesce(void *bp);
// 요청 크기를 만족하는 free block을 찾는 함수
static void *find_fit(size_t asize);
// 요청 크기를 만족하는 free block을 찾는 함수
static void place(void *bp, size_t asize);

static void insert_free_block(void *bp);
static void remove_free_block(void *bp);

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

    // 병합 하고, free list에서 remove/insert도 하고 최종 free block 반환
    return coalesce(bp);
}

/*
 * 현재 free block과 인접한 free block들을 합친 뒤,
 * 최종 free block을 explicit free list에 넣고 그 payload 포인터 반환
 * bp: 현재 free 상태인 block의 payload 시작 주소
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
        // free list에 등록
        insert_free_block(bp);
        return bp;
    }

    // 앞 alloc, 뒤 free
    else if (prev_alloc && !next_alloc)
    {
        // 다음 free block은 free list에서 제거
        remove_free_block(NEXT_BLKP(bp));

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
        // 이전 free block은 free list에서 제거
        remove_free_block(PREV_BLKP(bp));

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
        // 앞, 뒤 free block 둘 다 free list에서 제거
        remove_free_block(PREV_BLKP(bp));
        remove_free_block(NEXT_BLKP(bp));

        // 이전 block size + 현재 size + 다음 block size 모두 합산
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));

        // 가장 앞 block 자리에서 새 header 기록
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        // 가장 뒤 block 끝자리에서 새 footer 기록
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        // 최종 free block 시작점은 이전 block
        bp = PREV_BLKP(bp);
    }

    insert_free_block(bp);
    // 최종적으로 합쳐진 free block의 payload 주소 반환
    return bp;
}

/*
 * 요청 크기를 만족하는 free block을 explicit free list에서 찾는 함수
 * asize: header/footer와 정렬을 포함한 실제 요청 block 크기
 * return: 조건에 맞는 free block의 payload 포인터, 없으면 NULL
 */
static void *find_fit(size_t asize)
{
    // heap을 순회하면서 각 block의 payload 시작 주소를 가리킬 포인터
    void *bp;

    // 빈 block 목록만 순회, 다음 free block이 없으면 끝, SUCC(bp)를 타고 리스트 따라가기
    for (bp = free_listp; bp != NULL; bp = SUCC(bp))
    {
        // 요청 크기가 다음 만큼 크면 할당 가능 
        if (GET_SIZE(HDRP(bp)) >= asize)
        {
            // first fit 방식이므로 처음으로 맞는 block 찾자마자 바로 변환   
            return bp;
        }
    }

    // heap 끝까지 갔는데도 맞는 free block이 없으면 실패
    return NULL;
}

/*
 * free block에 요청 block을 배치하고 필요하면 split
 * bp: 배치할 대상 free block의 payload 시작 주소
 * asize: 실제로 배치할 block 크기
 */
static void place(void *bp, size_t asize)
{
    // 현재 free block의 전체 크기를 읽어서 csize에 저장
    size_t csize = GET_SIZE(HDRP(bp));

    // 현재 free block은 이제 사용된 것이므로 free list에서 제거
    remove_free_block(bp);

    // 남는 공간이 새 free block이 될 만큼 크면 split
    if ((csize - asize) >= MINBLOCKSIZE)
    {
        // 현재 free block의 앞부분을 크기 asize, allocated 상태로 바꿈                
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        // split후 뒤쪽 공간을 free block으로 기록
        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(csize - asize, 0));
        PUT(FTRP(next_bp), PACK(csize - asize, 0));

        // remove한 free block대신 새로 남은 free block을 리스트에 다시 넣기
        insert_free_block(next_bp);
    }

    // 남는 공간이 너무 작으면 쪼개지 말고 block 전체를 allocated
    else
    { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * free block을 explicit free list 맨 앞에 삽입
 * bp: 삽입할 free block의 payload 시작 주소
 */
static void insert_free_block(void *bp)
{
    // 새 block은 맨 앞에 들어오므로 이전 노드 X
    PRED(bp) = NULL;
    // 새 block의 다음 노드는 기존 첫 free block
    SUCC(bp) = free_listp;

    // 기존 첫 free block이 있었다면
    if (free_listp != NULL) {
        // 그 block의 이전 노드를 새 block으로 바꿈
        PRED(free_listp) = bp;
    }
    // 새 block이 리스트의 첫 노드
    free_listp = bp;
}

/*
 * free block을 explicit free list에서 제거
 * bp: 제거할 free block의 payload 시작 주소
 */
static void remove_free_block(void *bp)
{
    // case 1. 중간노드 제거
    if (PRED(bp) != NULL) {
        SUCC(PRED(bp)) = SUCC(bp);
    }
    // case 2. 맨 앞 노드 제거
    else {
        free_listp = SUCC(bp);
    }
    // case 3. 마지막 노드 제거
    if (SUCC(bp) != NULL) {
        PRED(SUCC(bp)) = PRED(bp);
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

    heap_listp += (2 * WSIZE);

    // explicit free list는 처음엔 비어 있는 상태
    free_listp = NULL;

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
    // 정렬과 header/footer까지 포함한 실제 요청 block 크기
    size_t asize;
    // 현재 block의 전체 크기
    size_t oldsize;
    // 바로 뒤 block의 전체 크기
    size_t nextsize;
    // 현재 block과 다음 block을 합쳤을 때의 전체 크기
    size_t total;
    // fallback시 실제 복사할 크기
    size_t copysize;
    // 다음 block의 payload 주소
    void *next_bp;
    // split 후 남는 free block의 payload 주소
    void *split_bp;
    // 새로 할당받은 block의 payload 주소
    void *newptr;

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

    // asize = 할당기가 실제로 필요한 block 전체 크기
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    }
    else {
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    }

    // 현재 block의 header에서 block 전체 크기 읽기
    oldsize = GET_SIZE(HDRP(ptr));

    // 지금 block 자체가 이미 새 요청 크기를 만족하면 새 block 만들 필요 X
    if (oldsize >= asize)
    {
        // 쓰고 남는 공간이 크다면 split
        if ((oldsize - asize) >= MINBLOCKSIZE)
        {
            // 현재 block의 크기를 asize로 줄이고 allocated 상태로 다시 기록
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));

            // 현재 block 뒤쪽에 남은 공간을 새 free block으로 만들기
            // header/footer를 free 상태로 쓰고 필요하면 coalesce
            split_bp = NEXT_BLKP(ptr);
            PUT(HDRP(split_bp), PACK(oldsize - asize, 0));
            PUT(FTRP(split_bp), PACK(oldsize - asize, 0));
            coalesce(split_bp);
        }
        // 기존 ptr 그대로 사용
        return ptr;
    }

    // 현재 block 바로 뒤에 있는 다음 block 찾기
    next_bp = NEXT_BLKP(ptr);

    // 다음 block이 free라면 현재 block과 합쳐서 제자리 확장이 가능한지 확인
    if (!GET_ALLOC(HDRP(next_bp)))
    {
        // 다음 block 크기를 읽고, 현재 block과 합친 전체 크기 계산
        nextsize = GET_SIZE(HDRP(next_bp));
        total = oldsize + nextsize;

        // 합친 크기가 새 요청 크기를 만족하면 새 block 할당 없이 현재 자리에서 해결 가능
        if (total >= asize)
        {
            remove_free_block(next_bp);
            
            // 합치고 남는 공간이 충분히 크면 split해서 뒤쪽을 free block으로 남김
            if ((total - asize) >= MINBLOCKSIZE)
            {
                // 현재 block은 실제로 필요한 크기만 쓰고 그 크기로 header/footer 맞추기
                PUT(HDRP(ptr), PACK(asize, 1));
                PUT(FTRP(ptr), PACK(asize, 1));

                // 합친 전체 공간에서 남는 부분을 free block으로 만들기
                split_bp = NEXT_BLKP(ptr);
                PUT(HDRP(split_bp), PACK(total - asize, 0));
                PUT(FTRP(split_bp), PACK(total - asize, 0));
                coalesce(split_bp);
            }
            // 남는 공간이 너무 작으면 split하지 않고 합친 전체 block을 그대로 사용
            else
            {
                PUT(HDRP(ptr), PACK(total, 1));
                PUT(FTRP(ptr), PACK(total, 1));
            }
            // 기존 ptr 그대로 사용
            return ptr;
        }
    }

    // 새 크기에 맞는 block을 하나 새로 받기
    newptr = mm_malloc(size); 

    // 실패하면 더 할 수 있는 게 없으니 NULL
    if (newptr == NULL) {          
        return NULL;
    }

    // old payload 크기 구하고 새 요청 크기보다 크면 새 요청 크기로 줄이기
    copysize = oldsize - DSIZE;
    if (size < copysize) {
        copysize = size;
    }

    // old payload 내용을 new payload로 copysize 만큼 복사
    memcpy(newptr, ptr, copysize); 
    // old block free해서 다시 재사용 가능하게 돌려놓기
    mm_free(ptr);                  

    // 이제부터 사용자는 새 block 사용
    return newptr; 
}
