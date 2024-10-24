#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <memlib.h>

/* 기본 상수와 매크로 */
#define WSIZE       4       /* 워드와 헤더/푸터 사이즈(바이트) */
#define DSIZE       8       /* 더블 워드 사이즈(바이트) */
#define CHUNKSIZE  (1<<12)  /* 힙을 확장할 기본 크기 */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 패킹과 언패킹 매크로 */
#define PACK(size, alloc)   ((size) | (alloc))

/* 주소 p에서 읽고 쓰는 매크로 */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* 주소 p에서 크기와 할당 비트를 읽는 매크로 */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 블록 포인터 bp를 사용하여 헤더와 푸터의 주소를 계산하는 매크로 */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 다음과 이전 블록의 주소를 계산하는 매크로 */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* 함수 선언 */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 처음 사용할 가용 리스트의 시작을 저장할 포인터 */
static char *heap_listp = 0;

/* 메모리 관리 초기화 함수 */
int mm_init(void)
{
    /* 힙 초기화: 빈 가용 리스트를 생성하고 기본적인 힙 구조를 설정 */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                             /* Alignment 패딩 */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* 프롤로그 헤더 */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* 프롤로그 푸터 */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* 에필로그 헤더 */
    heap_listp += (2*WSIZE);

    /* CHUNKSIZE만큼 힙을 확장하고 초기 가용 블록을 생성 */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* 힙을 확장하는 함수 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 요청한 크기를 워드 크기의 배수로 반올림하여 실제 확장할 크기를 결정 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* 새로 할당된 블록의 헤더와 푸터를 설정하고 에필로그 헤더를 이동 */
    PUT(HDRP(bp), PACK(size, 0));         /* 가용 블록 헤더 */
    PUT(FTRP(bp), PACK(size, 0));         /* 가용 블록 푸터 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* 새 에필로그 헤더 */

    /* 가용 블록을 병합하고 병합된 블록의 시작 주소를 반환 */
    return coalesce(bp);
}

/* 블록을 병합하는 함수 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* 이전과 다음 블록 모두 할당되어 있음 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* 다음 블록만 가용 상태 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {      /* 이전 블록만 가용 상태 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                     /* 이전과 다음 블록 모두 가용 상태 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
              GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/* 메모리 할당 함수 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* 할당할 블록의 크기 */
    size_t extendsize; /* 힙이 가득 찼을 때 확장할 크기 */
    char *bp;

    /* 잘못된 요청이면 무시 */
    if (size == 0)
        return NULL;

    /* 요청 크기를 조정하여 최소 크기를 유지 */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* 가용 블록을 찾고, 할당할 공간이 있으면 배치 */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* 가용 블록이 없으면 힙을 확장하고 새 블록을 할당 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/* 메모리 해제 함수 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* 블록을 찾는 함수 */
static void *find_fit(size_t asize)
{
    /* 처음부터 끝까지 가용 블록을 탐색 */
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL;
}

/* 블록을 배치하는 함수 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
