/*
 * mm.c - 간단한 메모리 할당기 구현
 *
 * 이 구현에서는 묵시적 가용 리스트와 경계 태그를 사용합니다.
 * 가용 블록을 탐색할 때는 first-fit 전략을 사용하며, `free` 시에는 인접한 가용 블록을 병합합니다.
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
 * 팀 정보를 여기에 작성하세요.
 ********************************************************/
//team_t team = {
//    /* 팀 이름 */
//    "YourTeamName",
//    /* 첫 번째 멤버의 전체 이름 */
//    "Your Name",
//    /* 첫 번째 멤버의 이메일 주소 */
//    "your.email@example.com",
//    /* 두 번째 멤버의 전체 이름 (없으면 공백) */
//    "",
//    /* 두 번째 멤버의 이메일 주소 (없으면 공백) */
//    ""
//};

/* 기본 상수와 매크로 */
#define WSIZE       4       /* 워드 크기 (bytes) */
#define DSIZE       8       /* 더블워드 크기 (bytes) */
#define CHUNKSIZE  (1<<12)  /* 힙을 확장할 기본 크기 (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 헤더와 풋터에 저장할 값 생성 */
#define PACK(size, alloc)  ((size) | (alloc))

/* 주소 p에서 워드를 읽거나 씁니다 */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* 헤더 또는 풋터에서 블록의 크기와 할당 상태를 가져옵니다 */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 블록 포인터 bp를 사용하여 헤더와 풋터의 주소를 계산합니다 */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 다음과 이전 블록의 블록 포인터를 계산합니다 */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* 전역 변수 */
static char *heap_listp;  /* 힙의 시작 포인터 */

/* 함수 프로토타입 선언 */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init - 메모리 할당기를 초기화합니다.
 */
int mm_init(void)
{
    /* 힙 생성: 프롤로그와 에필로그를 포함한 4워드 할당 */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                             /* 패딩 */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* 프롤로그 헤더 */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* 프롤로그 풋터 */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* 에필로그 헤더 */
    heap_listp += (2*WSIZE);

    /* 초기 가용 블록 생성 */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * extend_heap - 힙을 확장하고 초기 가용 블록을 생성합니다.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 요청한 크기를 8의 배수로 반올림하여 할당 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* 새 블록의 헤더와 풋터 설정 */
    PUT(HDRP(bp), PACK(size, 0));         /* 가용 블록 헤더 */
    PUT(FTRP(bp), PACK(size, 0));         /* 가용 블록 풋터 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* 새로운 에필로그 헤더 */

    /* 만약 이전 블록이 가용하다면 병합 */
    return coalesce(bp);
}

/*
 * coalesce - 인접한 가용 블록을 병합합니다.
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        /* 아무것도 하지 않음 */
    }
    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * mm_malloc - 요청한 크기의 메모리 블록을 할당합니다.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* 조정된 블록 크기 */
    size_t extendsize; /* 메모리 부족 시 확장 크기 */
    char *bp;

    /* 잘못된 요청 처리 */
    if (size == 0)
        return NULL;

    /* 요청한 크기를 조정 */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* 적합한 가용 블록 탐색 */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* 적합한 블록이 없으면 힙을 확장하고 할당 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * find_fit - first-fit 전략으로 적합한 가용 블록을 찾습니다.
 */
static void *find_fit(size_t asize)
{
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize))
            return bp;
    }
    return NULL; /* 적합한 블록을 찾지 못함 */
}

/*
 * place - 요청한 크기만큼의 블록을 할당하고, 필요 시 분할합니다.
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        /* 블록을 분할 */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else {
        /* 전체 블록을 할당 */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - 주어진 블록을 해제하고, 인접한 가용 블록과 병합합니다.
 */
void mm_free(void *bp)
{
    if (bp == NULL)
        return;

    size_t size = GET_SIZE(HDRP(bp));

    /* 헤더와 풋터를 업데이트하여 블록을 가용 상태로 만듭니다 */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    /* 인접한 가용 블록과 병합 */
    coalesce(bp);
}

/*
 * mm_realloc - 기존 메모리 블록의 크기를 조정합니다.
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
        return mm_malloc(size);

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    void *newptr = ptr;
    size_t copySize;
    size_t asize;

    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    size_t oldsize = GET_SIZE(HDRP(ptr));

    if (asize <= oldsize)
        return ptr;

    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t csize;

    /* 다음 블록과 병합하여 확장 가능 여부 확인 */
    if (!next_alloc && ((csize = oldsize + GET_SIZE(HDRP(NEXT_BLKP(ptr))))) >= asize) {
        PUT(HDRP(ptr), PACK(csize, 1));
        PUT(FTRP(ptr), PACK(csize, 1));
        return ptr;
    } else {
        /* 새로운 블록을 할당하고 데이터 복사 */
        newptr = mm_malloc(size);
        if (newptr == NULL)
            return NULL;
        copySize = oldsize - DSIZE;
        if (size < copySize)
            copySize = size;
        memcpy(newptr, ptr, copySize);
        mm_free(ptr);
        return newptr;
    }
}
