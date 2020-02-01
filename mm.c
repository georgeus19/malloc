/*
 * My malloc package uses explicit free lists as the main structure of 
 * the heap. Each block does have a header and footer both of which have
 * the same information about block - size, alloc/free bit.
 *
 * New free blocks are always inserted to the beginning of the explicit
 * list. Blocks are coalesced instantly after they are freed - New merged
 * block is inserted via standard instering procedure and the previous
 * blocks are removed from the explicit list. The find_fit (find_place
 * in my case) uses first_fit alg. to find the first free block in the
 * explicit free list.	
 *
 * Initially, prolog and epilog blocks are created to avoid corner cases
 * near the both ends of the heap. Although prolog block does not move
 * at all epilogue block is always the block with highest address.
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
    "Krystof Hruby",
    /* First member's email address */
    "krhr@itu.dk",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */

typedef size_t word;
#define WSIZE 4
#define DSIZE 8
#define ALIGNMENT 8

// Min block size
#define MBLK_SIZE 24
#define CHUNKSIZE (1<<9) // the higher the better perf but worse util.

#define MAX(x,y) (((x) > (y)) ? (x) : (y))
// Store block size and alloc bit
#define PACK(size, alloc) ((size) | (alloc))

// Get the word value at adr p
#define GET(p) (*((word *)(p)))
// Assign given val to adr p
#define PUT(p, val) (*((word *)(p)) = (val))
// Assign given ptr to the address pointed by p
#define PUTP(p, ptr) (*((void **)(p)) = (void *)(ptr))
// Get the ptr at adr p
#define GETP(p) (*((void **)(p)))

// Compute block size, allocation bit
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// pp means pointer to payload(or supposed payload mem in free block)
// Given payload ptr pp, compute address of header and footer 
#define HDRP(pp) ((char *)(pp) - WSIZE)
#define FTRP(pp) ((char *)(pp) + GET_SIZE(HDRP(pp)) - DSIZE)

// Given payload ptr pp, compute payload ptrs of next and prev blocks
#define NEXT_PP(pp) ((char *)(pp) + GET_SIZE((HDRP(pp))))  
#define PREV_PP(pp) ((char *)(pp) - GET_SIZE(((char *)(pp) - DSIZE)))

// Compute position of pointers that point to previous (resp. next) block.
#define PRED(pp) (pp)
#define SUCC(pp) ((void *)((char * )pp + DSIZE))

// Check if the block is free and if the size if lower than or equal to
// size of the ptr block.
#define GOOD_FIT(ptr, size) (!GET_ALLOC(HDRP(ptr)) && (size) <= GET_SIZE(HDRP(ptr)))


/* Rounds up to the nearest multiple of ALIGNMENT - DSIZE */
#define ALIGN(size) (((size) + (DSIZE-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void * heapp = NULL; /* Ptr to epilogue block */
static void * listp = NULL; /* Ptr to head of the list */
static void * start = NULL; /* Ptr to block where last search ended
								- for second fit alg - not implemented yet */

static void print_free_list();
static int same_boundaries(void *);
static void print_block(void *);
int mm_init();
int mm_check();
static void remove_blk(void *);
static void insert_blk(void *);
static int check_alignment(void *);
static void set_boundaries(void *, word, int);
static void * extend_heap(word);
static void place(void*, word);
static void * first_fit(word);

/*
	insert_blk - Insert the pp block to the beginning of the free list.
*/

static void insert_blk(void * pp) {
	if (listp == NULL) { /* Check if the list is empty. If so, add first block */
		PUTP(SUCC(pp), NULL);
	}
	else {	// Add block to the beginning of the list
		PUTP(SUCC(pp), listp);
		// Make previous first block (now next) point to new first block (<-pp)
		PUTP(PRED(listp), pp); 
	}

	PUTP(PRED(pp), NULL);
	// pp block is now the first block in the free list.
	listp = pp;
}

/*
	remove_blk - Removes the pp block from the free list.
*/
static void remove_blk(void * pp) {
	void * prev = GETP(PRED(pp));
	void * next = GETP(SUCC(pp));
	
	// If next block exists, it is linked to previous block or NULL
	if (next != NULL) {
		PUTP(PRED(next), prev);
	}
	
	// If the block is the first one in the list, make next block the first.
	if (prev == NULL) {
		listp = next;	
	}
	else {	// Add link from previous block to next block or NULL
		PUTP(SUCC(prev), next);
	}
}

/*
	coalesce - Do coalescing. Tries to merge pp block with adjacent free blocks.
		- Also puts the final block to the free list as the first block.
		- The adjancent free blocks are removed from the free list.
*/

static void * coalesce(void * pp) {
	void * next = NEXT_PP(pp);
	void * prev = PREV_PP(pp);

	// The payload ptr is not pp when previous block is free.
	// Set the final ptr in resp in each case.
	void * resp = NULL;
	word next_alloc = GET_ALLOC(HDRP(next));
	word prev_alloc = GET_ALLOC(FTRP(prev));
	word size = GET_SIZE(HDRP(pp));
	
		// previous alloc, next alloc
	if (prev_alloc && next_alloc) {
		resp = pp;
	}	// previous alloc, next free
	else if (prev_alloc && !next_alloc) {
		size += GET_SIZE(HDRP(next));
		remove_blk(next);
		resp = pp;
	}	// previous free, next alloc
	else if (!prev_alloc && next_alloc) {
		size += GET_SIZE(HDRP(prev));
		resp = prev;
		remove_blk(prev);
	}	// previous free, next free
	else if (!prev_alloc && !next_alloc) {
		size += GET_SIZE(HDRP(prev)) + GET_SIZE(HDRP(next));
		resp = prev;
		remove_blk(prev);
		remove_blk(next);
	}

	set_boundaries(resp, size, 0);
	insert_blk(resp);
	return resp;
} 

/*
	extend_heap - Extends heap by words * WSIZE. 
		- If words is odd, it is incremented for correct alignment. 
*/
static void * extend_heap(word words) {
	void * pp;
	word size;
	
	// Compute the number of bytes to extend the heap for.
	// If words if odd, inc it by one.
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;	
	//size = ALIGN(size);
	
	// Extend heap by `size`.
	pp = mem_sbrk(size);
	if (pp == (void *)-1) {
		return NULL;
	}
	
	set_boundaries(pp, size, 0);
	// Alloc new epilogue header
	PUT(HDRP(NEXT_PP(pp)), PACK(0, 1));
		
	// Tries to coalesce the new block with previous block
	// and inserts the block to the beginning of free list.
	return coalesce(pp);
}

/* 
 * mm_init - initialize the malloc package.
	- Padding is first word of heap.
	- Prologue of size MLBK_SIZE - won't change
	- Epilogue - only header - 4B is always at the end of the 
		allocated heap (= highest 4B)

	- Also allocates first memory chunk.
 */
int mm_init(void)
{	
	heapp = mem_sbrk(8 * WSIZE);
	if (heapp == (void*)-1) {
		return -1;
	}

	PUT(heapp, 0);
	PUT((char *)heapp + WSIZE, PACK(MBLK_SIZE, 1));
	PUT((char *)heapp + 6 * WSIZE, PACK(MBLK_SIZE, 1));
	PUT((char *)heapp + 7 * WSIZE, PACK(0, 1));
	heapp =(char *)heapp +  2 * WSIZE;


	PUTP((char *)heapp, NULL);
	PUTP((char *)heapp + 2 * WSIZE, NULL);

	listp = heapp;
	// Extend heap by CHUNKSIZE.
	void * tmp = extend_heap(CHUNKSIZE/WSIZE);
	if (tmp == NULL) {
		return -1;
	}	
	listp = tmp;
//	printf("listp heapp %p %p\n", listp, heapp);	
    return 0;
}

/*
	first_fit - First fit algorithm implementation to find the first
		large enough free block in the free list.
*/
static void * first_fit(word size) {
	void * pp = listp;
	while (pp != NULL) {
//		if (size <= GET_SIZE(HDRP(pp))) {
//			return pp;
//		}
//		if (GET_ALLOC(HDRP(pp))) {
//			printf("alloc block in free list\n");
//		}
		// Checking if it is free block and if it is large enough.
		if (GOOD_FIT(pp, size)) {
			return pp;
		}
		pp = GETP(SUCC(pp));
	}	
	return NULL;
}

/*
	all_blocks_search - Search over all block to find large enough free block.
*/
static void * all_blocks_search(word size) {
	void * ptr = heapp;
	void * top = mem_heap_hi();
	while (ptr < top) {
		if (GOOD_FIT(ptr, size)) {
			return ptr;
		}
		ptr = NEXT_PP(ptr);
	}
	return NULL;
}

/*
	next_fit - next_fit alogrithm to find free block in free list.
*/
static void * next_fit(word size) {
	void * ptr = start;	
	while (ptr != NULL) {
	if (GOOD_FIT(ptr, size)) {
		return ptr;
	}
	ptr = GETP(SUCC(ptr));
	}
	ptr = listp;
	while (ptr != start) {
	if (GOOD_FIT(ptr, size)) {
		return ptr;
	}

	ptr = GETP(SUCC(ptr));
	}
	return NULL;
}

/*
	find_place - find a free block in the free list 
	that can be used to allc a block of given size.
*/
static void * find_place(word size) {
	return first_fit(size);	
	void * pp;
	for (pp = listp; GET_ALLOC(HDRP(pp)) == 0; pp = GETP(SUCC(pp))) {
		if (GET_SIZE(HDRP(pp)) >= size) {
			return pp;
		}
	}
	return NULL;
}

/*
	place - Allocate a block of given size where pp is.
*/
static void place(void * pp, word size) {
	word block_size = GET_SIZE(HDRP(pp));
	// Check if a part of free block becomes smaller free block.
	if ((block_size - size) >= MBLK_SIZE) {
		//insert(GETP(PRED(pp)), pp_new, GETP(SUCC(pp)));
		// Alloc the block.
		set_boundaries(pp, size, 1);
		void * pp_new = NEXT_PP(pp);
		remove_blk(pp);
		// Insert the new smaller free block to the free list.
		set_boundaries(pp_new, block_size - size, 0);
		//coalesce(pp_new);		
		insert_blk(pp_new);
	}
	else {	// free block is gone
		remove_blk(pp);
		set_boundaries(pp, block_size, 1);
	}
}

/* 
 * mm_malloc - Allocate a block of given size.
	The actual size is aligned to be a multiple of the ALIGNMENT
	and is increased by size of boundary tags.
	The min size of adjusted block is MBLK_SIZE.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{	
	//mm_check();
	word asize;
	void * pp;

	if (size == 0) {
		printf("\nsize = 0 weird\n");
		return NULL;
	}

	// Align size to multiple of ALIGNMENT
	// Add sizeof(boundary_tags)
	// if size is too small set it to MBLK_SIZE
	if ((ALIGN(size) + DSIZE) <  MBLK_SIZE) {
		asize = MBLK_SIZE;
	}	
	else {
		asize = ALIGN(size) + DSIZE;
	}

	// Try to find place in free list to fit the block
	pp = find_place(asize);
	// If found, put the block on found place - pp
	if (pp != NULL) {
		place(pp, asize);
		return pp;
	}
	// Heap needs to be enlarged.
	asize = MAX(asize, CHUNKSIZE);
	pp = extend_heap(asize/WSIZE);
	if (pp == NULL) {
		return NULL;
	}
	
	// Place the block on given place - pp
	place(pp, asize);
	return pp;	
}


/*
 * mm_free 
	Free the block given by ptr passed in argument.
	Set boundary tags to 0 (= free block).
	Try to merge with possible adjacent free block (coalesce().)
 */
void mm_free(void *ptr)
{
	word size = GET_SIZE(HDRP(ptr));
	set_boundaries(ptr, size, 0);
	coalesce(ptr);
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

static void set_boundaries(void * ptr, word size, int alloc) {
	PUT(HDRP(ptr), PACK(size, alloc));
	PUT(FTRP(ptr), PACK(size, alloc));
}

static int check_alignment(void * ptr) {
	if ((size_t)ptr % ALIGNMENT) {
		printf("payload pointer is not aligned %p\n", ptr);
		return 0;
	}
	return 1; 
}

int mm_check() {
	void * ptr = listp;	
	int consistent = 1;
	void * tmp = ptr;
	// Check explicit free list
	printf("FIRST\n");
	while (ptr != NULL) {
		// Check if alloc bits are set to 0
		if (GET_ALLOC(HDRP(ptr))) {
			printf("incorrect alloc bit in free block header\n");
			consistent = 0;
		}
		if (GET_ALLOC(FTRP(ptr))) {
			printf("incorrect alloc bit in free block footer\n");
			consistent = 0;
		}
		if ((void*)FTRP(ptr) >= mem_heap_hi()) {
			printf("footer out of range");
		}
		if (GET_SIZE(HDRP(ptr)) != GET_SIZE(FTRP(ptr))) {
			printf("header and footer of free block are different\n");
			printf("header %zu, footer %zu\n", GET_SIZE(HDRP(ptr)), GET_SIZE(FTRP(ptr)));
			consistent = 0;
		}
		tmp = ptr;
		// Check that prev, next ptrs do not point to the block they are in
		if (GETP(PRED(ptr)) == ptr) {
			consistent = 0;
			printf("Prev pointer in free block points to the block it is in");
		}
		ptr = GETP(SUCC(ptr));
		if (tmp == ptr) { 
			printf("Succ pointer in free block points to the block it is in");
			consistent = 0;
			print_block(ptr);
			if (GETP(SUCC(ptr)) != NULL) {
				print_block(GETP(SUCC(ptr)));
			}
			if (GETP(PRED(ptr)) != NULL) {
				print_block(GETP(SUCC(ptr)));
			}
		//	print_free_list();
		}
	}
	
	ptr = heapp;
	// Checking all blocks	
	void * prev = ptr;
	while(ptr <= mem_heap_hi()) {
		consistent = (consistent == 0) ? 0 : same_boundaries(ptr);
		consistent = (consistent == 0) ? 0 : check_alignment(ptr);
			// If the block is free, check if prev, next are NOT freei
			// ->(They should not be free)
		if (!GET_ALLOC(HDRP(ptr))) {
			if (GETP(SUCC(ptr)) != NULL && GETP(SUCC(ptr)) == GETP(PRED(ptr))) {
				printf("pred == succ\n");
				exit(1);
			}
			if (!GET_ALLOC(HDRP(PREV_PP(ptr)))) {
				printf("Coalescing error");
			}
			if (!GET_ALLOC(HDRP(NEXT_PP(ptr)))) {
				printf("Coalescing error");
			}
		}
		prev = FTRP(ptr);
		ptr = NEXT_PP(ptr);
		// Checking block overlaping and if there is a gap between two adjacent.
		if ((char *)prev + WSIZE > HDRP(ptr)) {
			printf("Blocks overlap");
			consistent = 0;
		} else if ((char *)prev + WSIZE != HDRP(ptr)) {
			printf("Blocks too far from each other -> There is a gap in between.");
			consistent = 0;
		} 
	}
	return consistent;
}

static int same_boundaries(void * ptr) {
	if (GET_SIZE(HDRP(ptr)) != GET_SIZE(FTRP(ptr))) {
		printf("\nheader and footer of a block are different%p\n", ptr);
		printf("header %d, footer %d\n", GET_SIZE(HDRP(ptr)), GET_SIZE(FTRP(ptr)));
		return 0;	
	}
	return 1;
}

static void is_free(void * ptr) {
	if (ptr == NULL || ptr == heapp) {
		return;
	}
	if (GET_ALLOC(HDRP(ptr))) {
		printf("this block is not free %p\n", ptr);
	}
	same_boundaries(ptr);
}

static void print_free_list() {
	printf("print_free_list()\n");
	void * ptr = listp;
	void * tmp = ptr;
	while (ptr != NULL) {
		printf(" %p", ptr);
		is_free(ptr);
		tmp = ptr;
		ptr = GETP(SUCC(ptr));
		if (tmp == ptr) {
			printf("cycle ;(");
			break;
		}
	}

	printf("\nprint all free blocks\n");
	ptr = heapp;
	while (ptr < mem_heap_hi()) {
		if (!GET_ALLOC(HDRP(ptr)) || !GET_ALLOC(FTRP(ptr))) {
			printf(" %p", ptr);
			is_free(ptr);
		}
	ptr = NEXT_PP(ptr);
	}
	printf("\n");
}

static void print_block(void * pp) {
	if (pp == NULL) {
		return;
	}
	printf("\n");
	printf("header %zu\n", GET_SIZE(HDRP(pp)));
	printf("header adr %p\n", HDRP(pp));
	printf("paylaod ptr %p\n", pp);
	printf("pred %p\n", GETP(PRED(pp)));
	printf("succ %p\n", GETP(SUCC(pp)));
	printf("footer %zu\n", GET_SIZE(FTRP(pp)));
	printf("footer adr %p\n", FTRP(pp));
	printf("\n");
}

