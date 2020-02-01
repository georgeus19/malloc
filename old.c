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

// Min block size 8 for header, footer, 16 for prev, next free blocks
#define MBLK_SIZE 32
#define CHUNKSIZE (1<<8)

#define MAX(x,y) (((x) > (y)) ? (x) : (y))
// Store block size and alloc bit
#define PACK(size, alloc) ((size) | (alloc))

// Get the word value at adr p
#define GET(p) (*((word *)(p)))
// Assign given val to adr p
#define PUT(p, val) (*((word *)(p)) = (val))
#define PUTP(p, ptr) (*((void **)(p)) = (void *)(ptr))
#define GETP(p) (*((void **)(p)))

// Compute block size, allocation bit
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// pp means pointer to payload(or supposed payload mem in free block)
// Given payload ptr pp, compute address of header and footer 
#define HDRP(pp) ((char *)(pp) - WSIZE)
#define FTRP(pp) ((char *)(pp) + GET_SIZE(HDRP(pp)) - DSIZE)

// this sounds useless after all... - Given payload ptr pp, compute block ptrs of next and prev blocks
#define NEXT_BLKP(pp) (FTRP(pp) + WSIZE) // better to implement with NEXT_PP - LESS OP
#define PREV_BLKP(pp) (HDRP(pp) - GET_SIZE(HDRP(pp) - WSIZE)) // SAME

// Given payload ptr pp, compute payload ptrs of next and prev blocks
#define NEXT_PP(pp) ((char *)(pp) + GET_SIZE((HDRP(pp))))  
#define PREV_PP(pp) ((char *)(pp) - GET_SIZE(((char *)(pp) - DSIZE)))

#define ALIGNMENT 8

#define PRED(pp) (pp)
#define SUCC(pp) ((void *)((char * )pp + DSIZE))

#define GOOD_FIT(ptr, size) (!GET_ALLOC(HDRP(ptr)) && (size) <= GET_SIZE(HDRP(ptr)))


/* Rounds up to the nearest multiple of ALIGNMENT - DSIZE */
#define ALIGN(size) (((size) + (DSIZE-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void * heapp = NULL;
static void * listp = NULL;
static void * start = NULL;
static void * lastp = NULL;

void print_free_list();


void print_block(void * pp) {
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

void set_boundaries(void * ptr, word size, int alloc) {
	PUT(HDRP(ptr), PACK(size, alloc));
	PUT(FTRP(ptr), PACK(size, alloc));
}

int heap_checker() {
// every block in free list is free?
//	printf("heap_checker()\n");
	void * ptr = listp;	
	int consistent = 1;
	size_t count = 0;
//	printf("%p\n", ptr);
	void * tmp = ptr;
/*
	while (ptr != NULL) {
		printf("prev alloc, next free low %p %p top %p\n", mem_heap_lo(), ptr, mem_heap_hi());
		if (GET_ALLOC(HDRP(ptr))) {
			printf("\nincorrect alloc bit in free block header\n");
			consistent = 0;
		}
		//printf("header %p footer %p\n", HDRP(ptr), FTRP(ptr));
		if ((void*)FTRP(ptr) >= mem_heap_hi()) {
			printf("footer out of range");
		}
		if (GET_ALLOC(FTRP(ptr))) {
			printf("\nincorrect alloc bit in free block footer\n");
			consistent = 0;
		}
		//printf("aaa\n");
		if (GET_SIZE(HDRP(ptr)) != GET_SIZE(FTRP(ptr))) {
			printf("\nheader and footer of free block are different\n");
			printf("header %d, footer %d\n", GET_SIZE(HDRP(ptr)), GET_SIZE(FTRP(ptr)));
			consistent = 0;
		}
		++count;
		tmp = ptr;
		printf("%p %p\n", ptr, GETP(SUCC(ptr)));
		ptr = GETP(SUCC(ptr));
		if (tmp == ptr) {
			print_block(ptr);
			if (GETP(SUCC(ptr)) != NULL) {
				print_block(GETP(SUCC(ptr)));
			}
			if (GETP(PRED(ptr)) != NULL) {
				print_block(GETP(SUCC(ptr)));
			}
			print_free_list();
			while (1) {;}
		}
	}
	printf("number of free blocks is %d\n", count);
*/	
//	printf("aa");
	ptr = heapp;
	
//	printf("aa");
	void * prev = ptr;
	while(ptr <= mem_heap_hi()) {
		if (GET_SIZE(HDRP(ptr)) != GET_SIZE(FTRP(ptr))) {
			printf("\nheader and footer of a block are different\n");
			printf("header %d, footer %d\n", GET_SIZE(HDRP(ptr)), GET_SIZE(FTRP(ptr)));
			consistent = 0;
		}
		
		if (!GET_ALLOC(HDRP(ptr))) {
			if (GETP(SUCC(ptr)) != NULL && GETP(SUCC(ptr)) == GETP(PRED(ptr))) {
				printf("pred == succ\n");
				exit(1);
			}
			if (!GET_ALLOC(HDRP(PREV_PP(ptr)))) {
				printf("coalescing error");
			}
			if (!GET_ALLOC(HDRP(NEXT_PP(ptr)))) {
				printf("coalescing error");
			}
		}
		prev = FTRP(ptr);
		ptr = NEXT_PP(ptr);
		if ((char *)prev + WSIZE > HDRP(ptr)) {
			printf("blocks overlap");
			consistent = 0;
		} else if ((char *)prev + WSIZE != HDRP(ptr)) {
			printf("blocks too far from each other");
			consistent = 0;
		} 
	}
//	printf("heap_checker () END");
	return consistent;
}

void same_boundaries(void * ptr) {
	if (GET_SIZE(HDRP(ptr)) != GET_SIZE(FTRP(ptr))) {
		printf("\nheader and footer of a block are different%p\n", ptr);
		printf("header %d, footer %d\n", GET_SIZE(HDRP(ptr)), GET_SIZE(FTRP(ptr)));
	}
}

void is_free(void * ptr) {
	if (ptr == NULL || ptr == heapp) {
		return;
	}
	if (GET_ALLOC(HDRP(ptr))) {
		printf("this block is not free %p\n", ptr);
	}
	same_boundaries(ptr);
}

void print_free_list() {
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

	

// prev might be heapp, next might be null
void insert(void * prev, void * curr, void * next) {
	printf("Insert %p %p %p\n", prev, curr, next);
//	is_free(prev);
//	is_free(curr);
//	is_free(next);
	if (listp == NULL) {
		listp = curr;
	}
	if (prev != NULL && next != NULL && prev == next) {
		printf("CYCLE");
		while (1) {;}
	}
	if (curr == next) {
		printf("curr == next\n");
		while (1) {;}
	}
	if (prev == curr) {
		printf("prev == curr\n");
		while (1) {;}
	}
	print_block(prev);
	print_block(curr);
	print_block(next);
	if (prev != heapp && prev != NULL) {
		PUTP(SUCC(prev), curr);
		PUTP(PRED(curr), prev);
	}
	else {
		listp = curr;
		//printf("prev NULL%p\n", prev);
		PUTP(PRED(curr), NULL);
	}
	
	PUTP(SUCC(curr), next);
	if (next != NULL) {
		PUTP(PRED(next), curr);
	}

	if (listp == next) {
		listp = curr;
	}
	print_block(prev);
	print_block(curr);
	print_block(next);
	
	printf("Insert end\n");
}

// there might be a slight difference when the block is from free() and from extend_heap()
// maybe include a hack that we try if it is the last free block and if not we search all
// if so the op is O(1) instead of O(n)
void * coalesce(void * pp) {
	printf("COALESCE START\n");
	void * next_pp = NEXT_PP(pp);
	void * prev_pp = PREV_PP(pp);
	//PUTP(next_pp, NEXT_PP(pp));
	//PUTP(prev_pp, PREV_PP(pp));
//	printf("COALESCE MID1");
	word alloc_next = GET_ALLOC(HDRP(next_pp));
	word alloc_prev = GET_ALLOC(HDRP(prev_pp));
	word size;
	same_boundaries(pp);
// previous and next block allocated	
	if (alloc_next && alloc_prev) {
		size = GET_SIZE(HDRP(pp));
//		PUT(HDRP(pp), PACK(size, 0));		
//		PUT(FTRP(pp), PACK(size, 0));
// Add the block to the start of list? - better to point at last free block?
		void * ptr = listp;
//		if (listp == NULL) {
			insert(NULL, pp, NULL);
			//printf("listp is NULL\n");
			return pp;
//		}
/*		void * prev = heapp;
		printf("SEARCHING %p\n", ptr);
		while (ptr != NULL) {
			printf("while low %p %p top %p\n", mem_heap_lo(), ptr, mem_heap_hi());
			if (prev < pp && pp < ptr) {
				insert(prev, pp, ptr);
				return pp;				
			}
			prev = ptr;
			printf("before assign\n");
			printf("valid block? hdr %d ftr %d", GET_ALLOC(HDRP(ptr)), GET_ALLOC(FTRP(ptr)));
			ptr = GETP(SUCC(ptr));
			printf("after assign\n");
		}
		printf("after while");
		if (prev < pp && pp < mem_heap_hi()) {
			insert(prev, pp, NULL);
			return pp;
		}
		printf("\n ERROR coalesce inserting to a list\n");
		//PUTP(PRED(pp), lastp);
		//PUTP(SUCC(pp), NULL);
		//PUTP(lastp, pp);
//		printf("COALESCE END");
		return pp; // or NULL??
*/	}

// previous allocated, next free
	if (!alloc_next	&& alloc_prev) {
		size = GET_SIZE(HDRP(pp)) + GET_SIZE(HDRP(next_pp));
//		PUTP(SUCC(pp), GETP(SUCC(next_pp)));
//		PUTP(PRED(pp), GETP(PRED(next_pp)));
		set_boundaries(pp, size, 0);
//		PUT(HDRP(pp), PACK(size, 0));// ne next_pp?? - opravdu ne? - proc??		
//		PUT(FTRP(pp), PACK(size, 0));
		printf("prev alloc, next free %p %p\n", prev_pp, next_pp);
		printf("next pred succ %p %p\n", PRED(next_pp), SUCC(next_pp));
		printf("next GETP-> pred succ %p %p\n", GETP(PRED(next_pp)), GETP(SUCC(next_pp)));
		
		same_boundaries(pp);
		insert(NULL, pp, NULL);
		//insert(GETP(PRED(next_pp)), pp, GETP(SUCC(next_pp)));
		return pp;
	}

// previous free, next allocated
	if (alloc_next && !alloc_prev) {
		size = GET_SIZE(HDRP(pp)) + GET_SIZE(HDRP(prev_pp));
		set_boundaries(prev_pp, size, 0);
//		PUT(FTRP(pp), PACK(size, 0));
//		PUT(HDRP(prev_pp), PACK(size, 0));
		//printf("prev free next alloc low %p %p top %p\n", mem_heap_lo(), GETP(SUCC(pp)), mem_heap_hi());
//		printf("COALESCE END");
		same_boundaries(prev_pp);
		insert(NULL, prev_pp, NULL);	
		return prev_pp;
	}

// previous and next block free
	size = GET_SIZE(HDRP(pp)) + GET_SIZE(HDRP(next_pp)) + GET_SIZE(HDRP(prev_pp));
	set_boundaries(prev_pp, size, 0);
	PUT(HDRP(prev_pp), PACK(size, 0));
	PUT(FTRP(next_pp), PACK(size, 0));
	printf("prev next free %p %p", prev_pp, next_pp); 
//		printf("COALESCE END");
	same_boundaries(prev_pp);
	insert(NULL, prev_pp, NULL);
	//insert(GETP(PRED(prev_pp)), prev_pp, GETP(SUCC(next_pp)));
	return prev_pp;

}


void * extend_heap(word words) {
	void * pp;
	word size;
	//printf("EXTENDHEAP START\n");	
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;	
	//size = ALIGN(size);
	pp = mem_sbrk(size);
//	printf("pp is %p", pp);
	if (pp == (void *)-1) {
		return NULL;
	}

	set_boundaries(pp, size, 0);
//	PUT(HDRP(pp), PACK(size, 0));
//	PUT(FTRP(pp), PACK(size, 0));
// new epilogue header
	PUT(HDRP(NEXT_PP(pp)), PACK(0, 1));
	
	pp = coalesce(pp);
	//printf("first free block %p\n", pp);
	if (listp == NULL) {
		listp = pp;
	}

//	if (start == NULL) {
//		start = pp;
//	}
	return pp;
}


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{	
printf("\nMM_INIT()\n");
//	printf("word sizeof %d\n", sizeof(word));
//	printf("ptr sizeof %d\n", sizeof(void *));
	
	heapp = mem_sbrk(4 * WSIZE);
	if (heapp == (void*)-1) {
		return -1;
	}

	PUT(heapp, 0);
	PUT((char *)heapp + WSIZE, PACK(DSIZE, 1));
	PUT((char *)heapp + 2 * WSIZE, PACK(DSIZE, 1));
	PUT((char *)heapp + 3 * WSIZE, PACK(0, 1));
	heapp =(char *)heapp +  2 * WSIZE;	
	//printf("heap low %p heapp %p\n", mem_heap_lo(), heapp);
	listp = extend_heap(CHUNKSIZE/WSIZE);
	start = listp;
	if (listp == NULL) {
		return -1;
	}		
    return 0;
}


void * find_place(word size) {
	//printf("find_place()\n");
	void * ptr = heapp;
	void * top = mem_heap_hi();
	while (ptr < top) {
		if (GOOD_FIT(ptr, size)) {
			return ptr;
		}
		ptr = NEXT_PP(ptr);
	}
	return NULL;
	
//	void * ptr = listp;
	while( ptr != NULL) {
		if (GOOD_FIT(ptr, size)) {
			return ptr;
		}
	ptr = GETP(SUCC(ptr));
	}	
	return NULL;
	/*void **/ ptr = start;	
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

void remove_block(void * prev, void * curr, void * next) {	
//	is_free(prev);
//	is_free(curr);
//	is_free(next);
	printf("remove_block() %p %p %p\n", prev, curr, next);	
	print_block(curr);
	if (prev != NULL && next != NULL && prev == next) {
		printf("CYCLE");
//		while (1) {;}
	}
	if (curr == next) {
		printf("curr == next\n", curr);
		while (1) {;}
	}
	if (prev == curr) {
		printf("prev == curr\n");
		while (1) {;}
	}
	
//	print_block(prev);
//	printf("aa");	
//	print_block(curr);
//	printf("aa");	
//	print_block(next);
//	printf("aa");	
	if (next != NULL) {
		PUTP(PRED(next), prev);
	}
	if (prev != NULL) {
		PUTP(SUCC(prev), next);
	}

// If the free block was first in the list
	if (listp == curr) {
		listp = next;
	}
// If the free block was the beg place of search
//	if (start == curr) {
//		if (next != NULL) {
//			start = next;
//		}
//		else { 	// can be NULL!!	
//			start = prev;
//		}
//	}
	printf("remove_block() END");
}
	
// check correct assign to pred  - min size must 
void place(void * pp, word size) {
	word block_size = GET_SIZE(HDRP(pp));
	printf("place()\n");	
	is_free(pp);
	//printf("alloc%d  prev%d\n", size, block_size);
	if (block_size - size >= MBLK_SIZE) {
		void * pp_new = (char *)pp + size;
		//insert(GETP(PRED(pp)), pp_new, GETP(SUCC(pp)));	
//	print_block(curr);
//	print_block(curr);
//	print_block(curr);
		PUT(HDRP(pp_new), PACK(block_size - size, 0));
		PUT(FTRP(pp_new), PACK(block_size - size, 0));
		if (listp == pp) {
			listp = pp_new;
		}
// free block is just smaller now
		PUT(HDRP(pp), PACK(size, 1));
		PUT(FTRP(pp), PACK(size, 1));
		//printf("footer of alloc %p, header of free %p\n", FTRP(pp), HDRP(pp_new));
		same_boundaries(pp);
		same_boundaries(pp_new);
	}
	else {	// free block is gone
//		remove_block(GETP(PRED(pp)), pp, GETP(SUCC(pp)));
		PUT(HDRP(pp), PACK(block_size, 1));
		PUT(FTRP(pp), PACK(block_size, 1));
		same_boundaries(pp);
	}
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{	
//	printf("malloc\n");
/**/
//	print_free_list();
	heap_checker();
	word asize;
	void * pp;

	if (size == 0) {
		printf("\nsize = 0 weird\n");
		return NULL;
	}

	if (ALIGN(size + DSIZE) <  MBLK_SIZE) {
		asize = MBLK_SIZE;
	}	
	else {
		asize = ALIGN(size + DSIZE);
		//asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
	}

	
// Try to find place in list
	pp = find_place(asize);
// Create allocated block
	if (pp != NULL) {
		place(pp, asize);
		return pp;
	}
	asize = MAX(asize, CHUNKSIZE);

	pp = extend_heap(asize/WSIZE);
	if (pp == NULL) {
		printf("\n should not happen\n");		
		return NULL;
	}
	
// Create allocated block
	place(pp, asize);
	return pp;	
/**/
/*/

    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
/**/
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
	printf("free()\n");
	word size = GET_SIZE(HDRP(ptr));
	PUTP(SUCC(ptr), NULL);
	PUTP(PRED(ptr), NULL);
	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));
	print_block(ptr);
	coalesce(ptr);
//	heap_checker();
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














