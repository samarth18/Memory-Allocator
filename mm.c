/* 
 * Simple, 32-bit and 64-bit clean allocator based on an segregated free list,
 * best fit placement, and boundary tag coalescing. Blocks are aligned to 
 * double-word boundaries.  This yields 8-byte aligned blocks on a 32-bit 
 * processor, and 16-byte aligned blocks on a 64-bit processor.  However, 
 * 16-byte alignment is stricter than necessary; the assignment only requires
 * 8-byte alignment.  The minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Project 2",
	/* First member's full name */
	"Samarth Parikh",
	/* First member's email address */
	"201401244@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"Saurabh Shah",
	/* Second member's email address (leave blank if none) */
	"201401245@daiict.ac.in"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given a block ptr bp, read the explicit list next and previous blocks */
#define SEG_NEXT_BLKP(bp) GET(bp)
#define SEG_PREV_BLKP(bp) GET((char *)(bp)+WSIZE)

/* Given a block ptr bp, write the explicit list next and previous blocks */
#define SEG_SET_NEXT_BLKP(bp, next_block_ptr) PUT(bp, next_block_ptr)
#define SEG_SET_PREV_BLKP(bp, prev_block_ptr) PUT((char *)(bp)+WSIZE, prev_block_ptr) 


/* Global variables: */
static char *heap_listp;          /* Pointer to first block */  
size_t segregated_lists = 10;     /* segregated explicit free list split into 10 different sizes */
static char ** list_ptr;          

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static int list_index(size_t size);
static void remove_list (void *bp);
static void add_list (void *bp);
static void *main_coalesce(void *bp);
static void *find_fit(size_t asize);
static void *extend_heap(size_t words);
static void place(void* bp, size_t asize, bool extend);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void checkfreeblock(void *bp);
static void printblock(void *bp); 

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{
        int i;

        /* Create the initial heap space for list_ptr */
        if ((list_ptr = mem_sbrk(segregated_lists * WSIZE)) == (void *)-1)
		return (-1);

        /* Create the initial empty heap. */ 
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return (-1);

	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header  */
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer  */
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);
        
        for (i = 0; i < segregated_lists; i++)
                list_ptr[i] = NULL;                    /* initialize our free list pointer for each of the block sizes. */

	return (0); 
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize, false);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize, true);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
        main_coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}
        
        /* If the size fits within the current pointer's block then use the same block. */
        size_t curSize = GET_SIZE(HDRP(ptr));
        if (size < curSize-2*WSIZE) {
        	return ptr;
        } 

        void *next = NEXT_BLKP(ptr);
        int next_alloc = GET_ALLOC(HDRP(next));

        size_t coalesce_size = (GET_SIZE(HDRP(next)) + GET_SIZE(HDRP(ptr)));
        if (!next_alloc && size <= coalesce_size-2*WSIZE){        /* check if we can coalesce on the right. */ 
        	remove_list(next);
                PUT(HDRP(ptr), PACK(coalesce_size, 1));
                PUT(FTRP(ptr), PACK(coalesce_size, 1));
                return ptr;
        } 

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
                return (mm_malloc(size));

	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if (newptr == NULL)
		return (NULL);

	/* Copy the old data. */
	oldsize = GET_SIZE(HDRP(ptr));
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return (newptr); 
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {                 /* Case 1 */
		return (bp);
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	} else {                                        /* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   According to the corresponding size, returns the 
 *   segregated list array index.
 */
static int 
list_index(size_t size) {

    if (size > 16384)
        return 9;
    else if (size > 8192)
        return 8;
    else if (size > 4096)
        return 7;
    else if (size > 2048)
        return 6;
    else if (size > 1024)
        return 5;
    else if (size > 512)
        return 4;
    else if (size > 256)
        return 3;
    else if (size > 128)
        return 2;
    else if (size > 64)
        return 1;
    else
        return 0;

}

/*
 * Requires:
 *   "bp" is the address of a newly allocated block.
 *
 * Effects:
 *   Removes this block from the segregated free list.
 */
static void 
remove_list (void *bp){
    int index = list_index(GET_SIZE(HDRP(bp))); /* use size of block to determine which list. */

    if (SEG_PREV_BLKP(bp) != NULL)              /* check if the previous block is null and set accordingly. */ 
            SEG_SET_NEXT_BLKP(SEG_PREV_BLKP(bp),SEG_NEXT_BLKP(bp));
    else 
            list_ptr[index] = SEG_NEXT_BLKP(bp); 

    if (SEG_NEXT_BLKP(bp) != NULL)              /* check if the next block is null and set accordingly. */
            SEG_SET_PREV_BLKP(SEG_NEXT_BLKP(bp), SEG_PREV_BLKP(bp));
    return;
}

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Adds block pointer bp to the appropriate segregated free list.
 */
static void add_list (void *bp){
    int index = list_index(GET_SIZE(HDRP(bp)));  /* use size of block to determine which list. */
    SEG_SET_NEXT_BLKP(bp, list_ptr[index]);      /* place the new block at the start of the list. */   
    SEG_SET_PREV_BLKP(bp, NULL); 

    if (list_ptr[index] != NULL)                 /* check if the first block is null. */
            SEG_SET_PREV_BLKP(list_ptr[index], bp);	 
    list_ptr[index] = bp; 
    return; 
}

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Performs coalescing as per LIFO principle and calls coalesce as necessary.
 */
static void *
main_coalesce(void *bp) {

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    
    if (prev_alloc && next_alloc) {         /* case 1 */
            add_list(bp);
    } 

    if (prev_alloc && !next_alloc) {        /* case 2 */
            void *next = NEXT_BLKP(bp); 
            remove_list(next);
            bp = coalesce(bp);
            add_list(bp); 
    }

    if (!prev_alloc && next_alloc) {        /* case 3 */
            void *prev = PREV_BLKP(bp);
            remove_list(prev);
            bp = coalesce(bp);
            add_list(bp);
    }

    if (!prev_alloc && !next_alloc) {       /* case 4 */
            void *prev = PREV_BLKP(bp);
            void *next = NEXT_BLKP(bp);
            remove_list(prev);
            remove_list(next);
            bp = coalesce(bp);
            add_list(bp);
    }
    return bp;

}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */

static void *
find_fit(size_t asize) {

    size_t lowest_diff = 9999999;
    void *bestSoFar = NULL;

    int index = list_index(asize);
    int i;
   for (i = index; i < segregated_lists; i++) {          /* Traverse for block size equal to asize to all larger blocks. */
           void *bp = list_ptr[i];                      /* search from the beginning in a list */
           while (bp) {                                 /* traverse through the linked list */
                   size_t curr_block_size = GET_SIZE(HDRP(bp));
                   if (!GET_ALLOC(HDRP(bp)) && (asize <= curr_block_size)) { 
                           size_t diff = curr_block_size;
                           if (diff < lowest_diff) { 
                                   lowest_diff = diff;
                                   bestSoFar = bp; 
                            }

                    }
           bp  = SEG_NEXT_BLKP(bp);
           }

           if(bestSoFar!= NULL)
           return bestSoFar;
    }

    /* No fit was found. */
    return bestSoFar; 
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	return (bp);
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *   "extend" to check if the call to place is done when the heap is extended or not.
 *
 * Effects:
 *   Place a block of "asize" bytes in our explicit free list and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */

static void 
place(void* bp, size_t asize, bool extend)
{
    /* Get the current block size */
    size_t bsize = GET_SIZE(HDRP(bp));

    if (extend == true) {
            if ((bsize - asize) >= (2 * DSIZE)){
                    PUT(HDRP(bp), PACK(asize, 1));
                    PUT(FTRP(bp), PACK(asize, 1));
            	    size_t excess_size = bsize - asize;
                    void *new_spliced = NEXT_BLKP(bp);
                    PUT(HDRP(new_spliced), PACK(excess_size, 0));
                    PUT(FTRP(new_spliced), PACK(excess_size, 0)); 
                    add_list(new_spliced);
            }
            else {
                    PUT(HDRP(bp), PACK(bsize, 1));
                    PUT(FTRP(bp), PACK(bsize, 1));
	    } 
    }
    else { 

            if ((bsize - asize) >= (2 * DSIZE)) {
                    /* removing from the list is necessary in this case. */
	            remove_list(bp);
                    PUT(HDRP(bp), PACK(asize, 1));
                    PUT(FTRP(bp), PACK(asize, 1));
                    size_t excess_size = bsize - asize;
                    void *new_spliced = NEXT_BLKP(bp);

                    PUT(HDRP(new_spliced), PACK(excess_size, 0));
                    PUT(FTRP(new_spliced), PACK(excess_size, 0)); 
                    add_list(new_spliced);
            }
	    else {
                    PUT(HDRP(bp), PACK(bsize, 1));
                    PUT(FTRP(bp), PACK(bsize, 1));
                     /* removing from the list is necessary in this case. */
                    remove_list(bp);
            }
    }
}

/*
 * The remaining routines are heap consistency checker routines.
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp)
{
	size_t alloc, prev_alloc, next_alloc;
	alloc = GET_ALLOC(HDRP(bp));
	prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

	if ((uintptr_t)bp % DSIZE)                          /* checks if the block is double word aligned*/
		printf("Error: %p must be doubleword aligned\n", bp);

	if (GET(HDRP(bp)) != GET(FTRP(bp)))                 /* checks if header matches footer*/
		printf("Error: header does not match footer\n");

	if((!alloc) && !(prev_alloc & next_alloc)){         /* checks if contiguous free blocks escaped coalescing*/
		printf("%p consecutive free blocks\n", bp);
		exit(-1);
	}
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency.
 */

void
checkheap(bool verbose)
{
	void *bp;
	int numfreeblocks_heap = 0;
	int numfreeblocks_list = 0;
	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE || !GET_ALLOC(HDRP(heap_listp))) /*checks Prologue header*/
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {      /*checks each block */
		if (verbose)
			printblock(bp);
		checkblock(bp);
		if(!GET_ALLOC(HDRP(bp)))                                         /* counts the total number of free blocks in the heap */
			numfreeblocks_heap++;
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))                     /* checks epilogue header */
		printf("Bad epilogue header\n");

	/* Free list checking */
	int i = 0;
	for(i = 0; i < segregated_lists; i++)
	{
		if(list_ptr[i]!=NULL){
			for(bp = list_ptr[i]; bp!=NULL && GET_ALLOC(HDRP(bp)) == 0; bp = SEG_NEXT_BLKP(bp))
			{
				checkfreeblock(bp);
				numfreeblocks_list++;
			}
		}
	}

	/* Check if number of free blocks in the heap and segregated list match */
	if(numfreeblocks_list != numfreeblocks_heap)
	{
		printf("Mismatch between free blocks in heap and free list\n");
		exit(-1);
	}
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the free block "bp".
 */
static void
checkfreeblock(void *bp)
{
 /*Checks if the pointers in the free list point to valid free blocks*/

	if(SEG_PREV_BLKP(bp))   /* for a previous block */
	{
		if(SEG_NEXT_BLKP(SEG_PREV_BLKP(bp)) != bp)  /*the next of previous block should point to the current block*/
		{
			printf("Free list inconsistent at %p\n", bp);
			exit(-1);
		}
	}

	if(SEG_NEXT_BLKP(bp) && SEG_NEXT_BLKP(bp) != heap_listp)
	{
		if(SEG_PREV_BLKP(SEG_NEXT_BLKP(bp)) != bp)  /*the previous of next block should point to the current block*/
		{
			printf("Free list inconsistent at %p\n", bp);
			exit(-1);
		}
	}

}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp)
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp,
	    hsize, (halloc ? 'a' : 'f'),
	    fsize, (falloc ? 'a' : 'f'));
}

/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */

