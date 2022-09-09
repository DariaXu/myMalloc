#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
inline static void assert(int e) {
	if (!e) {
		const char * msg = "Assertion Failed!\n";
		write(2, msg, strlen(msg));
		exit(1);
	}
}
#else
#include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
	return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
	if (numOsChunks < MAX_OS_CHUNKS) {
		osChunkList[numOsChunks++] = hdr;
	}
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
	// Convert to char * before performing operations
	char * mem = (char *) raw_mem;

	// Insert a fencepost at the left edge of the block
	header * leftFencePost = (header *) mem;
	initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

	// Insert a fencepost at the right edge of the block
	header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
	initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
	void * mem = sbrk(size);

	insert_fenceposts(mem, size);
	header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
	set_state(hdr, UNALLOCATED);
	set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
	hdr->left_size = ALLOC_HEADER_SIZE;
	return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {

	// TODO implement allocation
	if(raw_size == 0){
		header * p = NULL;
		return p;
	}
	// cast index
	int index ;
	int eight =sizeof(size_t);
	if (raw_size < 2*eight){
		index = 1;
	}else if (raw_size%eight == 0){
		index = raw_size/eight -1;
	}else{
		index = ((size_t)raw_size/eight);
	}

	// index is the last index 
	if (index >= N_LISTS -1){
		bool check = true;

		while(check){
			header * freelist = &freelistSentinels[N_LISTS-1];
			header * n = freelist->next;
			size_t s;
			bool c =false;
			// check any block large enough in the list
			if(n != freelist){
				s = get_size(n) -  ALLOC_HEADER_SIZE; 

				while(s < (index +1)*eight){
					n = n->next;
					s = get_size(n)- ALLOC_HEADER_SIZE;
					if (n == freelist){
						// no satify
						c =true;
						break;
					}    
				}
			}
			// need new chunk
			if(c || n == freelist){
				// new chunk
				header * block = allocate_chunk(ARENA_SIZE);
				header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
				insert_os_chunk(prevFencePost);

				//check chunk for adjacent 
				// adjacent
				header * prevF =get_header_from_offset(prevFencePost,-ALLOC_HEADER_SIZE);
				if (get_state(prevF)==FENCEPOST){
					size_t prevSize = prevF -> left_size;
					header * prevChunk =  get_header_from_offset(prevF,-prevSize); 
					//prev allocated
					if (get_state(prevChunk) == ALLOCATED){
						set_state(prevF,UNALLOCATED);
						set_size(prevF,ARENA_SIZE);
						prevF->left_size = get_size(prevChunk);
						// coalescing
						prevF -> next = freelist->next;
						prevF -> prev = freelist;
						freelist->next->prev = prevF;
						freelist->next = prevF;
						//change left size
						header * rightFP =get_header_from_offset(prevFencePost, get_size(block)+ALLOC_HEADER_SIZE);
						rightFP->left_size = ARENA_SIZE;
						numOsChunks--;
					}else{
						//unallocated
						size_t sz = get_size(prevChunk);
						set_size(prevChunk,sz+ARENA_SIZE);

						header * rightFP =get_header_from_offset(prevFencePost, get_size(block)+ALLOC_HEADER_SIZE);
						rightFP->left_size = ARENA_SIZE+sz;

						if((sz - ALLOC_HEADER_SIZE)< (N_LISTS) *eight){
							//remove
							prevChunk->prev->next = prevChunk->next;
							prevChunk->next->prev = prevChunk->prev;          
						}

						prevChunk -> next = freelist->next;
						prevChunk -> prev = freelist;
						freelist->next->prev = prevChunk;
						freelist->next = prevChunk;
						numOsChunks--;					
					}     
				}else{
					// not adjacent
					block -> next = freelist->next;
					block -> prev = freelist;
					freelist->next->prev = block;
					freelist->next = block;

				}

				continue;

			}else{
				if(s - (index+1)*eight < 2*eight){
					// block picked
					set_state(n, ALLOCATED);
					n->prev->next = n->next;
					n->next->prev = n->prev;
					return get_header_from_offset(n,ALLOC_HEADER_SIZE);
				}else{
					//spilt block in last free list
					size_t spilt = s - (index + 1)*eight-ALLOC_HEADER_SIZE;
					header * newHeader = get_header_from_offset(n,spilt + ALLOC_HEADER_SIZE);
					set_size(n,spilt + ALLOC_HEADER_SIZE);

					set_size(newHeader, (index + 1)*eight + ALLOC_HEADER_SIZE);
					set_state(newHeader,ALLOCATED);
					newHeader->left_size = spilt + ALLOC_HEADER_SIZE;

					header * checkFP = get_right_header(newHeader);
					checkFP-> left_size = get_size(newHeader);
					

					int newIndex = spilt/eight -1;
					if (newIndex < N_LISTS -1 ){
						// if need to remove and insert to new list
						n->prev->next = n->next;
						n->next->prev=n->prev;

						header * free = &freelistSentinels[newIndex];
						n-> next = free->next;
						n->prev = free ;
						free -> next->prev = n;
						free -> next = n;
					}

					return get_header_from_offset(newHeader,ALLOC_HEADER_SIZE);

				}
			}
		}
	}else{
		// not last index
		header * n;
		int currentIndex;
		bool check = true;
		while(check){
			bool c = true;
			for (int i = index; i < N_LISTS; i++){
				header * freelist = &freelistSentinels[i];
				if (freelist->next != freelist){
					if (i == index || get_size(freelist->next) - (index+1)*8 == 8 ){
						header * ne = freelist->next;
						set_state(ne, ALLOCATED);
						freelist->next = ne->next;
						freelist->next->prev = freelist;
						return get_header_from_offset(n,ALLOC_HEADER_SIZE);
					}else{
						c =false;
						n = freelist->next;
						currentIndex = i;
						break;   
					}
				}
			}

			if(c){
				header * freelist = &freelistSentinels[N_LISTS-1];

				// new chunk
				header * block = allocate_chunk(ARENA_SIZE);
				header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
				insert_os_chunk(prevFencePost);
				lastFencePost = get_header_from_offset(block, get_size(block));

				//check chunk for adjacent 
				// adjacent
				header * prevF =get_header_from_offset(prevFencePost,-ALLOC_HEADER_SIZE);
				if (get_state(prevF)==FENCEPOST){

					size_t prevSize = prevF -> left_size;
					header * prevChunk =  get_header_from_offset(prevF,-prevSize); 
					if (get_state(prevChunk) == ALLOCATED){
						set_state(prevFencePost,UNALLOCATED);
						set_state(prevF,UNALLOCATED);
						set_size(prevF,ARENA_SIZE);
						prevF->left_size = get_size(prevChunk);

						prevF -> next = freelist->next;
						prevF -> prev = freelist;
						freelist->next->prev = prevF;
						freelist->next = prevF;

						lastFencePost->left_size = ARENA_SIZE;
						numOsChunks--;

					}else{
						size_t sz = get_size(prevChunk);
						set_size(prevChunk,sz+ARENA_SIZE);

						header * rightFP =get_header_from_offset(prevFencePost, get_size(block)+ALLOC_HEADER_SIZE);
						rightFP->left_size = ARENA_SIZE+sz;

						if((sz - ALLOC_HEADER_SIZE)< (N_LISTS) *eight){
							//remove
							prevChunk->prev->next = prevChunk->next;
							prevChunk->next->prev = prevChunk->prev;          
						}

						prevChunk -> next = freelist->next;
						prevChunk -> prev = freelist;
						freelist->next->prev = prevChunk;
						freelist->next = prevChunk;
						numOsChunks--;
					}     
				}else{
					// not adjacent
					block -> next = freelist->next;
					block -> prev = freelist;
					freelist->next->prev = block;
					freelist->next = block;

				}

				continue;

			}else{
				check = false;
			}

		}
		//spilt block
		size_t spilt = get_size(n) - 2* ALLOC_HEADER_SIZE - (index + 1)*eight;
		header * newHeader = get_header_from_offset(n,spilt + ALLOC_HEADER_SIZE);
		set_size(n,spilt + ALLOC_HEADER_SIZE);

		set_size(newHeader, (index + 1)*eight+ALLOC_HEADER_SIZE);
		set_state(newHeader,ALLOCATED);
		newHeader->left_size = get_size(n);

		header * ri = get_right_header(newHeader);
		ri->left_size = get_size(newHeader);


		int newIndex = spilt/eight -1;
		if (newIndex >= N_LISTS -1) {
			newIndex = N_LISTS -1;
		}
		if (newIndex !=  currentIndex){
			n->prev->next = n->next;
			n->next->prev = n->prev;

			header * free = &freelistSentinels[newIndex];
			n-> next = free->next;
			n->prev = free ;

			free-> next->prev = n;
			free -> next = n;
		}

		return get_header_from_offset(newHeader,ALLOC_HEADER_SIZE); 
	}

	// (void) raw_size;
	//assert(false);
	// exit(1);
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
	return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
	// TODO implement deallocation
	(void) p;
	if(p != NULL){
		int eight = sizeof(size_t);
		header * current = ptr_to_header(p);
		if(get_state(current) == UNALLOCATED){
			const char * msg = "Double Free Detected\n";
			write(2, msg, strlen(msg));	
			assert(false);
			exit(1);
		}		
		set_state(current,UNALLOCATED);
		header * left = get_left_header(current);
		header * right = get_right_header(current);

		bool l = false;
		if (get_state(left) == UNALLOCATED){
			l = true;
		}
		bool r = false;
		if (get_state(right) == UNALLOCATED){
			r = true;
		}

		if(!r && !l){
			//both allocated
			int index = (get_size(current) - ALLOC_HEADER_SIZE)/eight -1;
			if(index >= N_LISTS -1){
index = N_LISTS -1;
}
			header * free = &freelistSentinels[index];
			current->next = free->next;
			current->prev = free;
			free->next->prev = current;
			free->next = current;
		}else if (r && l){
			//both unallocated
			size_t tempS = get_size(left) - ALLOC_HEADER_SIZE;
			set_size(left,get_size(left)+ get_size(current) + get_size(right));
			header * rightS = get_right_header(right);
			rightS->left_size = get_size(left);

			int i;
			if(tempS/eight -1 < N_LISTS -1){
				// not in last list
				i = (get_size(left) -ALLOC_HEADER_SIZE)/eight - 1;
				if (i >= N_LISTS -1){
					i = N_LISTS -1;
				}
				//remove
				left->prev->next = left ->next;
				left->next->prev=left->prev;
				right->prev->next = right ->next;
				right->next->prev=right->prev;
				//add
				header * free =&freelistSentinels[i];
				left->next = free->next;
				left->prev = free;
				free->next->prev = left;
				free->next = left;
			}else{
				//remove
				right->prev->next = right ->next;
				right->next->prev=right->prev;
			}

		}else if (!r && l){
			//left unallocate
			size_t tempS = get_size(left) - ALLOC_HEADER_SIZE;
			set_size(left,get_size(left)+ get_size(current));

			right->left_size = get_size(left);

			int i;
			if(tempS/eight -1 < N_LISTS -1){
				i = (get_size(left) - ALLOC_HEADER_SIZE)/eight - 1;
				if (i >= N_LISTS -1){
					i = N_LISTS -1;
				}
				//remove
				left->prev->next = left ->next;
				left->next->prev=left->prev;

				//add
				header * free =&freelistSentinels[i];
				left->next = free->next;
				left->prev = free;
				free->next->prev = left;
				free->next = left;

			}

		}else{
			//right unallocate
			size_t tempS = get_size(right) - ALLOC_HEADER_SIZE;
			set_size(current,get_size(right)+ get_size(current));

			header * rightS = get_right_header(right);
			rightS->left_size = get_size(current);

			int i;
			if(tempS/eight -1 < N_LISTS -1){
				i = (get_size(current) - ALLOC_HEADER_SIZE)/eight - 1;
				if (i >= N_LISTS -1){
					i = N_LISTS -1;
				}
				//add
				header * free =&freelistSentinels[i];
				current->next = free->next;
				current->prev = free;
				free->next->prev = current;
				free->next = current;

				//remove
				right->prev->next = right ->next;
				right->next->prev=right->prev;
			}else{
				//change header
				current->prev = right->prev;
				current->next =right->next;
				right->prev->next=current;
				right->next->prev = current;
			} 

		}
		//assert(false);
		//exit(1);

	}
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
	for (int i = 0; i < N_LISTS; i++) {
		header * freelist = &freelistSentinels[i];
		for (header * slow = freelist->next, * fast = freelist->next->next; 
				fast != freelist; 
				slow = slow->next, fast = fast->next->next) {
			if (slow == fast) {
				return slow;
			}
		}
	}
	return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
	for (int i = 0; i < N_LISTS; i++) {
		header * freelist = &freelistSentinels[i];
		for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
			if (cur->next->prev != cur || cur->prev->next != cur) {
				return cur;
			}
		}
	}
	return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
	header * cycle = detect_cycles();
	if (cycle != NULL) {
		fprintf(stderr, "Cycle Detected\n");
		print_sublist(print_object, cycle->next, cycle);
		return false;
	}

	header * invalid = verify_pointers();
	if (invalid != NULL) {
		fprintf(stderr, "Invalid pointers\n");
		print_object(invalid);
		return false;
	}

	return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}

	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}

	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
	for (size_t i = 0; i < numOsChunks; i++) {
		header * invalid = verify_chunk(osChunkList[i]);
		if (invalid != NULL) {
			return invalid;
		}
	}

	return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
	// Initialize mutex for thread safety
	pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
	// Manually set printf buffer so it won't call malloc when debugging the allocator
	setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

	// Allocate the first chunk from the OS
	header * block = allocate_chunk(ARENA_SIZE);

	header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
	insert_os_chunk(prevFencePost);

	lastFencePost = get_header_from_offset(block, get_size(block));

	// Set the base pointer to the beginning of the first fencepost in the first
	// chunk from the OS·
	base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

	// Initialize freelist sentinels
	for (int i = 0; i < N_LISTS; i++) {
		header * freelist = &freelistSentinels[i];
		freelist->next = freelist;
		freelist->prev = freelist;
	}

	// Insert first chunk into the free list
	header * freelist = &freelistSentinels[N_LISTS - 1];
	freelist->next = block;
	freelist->prev = block;
	block->next = freelist;
	block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
	pthread_mutex_lock(&mutex);
	header * hdr = allocate_object(size); 
	pthread_mutex_unlock(&mutex);
	return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
	return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
	void * mem = my_malloc(size);
	memcpy(mem, ptr, size);
	my_free(ptr);
	return mem; 
}

void my_free(void * p) {
	pthread_mutex_lock(&mutex);
	deallocate_object(p);
	pthread_mutex_unlock(&mutex);
}

bool verify() {
	return verify_freelist() && verify_tags();
}
