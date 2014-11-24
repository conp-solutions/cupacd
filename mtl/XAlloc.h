/****************************************************************************************[XAlloc.h]
Copyright (c) 2009-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/


#ifndef Minisat_XAlloc_h
#define Minisat_XAlloc_h

#include <errno.h>
#include <stdlib.h>

#include <sys/mman.h> // use a specialized malloc/free pair that is based on mmap and munmap to use HUGE_PAGES
#include <cstring>    // for memcpy

namespace Minisat {

//=================================================================================================
// Simple layer on top of malloc/realloc to catch out-of-memory situtaions and provide some typing:

class OutOfMemoryException{};
static inline void* xrealloc(void *ptr, size_t size)
{
    void* mem = realloc(ptr, size);
    if (mem == NULL && errno == ENOMEM){
        throw OutOfMemoryException();
    }else
        return mem;
}

#if 0
/** free memory that has been allocated with @see mmrealloc
 */
static inline void mmfree(void* ptr, size_t size)
{
  munmap(ptr, size); // use munmap instead of free
  ptr = 0;
}

/** alloc (or realloc) memory with the mmap command instead of malloc
 */
static inline void* mmrealloc(void *ptr, size_t newsize, size_t oldsize)
{
    void* mem ;
    if( ptr != 0 ) {
      mem = mmap(0, newsize, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS  | MAP_HUGETLB , -1, 0);
      if( MAP_FAILED == mem ) throw OutOfMemoryException(); // check whether allocation failed
    } else {
      mem = mmap(0, newsize, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS  | MAP_HUGETLB , -1, 0);
      if( MAP_FAILED == mem ) throw OutOfMemoryException(); // check whether allocation failed
      memcpy( mem, ptr, oldsize);                           // copy old content into new memory
      mmfree( ptr, oldsize );                                        // free old memory
    }
    return mem;
}

#endif

//=================================================================================================
}

#endif
