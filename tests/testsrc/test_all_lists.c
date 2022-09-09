#include <stdlib.h>

#include "testing.h"

int main() {
  initialize_test(__FILE__);

  mallocing(1, print_status, false);
  for (int i = 1; i <= N_LISTS; i++) {
    size_t s = 8 * (i + 1);

    void * ptr = mallocing(s, print_status, false); 
    // Malloc a gap in the freelist
//if(i==56){
// i=56;
//}
    mallocing(s + 8, print_status, false);
//if(i == 56){
//tags_print(print_object);
//}
    freeing(ptr, s, print_status, false);
//tags_print(print_object);  
}

  finalize_test();
}
