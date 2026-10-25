/* Native oracle: run the exact example routines and print a0..a2 and a 96-byte buffer.
   Input lines: <routine> <4 args> <96 buffer bytes>; an arg "p<offset>" is a pointer into the
   buffer. Results come from an inline jalr so non-ABI outputs (add128's carry in a2) survive. */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef ROUTINES /* the C corpus check supplies its own list with -include */
#define ROUTINES X(inc64) X(umax64) X(count64) X(scan64) X(add128) X(addmem) X(fill64) \
  X(stack32) X(reserve256) X(alias64) X(stack64) X(shift64) X(probe_stack32)
#endif
#define X(name) extern char name[];
ROUTINES
#undef X

int main(void) {
  char name[32], arg[4][32];
  unsigned char buf[96];
  while (scanf("%31s %31s %31s %31s %31s", name, arg[0], arg[1], arg[2], arg[3]) == 5) {
    for (int i = 0; i < 96; ++i) {
      unsigned v;
      if (scanf("%u", &v) != 1) return 2;
      buf[i] = (unsigned char)v;
    }
    void *fn = NULL;
#define X(n) if (!strcmp(name, #n)) fn = n;
    ROUTINES
#undef X
    if (!fn) return 2;
    uint64_t v[4];
    for (int i = 0; i < 4; ++i)
      v[i] = arg[i][0] == 'p' ? (uint64_t)(uintptr_t)(buf + strtoull(arg[i] + 1, NULL, 0))
                              : strtoull(arg[i], NULL, 0);
    register uint64_t a0 __asm__("a0") = v[0], a1 __asm__("a1") = v[1];
    register uint64_t a2 __asm__("a2") = v[2], a3 __asm__("a3") = v[3];
    __asm__ volatile("jalr ra, 0(%[fn])"
                     : "+r"(a0), "+r"(a1), "+r"(a2), "+r"(a3)
                     : [fn] "r"(fn)
                     : "ra", "t0", "t1", "t2", "t3", "t4", "t5", "t6", "a4", "a5", "a6", "a7",
                       "memory");
    /* Pointers into (or just past) the buffer are printed relative to it, as the model does. */
    uint64_t out[3] = {a0, a1, a2}, base = (uint64_t)(uintptr_t)buf;
    for (int i = 0; i < 3; ++i) {
      if (out[i] - base <= 1024) printf(i ? " p%" PRIu64 : "p%" PRIu64, out[i] - base);
      else printf(i ? " %" PRIu64 : "%" PRIu64, out[i]);
    }
    for (int i = 0; i < 96; ++i) printf(" %u", buf[i]);
    printf("\n");
  }
  return 0;
}
