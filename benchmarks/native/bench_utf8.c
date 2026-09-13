// Times the UTF-8 validator emitted by one backend over an input file:
// KERNEL_C names the emitted C (with or without the native companion
// object linked beside it), LABEL the row. Build: see run.sh.
#define main oak_program_main
#include KERNEL_C
#undef main
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
static double now_ns(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); if (!f) return 2;
    fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
    unsigned char *buf = malloc((size_t)n + 64); if (fread(buf, 1, (size_t)n, f) != (size_t)n) return 2; fclose(f);
    unsigned char tables[64];
    for (int i = 0; i < 16; i++) { tables[i] = table_high1.v[i]; tables[16 + i] = table_low1.v[i]; tables[32 + i] = table_high2.v[i]; tables[48 + i] = incomplete_max.v[i]; }
    oak_view_u8 text; text.base = buf; text.len = (u32)n;
    oak_view_u8 tv; tv.base = tables; tv.len = 64;
    double best = 1e30; Bool ok = 0;
    for (int r = 0; r < 5; r++) { double t0 = now_ns(); ok = oak_valid_with(text, tv); double t = now_ns() - t0; if (t < best) best = t; }
    printf("%-28s %6.2f ns/byte  %6.2f GB/s  valid=%d\n", LABEL, best / n, n / best, ok == oak_Bool_True);
    return 0;
}
