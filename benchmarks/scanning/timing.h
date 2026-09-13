#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
static double now_ns(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec; }
static uint8_t *read_input(uint64_t *len) {
    FILE *f = fopen("input.bin", "rb"); if (!f) { fprintf(stderr, "run gen_input first\n"); exit(2); }
    fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
    uint8_t *buf = (uint8_t *)malloc((size_t)n + 64); if (fread(buf, 1, (size_t)n, f) != (size_t)n) exit(2); fclose(f);
    *len = (uint64_t)n; return buf;
}
#define REPORT(label, best, n) printf("%-34s %6.2f ns/byte  %6.2f GB/s\n", label, (best) / (double)(n), (double)(n) / (best))
