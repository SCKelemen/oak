#include <dlfcn.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef struct { const uint8_t *base; uint32_t len; } View;
typedef struct { uint8_t *base; uint32_t len; } Span;
typedef enum { OakFalse = 0, OakTrue = 1 } OakBool;
typedef OakBool (*Hash)(View, Span);

static double now_ns(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) { perror("clock_gettime"); exit(2); }
    return (double)ts.tv_sec * 1e9 + ts.tv_nsec;
}

static int number(const char *s, int limit) {
    char *end;
    errno = 0;
    long n = strtol(s, &end, 10);
    if (errno || *s == 0 || *end || n < 1 || n > limit) {
        fprintf(stderr, "invalid count: %s\n", s); exit(2);
    }
    return (int)n;
}

static void digest(Hash fn, const uint8_t *input, uint32_t size, uint8_t out[32]) {
    memset(out, 0xa5, 32);
    if (fn((View){input, size}, (Span){out, 32}) != OakTrue) {
        fprintf(stderr, "hash call failed\n"); exit(2);
    }
}

int main(int argc, char **argv) {
    if (argc != 6) { fprintf(stderr, "usage: same_process BEFORE_DYLIB AFTER_DYLIB C_DYLIB ROUNDS SAMPLES\n"); return 2; }
    int rounds = number(argv[4], 1000), samples = number(argv[5], 201);
    void *handles[3], *compress[2];
    Hash hash[3];
    for (int i = 0; i < 3; i++) {
        if (argv[i + 1][0] != '/') { fprintf(stderr, "library path must be absolute\n"); return 2; }
        handles[i] = dlopen(argv[i + 1], RTLD_NOW | RTLD_LOCAL);
        if (!handles[i]) { fprintf(stderr, "%s\n", dlerror()); return 2; }
        dlerror();
        hash[i] = (Hash)dlsym(handles[i], "oak_bench_blake3");
        const char *error = dlerror();
        if (error || !hash[i]) { fprintf(stderr, "missing hash entry: %s\n", error ? error : "null"); return 2; }
        if (i < 2) {
            compress[i] = dlsym(handles[i], "oak_hash__blake3_ucompress");
            if (!compress[i]) { fprintf(stderr, "missing native compressor\n"); return 2; }
        }
    }
    if (compress[0] == compress[1] || hash[0] == hash[1] || hash[0] == hash[2] || hash[1] == hash[2]) {
        fprintf(stderr, "variants share an entry point\n"); return 2;
    }
    const uint32_t size = 1u << 20;
    uint8_t *input = malloc(size);
    double *times = calloc((size_t)samples * 3, sizeof(double));
    if (!input || !times) { fprintf(stderr, "allocation failed\n"); return 2; }
    uint64_t rng = UINT64_C(0x9e3779b97f4a7c15);
    for (uint32_t i = 0; i < size; i++) {
        rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
        input[i] = (uint8_t)rng;
    }
    const uint32_t boundaries[] = {0,1,63,64,65,1023,1024,1025,2048,2049,3072,4096,5000,size};
    uint8_t expected[32], out[32];
    for (size_t k = 0; k < sizeof(boundaries)/sizeof(boundaries[0]); k++) {
        digest(hash[2], input, boundaries[k], expected);
        for (int i = 0; i < 2; i++) {
            digest(hash[i], input, boundaries[k], out);
            if (memcmp(out, expected, 32)) { fprintf(stderr, "boundary mismatch: %u, variant %d\n", boundaries[k], i); return 1; }
        }
    }
    for (int i = 0; i < 3; i++) digest(hash[i], input, size, out);
    for (int s = 0; s < samples; s++) {
        for (int step = 0; step < 3; step++) {
            int i = (s + step) % 3;
            double start = now_ns();
            for (int r = 0; r < rounds; r++) digest(hash[i], input, size, out);
            times[(size_t)i * samples + s] = (now_ns() - start) / rounds;
            if (memcmp(out, expected, 32)) { fprintf(stderr, "sample mismatch: %d, variant %d\n", s, i); return 1; }
        }
    }
    printf("{\"schema\":\"oak-same-process-blake3-v1\",\"size\":%u,\"rounds\":%d,\"samples\":%d,\"checksum\":\"", size, rounds, samples);
    for (int i = 0; i < 32; i++) printf("%02x", expected[i]);
    printf("\",\"protocol\":\"one thread, rotating interleaved variants, one warmup each, distinct locally loaded libraries; affinity uncontrolled\",\"results\":[");
    const char *names[] = {"before", "after", "c-control"};
    for (int i = 0; i < 3; i++) {
        printf("%s{\"impl\":\"%s\",\"samples\":[", i ? "," : "", names[i]);
        for (int s = 0; s < samples; s++) printf("%s%.1f", s ? "," : "", times[(size_t)i * samples + s]);
        printf("]}");
    }
    printf("]}\n");
    free(times); free(input);
    for (int i = 0; i < 3; i++) dlclose(handles[i]);
    return 0;
}
