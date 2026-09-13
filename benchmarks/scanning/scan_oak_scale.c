// Oak: big64_count and big256_count, projected from the declarations in
// scale_oak.oak (run.sh emits scale_oak.c), timed on the shared input.
#define main oak_program_main
#include "scale_oak.c"
#undef main
#include "timing.h"
int main(void) {
    uint64_t n; uint8_t *buf = read_input(&n);
    oak_view_u8 text; text.base = buf; text.len = (u32)n;
    double b64 = 1e30, b256 = 1e30; u32 c64 = 0, c256 = 0;
    for (int r = 0; r < 5; r++) {
        double t0 = now_ns(); c64 = oak_big64_count(text); double t = now_ns() - t0; if (t < b64) b64 = t;
        t0 = now_ns(); c256 = oak_big256_count(text); t = now_ns() - t0; if (t < b256) b256 = t;
    }
    REPORT("Oak Big64: literals (4 groups)", b64, n);
    printf("   matches %u\n", c64);
    REPORT("Oak Big256: literals (16 groups)", b256, n);
    printf("   matches %u\n", c256);
    return 0;
}
