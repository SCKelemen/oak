// Oak: http_count, projected from the Http literals declaration in literals.oak
// (run.sh emits literals.c with `oak build -emit-c`). Build: see run.sh
#define main oak_program_main
#include "literals.c"
#undef main
#include "timing.h"
int main(void) {
    uint64_t n; uint8_t *buf = read_input(&n);
    oak_view_u8 text; text.base = buf; text.len = (u32)n;
    double best = 1e30; u32 count = 0;
    for (int r = 0; r < 5; r++) {
        double t0 = now_ns(); count = oak_http_count(text); double t = now_ns() - t0; if (t < best) best = t;
    }
    REPORT("Oak Http: literals (declaration)", best, n);
    printf("   matches %u\n", count);
    return 0;
}
