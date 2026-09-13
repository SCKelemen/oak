// Oak: count_literals as emitted by the C backend from literals.oak
// (run.sh emits literals.c with `oak build -emit-c`). Build: see run.sh
#define main oak_program_main
#include "literals.c"
#undef main
#include "timing.h"
int main(void) {
    uint64_t n; uint8_t *buf = read_input(&n);
    oak_view_u8 text; text.base = buf; text.len = (u32)n;
    oak_view_u8 patterns; patterns.base = http_patterns.v; patterns.len = 136;
    oak_view_u32 starts; starts.base = http_starts.v; starts.len = 17;
    static u8 tables[96]; oak_span_u8 tspan; tspan.base = tables; tspan.len = 96;
    oak_build_tables(patterns, starts, 16u, tspan);
    oak_view_u8 tview; tview.base = tables; tview.len = 96;
    double best = 1e30; u32 count = 0;
    for (int r = 0; r < 5; r++) {
        double t0 = now_ns(); count = oak_count_literals(text, patterns, starts, 16u, tview); double t = now_ns() - t0; if (t < best) best = t;
    }
    REPORT("Oak count_literals (Teddy, Oak source)", best, n);
    printf("   matches %u\n", count);
    return 0;
}
