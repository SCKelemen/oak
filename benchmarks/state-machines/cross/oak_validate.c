// Oak: the protocol-declared machine (utf8_run) and the language's own
// is_valid_utf8 builtin, both as emitted by the C backend into
// ../utf8_protocol.c. Build: cc -std=c11 -O2 -o oak_validate oak_validate.c
#define main oak_program_main
#include "../utf8_protocol.c"
#undef main
#include "timing.h"
int main(void) {
    uint64_t n; uint8_t *buf = read_input(&n);
    oak_view_u8 view; view.base = buf; view.len = n;
    double best_run = 1e30, best_builtin = 1e30; int ok_run = 0, ok_builtin = 0;
    for (int r = 0; r < 5; r++) {
        double t0 = now_ns(); oak_Utf8State s = oak_utf8_run(oak_utf8_initial(), view); double t = now_ns() - t0;
        if (t < best_run) best_run = t; ok_run = s.tag == oak_Utf8State_tag_Accept;
        t0 = now_ns(); Bool v = oak_is_valid_utf8(view); t = now_ns() - t0;
        if (t < best_builtin) best_builtin = t; ok_builtin = v == oak_Bool_True;
    }
    REPORT("Oak protocol utf8_run (shift DFA)", best_run, n);
    REPORT("Oak builtin is_valid_utf8 (scalar)", best_builtin, n);
    if (!ok_run || !ok_builtin) { printf("MISMATCH: input judged invalid\n"); return 1; }
    return 0;
}
