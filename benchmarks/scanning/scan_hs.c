// Vectorscan: the literal set compiled with hs_compile_lit_multi, block
// mode, every occurrence reported. Build: see run.sh
#include <hs/hs.h>
#include <string.h>
#include "timing.h"
#include "literals.h"
static int on_match(unsigned id, unsigned long long from, unsigned long long to, unsigned flags, void *ctx) {
    (void)id; (void)from; (void)to; (void)flags; (*(uint64_t *)ctx)++; return 0;
}
int main(void) {
    uint64_t n; uint8_t *buf = read_input(&n);
    unsigned flags[NLITERALS], ids[NLITERALS]; size_t lens[NLITERALS];
    for (unsigned i = 0; i < NLITERALS; i++) { flags[i] = 0; ids[i] = i; lens[i] = strlen(LITERALS[i]); }
    hs_database_t *db = NULL; hs_compile_error_t *err = NULL;
    if (hs_compile_lit_multi(LITERALS, flags, ids, lens, NLITERALS, HS_MODE_BLOCK, NULL, &db, &err) != HS_SUCCESS) {
        fprintf(stderr, "hs_compile_lit_multi: %s\n", err ? err->message : "?"); return 2;
    }
    hs_scratch_t *scratch = NULL;
    if (hs_alloc_scratch(db, &scratch) != HS_SUCCESS) { fprintf(stderr, "hs_alloc_scratch failed\n"); return 2; }
    double best = 1e30; uint64_t count = 0;
    for (int r = 0; r < 5; r++) {
        uint64_t c = 0; double t0 = now_ns();
        if (hs_scan(db, (const char *)buf, (unsigned)n, 0, scratch, on_match, &c) != HS_SUCCESS) { fprintf(stderr, "hs_scan failed\n"); return 2; }
        double t = now_ns() - t0; if (t < best) best = t; count = c;
    }
    REPORT("Vectorscan hs_scan, literal db", best, n);
    printf("   matches %llu\n", (unsigned long long)count);
    hs_free_scratch(scratch); hs_free_database(db); free(buf);
    return 0;
}
