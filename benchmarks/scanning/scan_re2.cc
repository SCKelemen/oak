// RE2: the literal set as one alternation, every leftmost match consumed in
// turn (RE2 has no per-occurrence multi-pattern API; RE2::Set reports which
// patterns matched, not where). Build: see run.sh
#include <re2/re2.h>
#include <string>
#include <cstring>
extern "C" {
#include "timing.h"
}
#include "literals.h"
int main() {
    uint64_t n; uint8_t *buf = read_input(&n);
    std::string alt;
    for (unsigned i = 0; i < NLITERALS; i++) { if (i) alt += "|"; alt += RE2::QuoteMeta(LITERALS[i]); }
    RE2 re(alt);
    if (!re.ok()) { fprintf(stderr, "re2: %s\n", re.error().c_str()); return 2; }
    double best = 1e30; uint64_t count = 0;
    for (int r = 0; r < 5; r++) {
        uint64_t c = 0; absl::string_view text((const char *)buf, (size_t)n);
        double t0 = now_ns();
        while (RE2::FindAndConsume(&text, re)) c++;
        double t = now_ns() - t0; if (t < best) best = t; count = c;
    }
    REPORT("RE2 alternation, FindAndConsume", best, n);
    printf("   matches %llu\n", (unsigned long long)count);
    free(buf);
    return 0;
}
