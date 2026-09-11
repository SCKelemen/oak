// Reference host clocks for the Oak `timenative` package (stdlib/timenative.oak).
// Link this file into a program that imports timenative, or provide the two
// symbols yourself: a hypervisor reads its counter, a test harness returns
// whatever its scenario dictates. POSIX.1-2001 clock_gettime; macOS 10.12+.
// The feature-test macro exposes clock_gettime and the CLOCK_* identifiers
// under a strict -std=c99 compile on glibc, where <time.h> otherwise hides them.
#define _POSIX_C_SOURCE 200112L
#include <stdint.h>
#include <time.h>

int64_t oak_time_host_wall_nanos(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_REALTIME, &ts) != 0) {
        return 0;
    }
    return (int64_t)ts.tv_sec * 1000000000LL + (int64_t)ts.tv_nsec;
}

uint64_t oak_time_host_monotonic_nanos(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) {
        return 0;
    }
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}
