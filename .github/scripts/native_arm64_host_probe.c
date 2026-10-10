/* Check the runtime ISA, not just the runner label or the compiler target.
 * Native tests use scalar FP/FMA and NEON. CRC is necessary for the dispatch
 * claim test, and SHA2 keeps the hash hardware realization available.
 * SVE/SME and Apple frameworks are deliberately not claimed by this lane.
 */
#if !defined(__aarch64__) || !defined(__linux__)
#error This probe must execute natively on Linux ARM64
#endif
#include <asm/hwcap.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/auxv.h>

int main(void) {
    unsigned long have = getauxval(AT_HWCAP);
    unsigned long need = HWCAP_FP | HWCAP_ASIMD | HWCAP_CRC32 | HWCAP_SHA2;
    printf("ARM64 HWCAP: have=0x%lx required=0x%lx (FP, ASIMD, CRC32, SHA2)\n", have, need);
    if ((have & need) != need) {
        fprintf(stderr, "required native ARM64 ISA features unavailable\n");
        return 1;
    }
    float a = 2.0f, b = 3.0f, c = 4.0f, fma;
    __asm__ volatile("fmadd %s0, %s1, %s2, %s3"
                     : "=w"(fma) : "w"(a), "w"(b), "w"(c));
    uint32_t neon, crc;
    __asm__ volatile("movi v0.4s, #1\nadd v0.4s, v0.4s, v0.4s\numov %w0, v0.s[0]"
                     : "=r"(neon) : : "v0");
    __asm__ volatile(".arch_extension crc\ncrc32cw %w0, %w1, %w2"
                     : "=r"(crc) : "r"(0u), "r"(0u));
    __asm__ volatile(".arch_extension crypto\nmovi v0.4s, #0\nsha256su0 v0.4s, v0.4s"
                     : : : "v0");
    if (fma != 10.0f || neon != 2 || crc != 0) {
        fprintf(stderr, "native ARM64 ISA smoke result mismatch\n");
        return 1;
    }
    return 0;
}
