package asm

import (
	"bufio"
	"bytes"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"testing"
)

// The native encoder is checked against the host LLVM assembler
// (docs/spec/94-assembler.md §9): every instruction text is encoded by both
// and the words must agree. Two sources of instructions: a hand-written
// set covering the checker's idioms, and a seeded fuzz that instantiates
// every template reading of the generated table with random operands — so
// the oracle is exercised on the exact surface Arm's XML defines. The
// tests skip without llvm-mc.

var llvmEncodingLine = regexp.MustCompile(`encoding: \[(0x[0-9a-f]{2}),(0x[0-9a-f]{2}),(0x[0-9a-f]{2}),(0x[0-9a-f]{2})\]`)

func findLLVMMC(t *testing.T) string {
	for _, candidate := range llvmMCCandidates {
		if _, err := os.Stat(candidate); err == nil {
			return candidate
		}
	}
	t.Skip("llvm-mc not present")
	return ""
}

// llvmEncode assembles each line with llvm-mc; the result per line is the
// four bytes, nil when the assembler rejected the line or left a fixup.
func llvmEncode(t *testing.T, llvmMC string, lines []string) [][]byte {
	out := make([][]byte, len(lines))
	// One process per line keeps rejected lines from shifting the others.
	// Batch in chunks with a marker instruction between lines instead:
	// `nop` encodes to a fixed word we can recognize.
	var input bytes.Buffer
	for _, line := range lines {
		input.WriteString(line)
		input.WriteString("\n\tmovz x3, #0xbeef\n")
	}
	cmd := exec.Command(llvmMC, "--triple=arm64", "-mcpu=apple-m4", "--show-encoding")
	cmd.Stdin = &input
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	_ = cmd.Run() // rejected lines report on stderr and are absent from stdout
	index := 0
	var pending []byte
	scanner := bufio.NewScanner(&stdout)
	scanner.Buffer(make([]byte, 1<<20), 1<<26)
	for scanner.Scan() {
		line := scanner.Text()
		m := llvmEncodingLine.FindStringSubmatch(line)
		if m == nil {
			continue
		}
		word := make([]byte, 4)
		for i := 0; i < 4; i++ {
			v, _ := strconv.ParseUint(m[i+1][2:], 16, 8)
			word[i] = byte(v)
		}
		if bytes.Equal(word, []byte{0xe3, 0xdd, 0x97, 0xd2}) && strings.Contains(line, "48879") {
			if index < len(out) {
				out[index] = pending
			}
			pending = nil
			index++
			continue
		}
		pending = word
	}
	return out
}

func encodeText(t *testing.T, text string) (uint32, error) {
	instr, err := parseInstruction(splitFields(text), 1)
	if err != nil {
		return 0, err
	}
	word, _, err := EncodeInstruction(instr, 0, map[string]int64{})
	return word, err
}

func wordBytes(word uint32) []byte {
	return []byte{byte(word), byte(word >> 8), byte(word >> 16), byte(word >> 24)}
}

// Hand-picked instructions: the checker's idioms across the general-purpose
// ISA, memory forms, aliases, immediates, and system instructions.
var encoderSamples = []string{
	"add x0, x1, x2", "add w0, w1, w2", "add x0, x1, x2, lsl #3", "add x0, x1, w2, uxtw #2", "add x0, x1, w2, sxtw", "add x0, x1, #4095", "add x0, x1, #4095, lsl #12",
	"add sp, sp, #16", "sub sp, sp, #32", "adds x0, x1, x2", "subs w0, w1, #7", "sub x0, x1, x2, lsr #4", "cmp x0, x1", "cmp w0, #12", "cmn x0, x1", "cmp x0, w1, sxth",
	"neg x0, x1", "negs w0, w1", "adc x0, x1, x2", "adcs w0, w1, w2", "sbc x0, x1, x2", "sbcs x0, x1, x2", "ngc x0, x1", "ngcs w0, w1",
	"and x0, x1, x2", "and x0, x1, #0xff", "and w0, w1, #0xf0f0f0f0", "ands x0, x1, #0x3", "orr x0, x1, x2, lsl #8", "orr w0, w1, #0x7", "eor x0, x1, #0xffff0000", "eon x0, x1, x2", "bic x0, x1, x2", "bics w0, w1, w2", "orn x0, x1, x2", "tst x0, x1", "tst w0, #8", "mvn x0, x1",
	"lsl x0, x1, #3", "lsr w0, w1, #5", "asr x0, x1, #63", "ror x0, x1, #7", "lsl x0, x1, x2", "lsr w0, w1, w2", "asr x0, x1, x2", "ror w0, w1, w2", "extr x0, x1, x2, #8", "lslv x0, x1, x2", "rorv w0, w1, w2",
	"ubfx x0, x1, #4, #8", "ubfiz w0, w1, #3, #9", "sbfx x0, x1, #7, #20", "sbfiz x0, x1, #4, #8", "bfi x0, x1, #4, #8", "bfxil x0, x1, #4, #8", "bfc x0, #4, #8", "bfm x0, x1, #4, #8", "sbfm w0, w1, #3, #9", "ubfm x0, x1, #7, #20",
	"rev x0, x1", "rev16 w0, w1", "rev32 x0, x1", "rev64 x0, x1", "rbit x0, x1", "clz x0, x1", "cls w0, w1", "sxtb x0, w1", "sxth w0, w1", "sxtw x0, w1", "uxtb w0, w1", "uxth w0, w1",
	"movz x0, #1", "movz x0, #1, lsl #16", "movn w0, #7", "movk x0, #2, lsl #32", "mov x0, #0x1234", "mov x0, #0x12340000", "mov x0, #-1", "mov w0, #-2", "mov x0, #0xffff0000ffff0000", "mov x0, #0x00ff00ff00ff00ff", "mov x0, x1", "mov w0, w1", "mov sp, x1", "mov x1, sp",
	"mul x0, x1, x2", "madd x0, x1, x2, x3", "msub w0, w1, w2, w3", "mneg x0, x1, x2", "smull x0, w1, w2", "umull x0, w1, w2", "smaddl x0, w1, w2, x3", "umsubl x0, w1, w2, x3", "smnegl x0, w1, w2", "smulh x0, x1, x2", "umulh x0, x1, x2", "udiv x0, x1, x2", "sdiv w0, w1, w2",
	"csel x0, x1, x2, lo", "csinc w0, w1, w2, eq", "csinv x0, x1, x2, ne", "csneg x0, x1, x2, ge", "cset x0, lo", "csetm w0, eq", "cinc x0, x1, hi", "cinv x0, x1, ls", "cneg w0, w1, lt", "ccmp x0, x1, #0, eq", "ccmp w0, #3, #4, ne", "ccmn x0, x1, #15, gt",
	"ldr x0, [x1]", "ldr x0, [x1, #8]", "ldr w0, [sp, #12]", "ldr x0, [sp, #-16]!", "ldr x0, [sp], #16", "ldr x0, [x1, #3]", "ldr x0, [x1, w2, uxtw #3]", "ldr w0, [x1, w2, uxtw #2]", "ldr x0, [x1, x2]", "ldr x0, [x1, x2, lsl #3]",
	"str x0, [sp, #-16]!", "str w0, [x1, #4]", "str x0, [x1], #8", "ldrb w0, [x1, #1]", "strb w0, [x1, w2, uxtw]", "ldrh w0, [x1, #2]", "strh w0, [x1]", "ldrsb x0, [x1]", "ldrsh w0, [x1, #2]", "ldrsw x0, [x1, #4]", "ldrsw x0, [x1, w2, uxtw #2]",
	"ldur x0, [x1, #-3]", "stur w0, [sp, #5]", "ldurb w0, [x1, #1]", "ldursh x0, [x1, #-7]", "ldursw x0, [x1, #3]",
	"ldp x0, x1, [sp]", "ldp x0, x1, [sp], #16", "stp x0, x1, [sp, #-16]!", "stp w0, w1, [x2, #8]", "ldpsw x0, x1, [x2, #4]", "ldnp x0, x1, [x2, #16]", "stnp x0, x1, [x2]",
	"ldar x0, [x1]", "ldarb w0, [x1]", "ldxr x0, [x1]", "ldaxr w0, [x1]", "stlr x0, [x1]", "stxr w0, x1, [x2]", "stlxr w0, w1, [x2]", "stlxrb w0, w1, [x2]", "ldapr x0, [x1]", "ldxp x0, x1, [x2]", "stxp w0, x1, x2, [x3]", "stlxp w0, w1, w2, [x3]",
	"ldadd x0, x1, [x2]", "ldaddal w0, w1, [x2]", "ldclrb w0, w1, [x2]", "swpal x0, x1, [x2]", "cas x0, x1, [x2]", "casal w0, w1, [x2]", "casp x0, x1, x2, x3, [x4]", "stadd x0, [x1]", "stclrl w0, [x1]", "ldumaxh w0, w1, [x2]",
	"ldtr x0, [x1, #8]", "sttrb w0, [x1, #-1]", "ldtrsw x0, [x1, #4]", "ldlar x0, [x1]", "stllrh w0, [x1]", "ldapur x0, [x1, #8]", "stlur w0, [x1, #-4]", "ldapursw x0, [x1]", "ldraa x0, [x1, #8]", "ldrab x0, [x1]",
	"prfm pldl1keep, [x0]", "prfm pstl2strm, [x0, #8]", "prfm #5, [x0]", "prfum pldl1keep, [x0, #-8]",
	"br x1", "blr x2", "ret", "ret x30", "eret", "nop", "wfe", "wfi", "sev", "sevl", "yield", "csdb", "esb", "hint #7", "clrex", "brk #1", "svc #0", "hvc #3", "smc #2",
	"dmb ish", "dmb sy", "dsb sy", "dsb ishst", "dsb #4", "isb", "isb sy", "ssbb", "pssbb", "sb", "dgh", "bti", "bti c", "bti j", "bti jc", "wfet x0", "wfit x1",
	"dc civac, x0", "dc zva, x1", "ic iallu", "ic ivau, x0", "tlbi vmalle1is", "tlbi vae1is, x0", "at s1e1r, x0", "cfp rctx, x0", "cpp rctx, x0", "dvp rctx, x0",
	"mrs x0, cntvct_el0", "mrs x0, s3_3_c14_c0_2", "msr cntvoff_el2, x0", "msr vbar_el1, x0", "mrs x0, nzcv", "msr nzcv, x0", "msr daifset, #2", "msr daifclr, #3", "msr spsel, #1",
	"crc32b w0, w1, w2", "crc32x w0, w1, x2", "crc32cw w0, w1, w2", "cfinv", "setf8 w0", "setf16 w1", "rmif x0, #3, #15", "axflag", "xaflag",
	"pacia x0, x1", "pacib x0, sp", "autda x0, x1", "autdb x0, sp", "paciza x0", "autizb x1", "xpaci x0", "xpacd x1", "paciasp", "autiasp", "paciaz", "autibz", "pacia1716", "autib1716", "xpaclri", "pacga x0, x1, x2", "pacga x0, x1, sp",
	"retaa", "retab", "braa x1, x0", "brab x1, sp", "braaz x1", "brabz x2", "blraa x1, x0", "blrab x1, sp", "blraaz x1", "blrabz x2", "eretaa", "eretab",
	// FP and NEON.
	"fmov d0, d1", "fmov s0, w1", "fmov d0, x1", "fmov w0, s1", "fmov x0, d1", "fmov h0, h1", "fmov h0, w1", "fmov x0, h1", "fmov d0, #1.0", "fmov s0, #0.5", "fmov v0.2d, #1.0", "fmov x0, v1.d[1]", "fmov v0.d[1], x1",
	"fadd d0, d1, d2", "fsub s0, s1, s2", "fmul h0, h1, h2", "fdiv d0, d1, d2", "fnmul d0, d1, d2", "fmax s0, s1, s2", "fminnm d0, d1, d2", "fneg d0, d1", "fabs s0, s1", "fsqrt d0, d1", "frinta d0, d1", "frintz s0, s1", "frint32z d0, d1", "frint64x s0, s1",
	"fmadd d0, d1, d2, d3", "fmsub s0, s1, s2, s3", "fnmadd d0, d1, d2, d3", "fnmsub h0, h1, h2, h3", "fcmp d0, d1", "fcmp s0, #0.0", "fcmpe d0, d1", "fccmp d0, d1, #0, eq", "fccmpe s0, s1, #4, ne", "fcsel d0, d1, d2, lo",
	"fcvt s0, d1", "fcvt d0, s1", "fcvt h0, s1", "fcvtzs x0, d1", "fcvtzu w0, s1", "fcvtas x0, d1", "fcvtms w0, s1", "fcvtns x0, d1", "fcvtps w0, s1", "fcvtzs x0, d1, #4", "fcvtzu w0, s1, #2", "fcvtzs d0, d1", "fcvtzs s0, s1, #3", "scvtf d0, x1", "ucvtf s0, w1", "scvtf d0, x1, #8", "scvtf d0, d1", "ucvtf s0, s1, #4", "fjcvtzs w0, d1",
	"fcvtn v0.2s, v1.2d", "fcvtl v0.2d, v1.2s", "fcvtn2 v0.4s, v1.2d", "fcvtl2 v0.2d, v1.4s", "fcvtxn v0.2s, v1.2d", "fcvtxn s0, d1", "fcvtzs v0.4s, v1.4s", "fcvtzs v0.4s, v1.4s, #3", "scvtf v0.2d, v1.2d", "ucvtf v0.4s, v1.4s, #5",
	"add v0.4s, v1.4s, v2.4s", "sub v0.16b, v1.16b, v2.16b", "add d0, d1, d2", "sub d0, d1, d2", "mul v0.8h, v1.8h, v2.8h", "mul v0.4s, v1.4s, v2.s[1]", "mla v0.4s, v1.4s, v2.4s", "mls v0.2s, v1.2s, v2.s[3]", "and v0.16b, v1.16b, v2.16b", "orr v0.8b, v1.8b, v2.8b", "eor v0.16b, v1.16b, v2.16b", "bic v0.16b, v1.16b, v2.16b", "orn v0.16b, v1.16b, v2.16b", "bsl v0.16b, v1.16b, v2.16b", "bit v0.8b, v1.8b, v2.8b", "bif v0.16b, v1.16b, v2.16b",
	"orr v0.4s, #7", "orr v0.4s, #7, lsl #8", "bic v0.8h, #3, lsl #8", "movi v0.4s, #1", "movi v0.16b, #0xff", "movi v0.2d, #0xff00ff00ff00ff00", "movi d0, #0xff", "movi v0.4s, #1, lsl #24", "movi v0.2s, #5, msl #16", "mvni v0.8h, #2", "mvni v0.4s, #2, lsl #8",
	"neg v0.4s, v1.4s", "neg d0, d1", "mvn v0.16b, v1.16b", "not v0.8b, v1.8b", "abs v0.2d, v1.2d", "abs d0, d1", "cnt v0.16b, v1.16b", "rev16 v0.16b, v1.16b", "rev32 v0.8h, v1.8h", "rev64 v0.4s, v1.4s", "clz v0.4s, v1.4s", "cls v0.8h, v1.8h", "rbit v0.16b, v1.16b",
	"smax v0.4s, v1.4s, v2.4s", "umin v0.16b, v1.16b, v2.16b", "sabd v0.8h, v1.8h, v2.8h", "uabd v0.4s, v1.4s, v2.4s", "shadd v0.4s, v1.4s, v2.4s", "uhsub v0.8h, v1.8h, v2.8h", "srhadd v0.16b, v1.16b, v2.16b", "sqadd v0.4s, v1.4s, v2.4s", "uqsub v0.8h, v1.8h, v2.8h", "sqadd d0, d1, d2", "uqadd s0, s1, s2", "sqsub b0, b1, b2", "suqadd v0.4s, v1.4s", "usqadd d0, d1", "sqabs v0.4s, v1.4s", "sqneg s0, s1",
	"addp v0.4s, v1.4s, v2.4s", "addp d0, v1.2d", "smaxp v0.8h, v1.8h, v2.8h", "uminp v0.16b, v1.16b, v2.16b", "faddp v0.4s, v1.4s, v2.4s", "faddp s0, v1.2s", "fmaxp d0, v1.2d", "fmaxnmp v0.2d, v1.2d, v2.2d", "fminnmp h0, v1.2h",
	"cmeq v0.4s, v1.4s, v2.4s", "cmeq v0.4s, v1.4s, #0", "cmgt v0.8h, v1.8h, #0", "cmge d0, d1, d2", "cmhi v0.16b, v1.16b, v2.16b", "cmhs v0.4s, v1.4s, v2.4s", "cmtst d0, d1, d2", "cmlt v0.4s, v1.4s, #0", "cmle d0, d1, #0",
	"fcmeq v0.4s, v1.4s, v2.4s", "fcmeq v0.2d, v1.2d, #0.0", "fcmgt d0, d1, d2", "fcmge s0, s1, #0.0", "fcmlt v0.4s, v1.4s, #0.0", "fcmle d0, d1, #0.0", "facge v0.4s, v1.4s, v2.4s", "facgt d0, d1, d2",
	"addv b0, v1.8b", "addv h0, v1.4h", "addv s0, v1.4s", "smaxv b0, v1.16b", "uminv h0, v1.8h", "saddlv h0, v1.8b", "uaddlv d0, v1.4s", "fmaxv s0, v1.4s", "fminnmv h0, v1.4h",
	"shl v0.4s, v1.4s, #3", "shl d0, d1, #7", "ushr v0.2d, v1.2d, #5", "sshr v0.16b, v1.16b, #2", "sshr d0, d1, #4", "sli v0.4s, v1.4s, #3", "sri d0, d1, #9", "ssra v0.8h, v1.8h, #3", "usra d0, d1, #5", "srshr v0.4s, v1.4s, #3", "urshr d0, d1, #3", "srsra v0.4s, v1.4s, #3", "ursra d0, d1, #3",
	"shrn v0.4h, v1.4s, #8", "shrn2 v0.8h, v1.4s, #8", "rshrn v0.2s, v1.2d, #16", "sqshrn v0.4h, v1.4s, #8", "sqshrn h0, s1, #3", "uqshrn b0, h1, #2", "sqrshrn s0, d1, #7", "uqrshrn2 v0.8h, v1.4s, #8", "sqshrun v0.4h, v1.4s, #8", "sqrshrun2 v0.16b, v1.8h, #4",
	"ushll v0.4s, v1.4h, #0", "ushll2 v0.4s, v1.8h, #3", "sshll v0.2d, v1.2s, #1", "shll v0.4s, v1.4h, #16", "shll2 v0.2d, v1.4s, #32", "sxtl v0.4s, v1.4h", "uxtl2 v0.8h, v1.16b",
	"uqshl v0.4s, v1.4s, #3", "sqshl d0, d1, #7", "sqshl v0.4s, v1.4s, v2.4s", "uqshl b0, b1, b2", "sqshlu v0.4s, v1.4s, #3", "sqshlu s0, s1, #3", "ushl v0.4s, v1.4s, v2.4s", "sshl d0, d1, d2", "urshl v0.16b, v1.16b, v2.16b", "srshl d0, d1, d2", "sqrshl v0.8h, v1.8h, v2.8h", "uqrshl h0, h1, h2",
	"xtn v0.4h, v1.4s", "xtn2 v0.8h, v1.4s", "sqxtn v0.2s, v1.2d", "sqxtn s0, d1", "uqxtn2 v0.16b, v1.8h", "sqxtun v0.4h, v1.4s", "sqxtun2 v0.4s, v1.2d", "sqxtun h0, s1",
	"uaddlp v0.2d, v1.4s", "saddlp v0.4h, v1.8b", "uadalp v0.2d, v1.4s", "sadalp v0.8h, v1.16b",
	"uaddl v0.4s, v1.4h, v2.4h", "saddl2 v0.2d, v1.4s, v2.4s", "usubl v0.8h, v1.8b, v2.8b", "ssubl2 v0.4s, v1.8h, v2.8h", "uaddw v0.4s, v1.4s, v2.4h", "saddw2 v0.2d, v1.2d, v2.4s", "usubw v0.8h, v1.8h, v2.8b", "ssubw2 v0.4s, v1.4s, v2.8h",
	"umull v0.4s, v1.4h, v2.4h", "smull2 v0.2d, v1.4s, v2.4s", "umlal v0.4s, v1.4h, v2.4h", "smlsl2 v0.2d, v1.4s, v2.4s", "smull v0.4s, v1.4h, v2.h[3]", "umlal2 v0.4s, v1.8h, v2.h[7]", "smlsl v0.2d, v1.2s, v2.s[1]",
	"addhn v0.4h, v1.4s, v2.4s", "raddhn2 v0.8h, v1.4s, v2.4s", "subhn v0.2s, v1.2d, v2.2d", "rsubhn2 v0.16b, v1.8h, v2.8h", "saba v0.4s, v1.4s, v2.4s", "uabal v0.4s, v1.4h, v2.4h", "sabdl2 v0.2d, v1.4s, v2.4s",
	"sqdmulh v0.4s, v1.4s, v2.4s", "sqrdmulh h0, h1, h2", "sqdmulh v0.4h, v1.4h, v2.h[2]", "sqrdmlah v0.4s, v1.4s, v2.4s", "sqrdmlsh s0, s1, v2.s[3]", "sqdmull v0.4s, v1.4h, v2.4h", "sqdmlal s0, h1, h2", "sqdmlsl2 v0.2d, v1.4s, v2.4s", "sqdmull d0, s1, v2.s[1]", "sqdmlal v0.4s, v1.4h, v2.h[1]",
	"fmla v0.4s, v1.4s, v2.4s", "fmls v0.2d, v1.2d, v2.2d", "fmla v0.4s, v1.4s, v2.s[3]", "fmls d0, d1, v2.d[1]", "fmul v0.2s, v1.2s, v2.s[0]", "fmul s0, s1, v2.s[2]", "fmulx v0.4s, v1.4s, v2.4s", "fmulx d0, d1, d2", "fmulx s0, s1, v2.s[1]", "fabd v0.4s, v1.4s, v2.4s", "fabd d0, d1, d2",
	"frecpe v0.4s, v1.4s", "frecpe d0, d1", "frsqrte s0, s1", "frecps v0.2d, v1.2d, v2.2d", "frsqrts d0, d1, d2", "frecpx d0, d1", "urecpe v0.4s, v1.4s", "ursqrte v0.2s, v1.2s",
	"dup v0.4s, w1", "dup v0.2d, x1", "dup v0.8h, v1.h[3]", "dup s0, v1.s[2]", "dup b0, v1.b[15]", "ins v0.s[1], w2", "ins v0.d[1], x2", "ins v0.b[3], v1.b[7]", "umov w0, v1.s[1]", "umov x0, v1.d[1]", "smov x0, v1.h[2]", "smov w0, v1.b[7]",
	"mov v0.16b, v1.16b", "mov w0, v1.s[1]", "mov x0, v1.d[0]", "mov v0.s[1], w2", "mov v0.d[1], x2", "mov v0.h[2], v1.h[5]", "mov s0, v1.s[3]",
	"ext v0.16b, v1.16b, v2.16b, #3", "ext v0.8b, v1.8b, v2.8b, #7", "tbl v0.16b, {v1.16b}, v2.16b", "tbl v0.8b, {v1.16b, v2.16b}, v3.8b", "tbx v0.16b, {v1.16b, v2.16b, v3.16b, v4.16b}, v5.16b",
	"zip1 v0.4s, v1.4s, v2.4s", "zip2 v0.16b, v1.16b, v2.16b", "uzp1 v0.8h, v1.8h, v2.8h", "uzp2 v0.2d, v1.2d, v2.2d", "trn1 v0.4s, v1.4s, v2.4s", "trn2 v0.8b, v1.8b, v2.8b",
	"ld1 {v0.16b}, [x1]", "ld1 {v0.4s, v1.4s}, [x1]", "ld1 {v0.2d, v1.2d, v2.2d}, [x1]", "ld1 {v0.8h, v1.8h, v2.8h, v3.8h}, [x1]", "st1 {v0.4s}, [x1]", "st1 {v0.2d, v1.2d}, [x1]", "ld2 {v0.4s, v1.4s}, [x1]", "st2 {v0.8b, v1.8b}, [x1]", "ld3 {v0.4s, v1.4s, v2.4s}, [x1]", "st3 {v0.2d, v1.2d, v2.2d}, [x1]", "ld4 {v0.4s, v1.4s, v2.4s, v3.4s}, [x1]", "st4 {v0.16b, v1.16b, v2.16b, v3.16b}, [x1]",
	"ld1r {v0.4s}, [x1]", "ld2r {v0.2d, v1.2d}, [x1]", "ld3r {v0.8h, v1.8h, v2.8h}, [x1]", "ld4r {v0.16b, v1.16b, v2.16b, v3.16b}, [x1]",
	"ldr q0, [x1]", "ldr q0, [x1, #16]", "ldr d0, [sp, #8]", "ldr s0, [x1, #4]", "ldr h0, [x1, #2]", "ldr b0, [x1, #1]", "str q0, [sp, #-16]!", "str d0, [x1], #8", "ldur q0, [x1, #-3]", "stur s0, [x1, #5]", "ldp q0, q1, [sp]", "stp d0, d1, [sp, #-16]!", "ldp s0, s1, [x1], #8", "ldnp q0, q1, [x1]", "stnp d0, d1, [x1, #16]",
	"ldr q0, [x1, x2]", "ldr d0, [x1, w2, uxtw #3]", "str s0, [x1, x2, lsl #2]", "ldapur q0, [x1, #16]", "stlur d0, [x1]",
	"sdot v0.4s, v1.16b, v2.16b", "udot v0.2s, v1.8b, v2.8b", "sdot v0.4s, v1.16b, v2.4b[1]", "usdot v0.4s, v1.16b, v2.16b", "sudot v0.4s, v1.16b, v2.4b[3]", "bfdot v0.4s, v1.8h, v2.8h", "bfdot v0.2s, v1.4h, v2.2h[1]",
	"smmla v0.4s, v1.16b, v2.16b", "ummla v0.4s, v1.16b, v2.16b", "usmmla v0.4s, v1.16b, v2.16b", "bfmmla v0.4s, v1.8h, v2.8h", "bfmlalb v0.4s, v1.8h, v2.8h", "bfmlalt v0.4s, v1.8h, v2.h[3]", "bfcvt h0, s1", "bfcvtn v0.4h, v1.4s", "bfcvtn2 v0.8h, v1.4s",
	"fmlal v0.4s, v1.4h, v2.4h", "fmlsl v0.2s, v1.2h, v2.2h", "fmlal2 v0.4s, v1.4h, v2.4h", "fmlsl2 v0.4s, v1.4h, v2.h[3]", "fmlal v0.4s, v1.4h, v2.h[1]", "fcadd v0.4s, v1.4s, v2.4s, #90", "fcadd v0.2d, v1.2d, v2.2d, #270", "fcmla v0.4s, v1.4s, v2.4s, #180", "fcmla v0.4s, v1.4s, v2.s[1], #90",
	"aese v0.16b, v1.16b", "aesd v0.16b, v1.16b", "aesmc v0.16b, v1.16b", "aesimc v0.16b, v1.16b", "sha1c q0, s1, v2.4s", "sha1p q0, s1, v2.4s", "sha1m q0, s1, v2.4s", "sha1h s0, s1", "sha1su0 v0.4s, v1.4s, v2.4s", "sha1su1 v0.4s, v1.4s",
	"sha256h q0, q1, v2.4s", "sha256h2 q0, q1, v2.4s", "sha256su0 v0.4s, v1.4s", "sha256su1 v0.4s, v1.4s, v2.4s", "sha512h q0, q1, v2.2d", "sha512h2 q0, q1, v2.2d", "sha512su0 v0.2d, v1.2d", "sha512su1 v0.2d, v1.2d, v2.2d",
	"eor3 v0.16b, v1.16b, v2.16b, v3.16b", "bcax v0.16b, v1.16b, v2.16b, v3.16b", "rax1 v0.2d, v1.2d, v2.2d", "xar v0.2d, v1.2d, v2.2d, #7", "pmul v0.16b, v1.16b, v2.16b", "pmull v0.8h, v1.8b, v2.8b", "pmull v0.1q, v1.1d, v2.1d", "pmull2 v0.1q, v1.2d, v2.2d",
	"fadd v0.4s, v1.4s, v2.4s", "fsub v0.2d, v1.2d, v2.2d", "fmul v0.4h, v1.4h, v2.4h", "fdiv v0.2s, v1.2s, v2.2s", "fmax v0.4s, v1.4s, v2.4s", "fminnm v0.2d, v1.2d, v2.2d", "fneg v0.4s, v1.4s", "fabs v0.2d, v1.2d", "fsqrt v0.4s, v1.4s", "frintm v0.4s, v1.4s", "frint32x v0.4s, v1.4s", "frint64z v0.2d, v1.2d",
	"fcvtzs w0, h1", "fcvtau x0, h1", "scvtf h0, w1", "ucvtf h0, x1, #4", "fadd h0, h1, h2", "fcmp h0, h1", "fcsel h0, h1, h2, ne", "fcvtas h0, h1", "fcvtzs h0, h1, #2",
}

func TestEncoderAgainstLLVM(t *testing.T) {
	llvmMC := findLLVMMC(t)
	expected := llvmEncode(t, llvmMC, encoderSamples)
	var failures []string
	rejected := 0
	for i, text := range encoderSamples {
		word, err := encodeText(t, text)
		if expected[i] == nil {
			if err == nil {
				rejected++
				failures = append(failures, fmt.Sprintf("  %-40s llvm rejects; we encode %08x", text, word))
			}
			continue
		}
		if err != nil {
			failures = append(failures, fmt.Sprintf("  %-40s llvm %x; we fail: %v", text, expected[i], err))
			continue
		}
		if !bytes.Equal(wordBytes(word), expected[i]) {
			failures = append(failures, fmt.Sprintf("  %-40s llvm %x; we %x", text, expected[i], wordBytes(word)))
		}
	}
	if len(failures) > 0 {
		t.Errorf("%d of %d samples disagree with llvm-mc:\n%s", len(failures), len(encoderSamples), strings.Join(failures, "\n"))
	}
}

// TestEncoderFuzzAgainstLLVM instantiates every template reading of the
// generated table with random operands and compares both assemblers. A
// reading llvm-mc rejects is skipped (the random operand may be
// architecturally invalid in a way the template does not spell); a
// reading both accept must agree bit for bit.
func TestEncoderFuzzAgainstLLVM(t *testing.T) {
	llvmMC := findLLVMMC(t)
	rng := rand.New(rand.NewSource(940))
	var texts []string
	var origin []string
	for i := range isaEncodings {
		enc := &isaEncodings[i]
		if _, inTable := instructionTable[enc.Mnemonic]; !inTable {
			continue
		}
		for f := range enc.Forms {
			for k := 0; k < 3; k++ {
				text, ok := instantiate(rng, enc, &enc.Forms[f])
				if !ok {
					break
				}
				texts = append(texts, text)
				origin = append(origin, enc.Name)
			}
		}
	}
	expected := llvmEncode(t, llvmMC, texts)
	var failures []string
	agreed, skipped, ours := 0, 0, 0
	byEncoding := map[string]bool{}
	for i, text := range texts {
		word, err := encodeText(t, text)
		if expected[i] == nil {
			skipped++
			continue
		}
		if err != nil {
			ours++
			if len(failures) < 120 {
				failures = append(failures, fmt.Sprintf("  %-48s [%s] llvm %x; we fail: %v", text, origin[i], expected[i], err))
			}
			continue
		}
		if !bytes.Equal(wordBytes(word), expected[i]) {
			if len(failures) < 120 {
				failures = append(failures, fmt.Sprintf("  %-48s [%s] llvm %x; we %x", text, origin[i], expected[i], wordBytes(word)))
			}
			continue
		}
		agreed++
		byEncoding[origin[i]] = true
	}
	t.Logf("%d instantiations from %s: %d agree (%d encodings), %d rejected by llvm-mc, %d we could not encode", len(texts), isaRelease, agreed, len(byEncoding), skipped, ours)
	if len(failures) > 0 {
		sort.Strings(failures)
		t.Errorf("disagreements with llvm-mc:\n%s", strings.Join(failures, "\n"))
	}
}

// instantiate spells one reading with random operands in our syntax.
func instantiate(rng *rand.Rand, enc *isaEncoding, form *isaForm) (string, bool) {
	if enc.Mnemonic == "movprfx" {
		return "", false // LLVM rejects the marker instruction that follows a movprfx
	}
	var parts []string
	prevReg := ""
	// One spelling per template symbol (`<Zdn>` twice), one element size per
	// size table (`<T>` across operands).
	chosen := map[string]string{}
	letters := map[string]string{}
	for i := 0; i < len(form.Operands); i++ {
		fop := &form.Operands[i]
		switch fop.Kind {
		case "gp":
			width := fop.Width
			if width == 0 {
				width = 64
			}
			n := rng.Intn(29) + 1 // avoid 30 (lr) and 31 for determinism of sp/zr handling
			text := fmt.Sprintf("x%d", n)
			if width == 32 {
				text = fmt.Sprintf("w%d", n)
			}
			if strings.HasPrefix(fop.Fields[0], "+") {
				// The register after the previous one.
				if prevReg == "" {
					return "", false
				}
				num, _ := strconv.Atoi(prevReg[1:])
				text = fmt.Sprintf("%c%d", prevReg[0], num+1)
			} else if fop.SP && rng.Intn(3) == 0 && width == 64 {
				text = "sp"
			}
			prevReg = text
			parts = append(parts, text)
		case "fp":
			width := fop.Width
			if width == 0 {
				if len(fop.Sizes) == 0 {
					return "", false
				}
				row := fop.Sizes[rng.Intn(len(fop.Sizes))]
				width = map[string]int{"B": 8, "H": 16, "S": 32, "D": 64, "Q": 128}[row.Text]
			}
			letter := map[int]string{8: "b", 16: "h", 32: "s", 64: "d", 128: "q"}[width]
			parts = append(parts, fmt.Sprintf("%s%d", letter, rng.Intn(32)))
		case "vecarr":
			arr := strings.ToLower(fop.Text)
			if arr == "" {
				if len(fop.Sub) == 0 || len(fop.Sub[0].Table) == 0 {
					return "", false
				}
				arr = strings.ToLower(fop.Sub[0].Table[rng.Intn(len(fop.Sub[0].Table))].Text)
			}
			parts = append(parts, fmt.Sprintf("v%d.%s", rng.Intn(32), arr))
		case "veclane":
			letter := strings.ToLower(fop.Text)
			if letter == "" {
				for _, sub := range fop.Sub {
					if sub.Kind == "table" && len(sub.Table) > 0 {
						letter = strings.ToLower(sub.Table[rng.Intn(len(sub.Table))].Text)
					}
				}
			}
			if letter == "" {
				return "", false
			}
			lanes := map[string]int{"b": 16, "h": 8, "s": 4, "d": 2, "4b": 4, "2h": 4}[letter]
			if lanes == 0 {
				return "", false
			}
			lane := rng.Intn(lanes)
			for _, sub := range fop.Sub {
				if sub.Kind == "text" {
					lane, _ = strconv.Atoi(sub.Text)
				}
			}
			regs := 32
			if strings.Join(fop.Fields, ":") == "Rm" && letter == "h" {
				regs = 16
			}
			parts = append(parts, fmt.Sprintf("v%d.%s[%d]", rng.Intn(regs), letter, lane))
		case "imm":
			v, ok := randomImmediate(rng, fop)
			if !ok {
				return "", false
			}
			parts = append(parts, "#"+strconv.FormatInt(v, 10))
		case "fimm":
			parts = append(parts, "#1.0")
		case "cond":
			codes := []string{"eq", "ne", "hs", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le"}
			parts = append(parts, codes[rng.Intn(len(codes))])
		case "table":
			if fop.Sym == "<shift>" || fop.Sym == "<extend>" {
				// Modifier of the previous operand: `, lsl #n` or `, uxtw #n`.
				if len(fop.Table) == 0 || len(parts) == 0 {
					return "", false
				}
				row := fop.Table[rng.Intn(len(fop.Table))]
				amount := ""
				if i+1 < len(form.Operands) && form.Operands[i+1].Kind == "imm" {
					i++
					v, ok := randomImmediate(rng, &form.Operands[i])
					if !ok {
						return "", false
					}
					if strings.Contains(row.Text, "#") {
						// `LSL #12` rows carry their own amount.
						parts[len(parts)-1] += ", " + strings.ToLower(row.Text)
						continue
					}
					amount = " #" + strconv.FormatInt(v, 10)
				}
				if strings.Contains(row.Text, "#") {
					parts[len(parts)-1] += ", " + strings.ToLower(row.Text)
					continue
				}
				parts[len(parts)-1] += ", " + strings.ToLower(row.Text) + amount
				continue
			}
			if len(fop.Table) == 0 {
				return "", false
			}
			row := fop.Table[rng.Intn(len(fop.Table))]
			text := strings.ToLower(row.Text)
			if strings.HasPrefix(fop.Sym, "#") && !strings.HasPrefix(text, "#") {
				text = "#" + text
			}
			parts = append(parts, text)
		case "sysreg":
			parts = append(parts, fmt.Sprintf("s%d_%d_c%d_c%d_%d", 2+rng.Intn(2), rng.Intn(8), rng.Intn(16), rng.Intn(16), rng.Intn(8)))
		case "mem":
			text, ok := randomMemory(rng, fop)
			if !ok {
				return "", false
			}
			parts = append(parts, text)
		case "list":
			if len(fop.Sub) == 0 || fop.Sub[0].Kind != "vecarr" {
				return "", false
			}
			arr := strings.ToLower(fop.Sub[0].Text)
			if arr == "" {
				if len(fop.Sub[0].Sub) == 0 || len(fop.Sub[0].Sub[0].Table) == 0 {
					return "", false
				}
				arr = strings.ToLower(fop.Sub[0].Sub[0].Table[rng.Intn(len(fop.Sub[0].Sub[0].Table))].Text)
			}
			first := rng.Intn(32)
			var regs []string
			for k := range fop.Sub {
				regs = append(regs, fmt.Sprintf("v%d.%s", (first+k)%32, arr))
			}
			parts = append(parts, "{"+strings.Join(regs, ", ")+"}")
		case "zreg", "preg", "pnreg", "tile":
			if prior, seen := chosen[fop.Sym]; seen {
				parts = append(parts, prior)
				continue
			}
			text, ok := randomScalable(rng, enc, fop, letters)
			if !ok {
				return "", false
			}
			chosen[fop.Sym] = text
			parts = append(parts, text)
		case "zlane":
			text, ok := randomScalable(rng, enc, fop, letters)
			if !ok {
				return "", false
			}
			idx, ok := randomIndex(rng, enc, fop)
			if !ok {
				return "", false
			}
			parts = append(parts, fmt.Sprintf("%s[%d]", text, idx))
		case "slice":
			text, ok := randomSlice(rng, enc, fop, letters)
			if !ok {
				return "", false
			}
			parts = append(parts, text)
		case "zlist":
			if len(fop.Sub) == 1 && fop.Sub[0].Kind == "slice" {
				text, ok := randomSlice(rng, enc, &fop.Sub[0], letters)
				if !ok {
					return "", false
				}
				parts = append(parts, "{"+text+"}")
				continue
			}
			head, ok := randomScalable(rng, enc, &fop.Sub[0], letters)
			if !ok {
				return "", false
			}
			// zN.e → the consecutive group.
			num, elem := 0, ""
			if dot := strings.IndexByte(head, '.'); dot > 0 {
				num, _ = strconv.Atoi(head[1:dot])
				elem = head[dot:]
			} else {
				num, _ = strconv.Atoi(head[1:])
			}
			var regs []string
			for k := 0; k < fop.Count; k++ {
				regs = append(regs, fmt.Sprintf("z%d%s", (num+k)%32, elem))
			}
			parts = append(parts, "{"+strings.Join(regs, ", ")+"}")
		case "tilemask":
			if rng.Intn(5) == 0 {
				parts = append(parts, "{za}")
				continue
			}
			sizes := []struct {
				letter string
				tiles  int
			}{{"b", 1}, {"h", 2}, {"s", 4}, {"d", 8}}
			size := sizes[rng.Intn(len(sizes))]
			var tiles []string
			for k := 0; k < size.tiles; k++ {
				if rng.Intn(2) == 0 {
					tiles = append(tiles, fmt.Sprintf("za%d.%s", k, size.letter))
				}
			}
			if len(tiles) == 0 {
				tiles = append(tiles, "za0."+size.letter)
			}
			parts = append(parts, "{"+strings.Join(tiles, ", ")+"}")
		case "text":
			if fop.Text == "MUL" {
				// `MUL #<imm>` after a pattern word.
				if i+1 < len(form.Operands) && len(parts) > 0 && form.Operands[i+1].Kind == "imm" {
					i++
					v, ok := randomImmediate(rng, &form.Operands[i])
					if !ok {
						return "", false
					}
					parts[len(parts)-1] += fmt.Sprintf(", mul #%d", v)
					continue
				}
				return "", false
			}
			if fop.Text == "LSL" || fop.Text == "MSL" {
				// `LSL #<n>` after an immediate.
				if i+1 < len(form.Operands) && len(parts) > 0 {
					i++
					next := &form.Operands[i]
					var amount int64
					switch next.Kind {
					case "imm":
						v, ok := randomImmediate(rng, next)
						if !ok {
							return "", false
						}
						amount = v
					case "table":
						if len(next.Table) == 0 {
							return "", false
						}
						row := next.Table[rng.Intn(len(next.Table))]
						amount, _ = strconv.ParseInt(strings.TrimPrefix(row.Text, "#"), 10, 64)
					case "text":
						amount, _ = strconv.ParseInt(strings.TrimPrefix(next.Text, "#"), 10, 64)
					}
					parts[len(parts)-1] += fmt.Sprintf(", %s #%d", strings.ToLower(fop.Text), amount)
					continue
				}
				return "", false
			}
			parts = append(parts, strings.ToLower(fop.Text))
		default:
			return "", false
		}
	}
	mnemonic := enc.Mnemonic
	if mnemonic == "b." {
		if len(parts) == 0 {
			return "", false
		}
		mnemonic = "b." + parts[0]
		parts = parts[1:]
	}
	return strings.TrimSpace(mnemonic + " " + strings.Join(parts, ", ")), true
}

func randomImmediate(rng *rand.Rand, fop *isaOperand) (int64, bool) {
	if len(fop.Table) > 0 {
		row := fop.Table[rng.Intn(len(fop.Table))]
		v, err := strconv.ParseInt(strings.TrimPrefix(row.Text, "#"), 10, 64)
		return v, err == nil
	}
	switch fop.Special {
	case "bitmask":
		// A run of ones inside the low 32 bits: encodable at either width.
		ones := rng.Intn(31) + 1
		rot := rng.Intn(32 - ones)
		v := (uint64(1)<<uint(ones) - 1) << uint(rot)
		return int64(v), true
	case "wide", "movi", "shift-immh", "fbits", "index", "fp8":
		return 0, false
	case "sve-shift-left":
		return int64(rng.Intn(8)), true // legal for every element size
	case "sve-shift-right":
		return int64(rng.Intn(8) + 1), true
	case "sve-index":
		return int64(rng.Intn(2)), true
	case "sub":
		return int64(rng.Int63n(fop.Offset) + 1), true
	}
	if !fop.HasRange {
		return 0, false
	}
	scale := fop.Scale
	if scale <= 0 {
		scale = 1
	}
	lo, hi := fop.Min/scale, fop.Max/scale
	if hi < lo {
		return 0, false
	}
	v := lo + rng.Int63n(hi-lo+1)
	return v * scale, true
}

func randomMemory(rng *rand.Rand, fop *isaOperand) (string, bool) {
	if len(fop.Sub) == 0 {
		return "", false
	}
	base := fmt.Sprintf("x%d", rng.Intn(29)+1)
	if rng.Intn(4) == 0 {
		base = "sp"
	}
	var off string
	var idx string
	mulVL := false
	for _, sub := range fop.Sub[1:] {
		switch sub.Sym {
		case "MUL VL":
			mulVL = true
		case "off":
			v, ok := randomImmediate(rng, &sub)
			if !ok {
				return "", false
			}
			off = "#" + strconv.FormatInt(v, 10)
		case "idx", "<extend>", "LSL", "<amount>":
			// Our syntax admits `[base, wI, uxtw #s]` and `[base, xI]` /
			// `[base, xI, lsl #s]`; the fuzz uses the uxtw form for W and lsl for X.
			if sub.Sym == "idx" {
				idx = fmt.Sprintf("w%d, uxtw", rng.Intn(29)+1)
				if sub.Width == 64 {
					idx = fmt.Sprintf("x%d, lsl", rng.Intn(29)+1)
				}
			}
			if sub.Sym == "<amount>" && idx != "" {
				var amount int64
				if sub.Kind == "text" {
					amount, _ = strconv.ParseInt(strings.TrimPrefix(sub.Text, "#"), 10, 64)
				} else if len(sub.Table) > 0 {
					row := sub.Table[rng.Intn(len(sub.Table))]
					amount, _ = strconv.ParseInt(strings.TrimPrefix(row.Text, "#"), 10, 64)
				}
				if amount != 0 {
					idx += fmt.Sprintf(" #%d", amount)
				}
			}
		}
	}
	if mulVL {
		if off == "" || idx != "" || fop.Mode != "off" {
			return "", false
		}
		return fmt.Sprintf("[%s, %s, mul vl]", base, off), true
	}
	switch fop.Mode {
	case "post":
		if off == "" {
			return "", false
		}
		return fmt.Sprintf("[%s], %s", base, off), true
	case "pre":
		if off == "" {
			return "", false
		}
		return fmt.Sprintf("[%s, %s]!", base, off), true
	}
	if idx != "" {
		if strings.HasSuffix(idx, ", lsl") {
			idx = strings.TrimSuffix(idx, ", lsl") // `[base, xI]`
		}
		return fmt.Sprintf("[%s, %s]", base, idx), true
	}
	if off != "" {
		return fmt.Sprintf("[%s, %s]", base, off), true
	}
	return fmt.Sprintf("[%s]", base), true
}

// fieldsWidthOf sums the widths of an encoding's named fields (slices
// `f[hi:lo]` count their slice).
func fieldsWidthOf(enc *isaEncoding, names []string) int {
	total := 0
	for _, name := range names {
		base, slice := name, ""
		if i := strings.IndexAny(name, "[<"); i >= 0 {
			base, slice = name[:i], strings.Trim(name[i:], "[]<>")
		}
		for _, f := range enc.Fields {
			if f.Name != base {
				continue
			}
			if slice == "" {
				total += f.Width
			} else if j := strings.IndexByte(slice, ':'); j >= 0 {
				hi, _ := strconv.Atoi(slice[:j])
				lo, _ := strconv.Atoi(slice[j+1:])
				total += hi - lo + 1
			} else {
				total++
			}
		}
	}
	return total
}

// randomElement picks an element size letter the operand admits: its fixed
// letter, a row of its size table (the same row for every operand sharing
// the table's symbol), or "" when it names none.
func randomElement(rng *rand.Rand, fop *isaOperand, letters map[string]string) (string, bool) {
	if fop.Text != "" {
		return strings.ToLower(fop.Text), true
	}
	for _, sub := range fop.Sub {
		if sub.Kind == "table" && sub.Sym != "<ZM>" && sub.Sym != "hv" && sub.Sym != "group" {
			if prior, seen := letters[sub.Sym]; seen {
				return prior, true
			}
			var options []string
			for _, row := range sub.Table {
				if len(row.Text) == 1 {
					options = append(options, strings.ToLower(row.Text))
				}
			}
			if len(options) == 0 {
				return "", false
			}
			letter := options[rng.Intn(len(options))]
			letters[sub.Sym] = letter
			return letter, true
		}
	}
	return "", true
}

// randomScalable spells a z, p, pn, or tile operand the reading admits.
func randomScalable(rng *rand.Rand, enc *isaEncoding, fop *isaOperand, letters map[string]string) (string, bool) {
	prefix := map[string]string{"zreg": "z", "zlane": "z", "preg": "p", "pnreg": "pn", "tile": "za"}[fop.Kind]
	scale := fop.Scale
	if scale <= 0 {
		scale = 1
	}
	var num int64
	if fop.Kind == "tile" && fop.Special == "fixed" {
		num = fop.Offset
	} else {
		width := fieldsWidthOf(enc, fop.Fields)
		if width == 0 {
			return "", false
		}
		num = fop.Offset + int64(rng.Intn(1<<uint(width)))*scale
	}
	elem, ok := randomElement(rng, fop, letters)
	if !ok {
		return "", false
	}
	text := fmt.Sprintf("%s%d", prefix, num)
	if elem != "" {
		text += "." + elem
	}
	switch {
	case fop.Qual != "":
		text += "/" + strings.ToLower(fop.Qual)
	default:
		for _, sub := range fop.Sub {
			if sub.Sym == "<ZM>" {
				text += []string{"/m", "/z"}[rng.Intn(2)]
			}
		}
	}
	return text, true
}

// randomIndex picks the element or portion index of a zlane/pnreg reading.
func randomIndex(rng *rand.Rand, enc *isaEncoding, fop *isaOperand) (int64, bool) {
	for _, sub := range fop.Sub {
		if sub.Sym != "idx" {
			continue
		}
		if sub.Kind == "text" {
			v, _ := strconv.ParseInt(sub.Text, 10, 64)
			return v, true
		}
		if v, ok := randomImmediate(rng, &sub); ok {
			return v, true
		}
		width := fieldsWidthOf(enc, sub.Fields)
		if width == 0 {
			return 0, false
		}
		return int64(rng.Intn(1 << uint(width))), true
	}
	return 0, false
}

// randomSlice spells a ZA slice or array vector the reading admits.
func randomSlice(rng *rand.Rand, enc *isaEncoding, fop *isaOperand, letters map[string]string) (string, bool) {
	var b strings.Builder
	var elem string
	if fop.Text != "" {
		elem = strings.ToLower(fop.Text)
	}
	idxText, offsText, group := "", "", ""
	for i := range fop.Sub {
		sub := &fop.Sub[i]
		switch sub.Sym {
		case "tile":
			switch sub.Special {
			case "array":
				b.WriteString("za")
			case "fixed":
				fmt.Fprintf(&b, "za%d", sub.Offset)
			default:
				width := fieldsWidthOf(enc, sub.Fields)
				if width == 0 {
					return "", false
				}
				fmt.Fprintf(&b, "za%d", rng.Intn(1<<uint(width)))
			}
		case "hv":
			b.WriteString([]string{"h", "v"}[rng.Intn(2)])
		case "elem":
			if prior, seen := letters[sub.Sym]; seen {
				elem = prior
				continue
			}
			var options []string
			for _, row := range sub.Table {
				if len(row.Text) == 1 {
					options = append(options, strings.ToLower(row.Text))
				}
			}
			if len(options) == 0 {
				return "", false
			}
			elem = options[rng.Intn(len(options))]
			letters[sub.Sym] = elem
		case "idx":
			width := fieldsWidthOf(enc, sub.Fields)
			idxText = fmt.Sprintf("w%d", sub.Offset+int64(rng.Intn(1<<uint(width))))
		case "offs":
			var v int64
			if len(sub.Fields) == 0 {
				v = 0
			} else if value, ok := randomImmediate(rng, sub); ok {
				v = value
			} else {
				return "", false
			}
			offsText = strconv.FormatInt(v, 10)
			if fop.Count > 1 {
				offsText = fmt.Sprintf("%d:%d", v, v+int64(fop.Count)-1)
			}
		case "group":
			group = ", " + strings.ToLower(sub.Text)
		}
	}
	if elem != "" {
		b.WriteString("." + elem)
	}
	if idxText == "" || offsText == "" {
		return "", false
	}
	fmt.Fprintf(&b, "[%s, %s%s]", idxText, offsText, group)
	return b.String(), true
}

// TestEncodeFunctionAgainstLLVM encodes whole checked functions — labels
// resolved within the function, calls out as relocations — and compares
// the words with the host assembler's object code for the same text.
func TestEncodeFunctionAgainstLLVM(t *testing.T) {
	llvmMC := findLLVMMC(t)
	objdump := strings.TrimSuffix(llvmMC, "llvm-mc") + "llvm-objdump"
	if _, err := os.Stat(objdump); err != nil {
		t.Skip("llvm-objdump not present")
	}
	source, err := os.ReadFile("../examples/asm/kernels.arm64.oakasm")
	if err != nil {
		t.Fatal(err)
	}
	unit, errs := ParseUnit("kernels.arm64.oakasm", string(source))
	if len(errs) != 0 {
		t.Fatalf("parse: %v", errs)
	}
	for _, fn := range unit.Functions {
		fn := fn
		t.Run(fn.Name, func(t *testing.T) {
			ours, relocs, err := EncodeFunction(fn)
			if err != nil {
				t.Fatalf("encode: %v", err)
			}
			// The same function as assembler text, with the emitter's numeric
			// local labels (`1:` … `1b`/`1f`), which llvm-mc resolves too.
			numbers := map[string]int{}
			for _, item := range fn.Items {
				if label, ok := item.(Label); ok {
					numbers[label.Name] = len(numbers) + 1
				}
			}
			defined := map[string]bool{}
			var text strings.Builder
			for _, item := range fn.Items {
				switch it := item.(type) {
				case Label:
					fmt.Fprintf(&text, "%d:\n", numbers[it.Name])
					defined[it.Name] = true
				case Instruction:
					fmt.Fprintf(&text, "\t%s\n", renderInstruction(fn, it, func(s string) string { return s }, numbers, defined))
				}
			}
			dir := t.TempDir()
			obj := dir + "/f.o"
			cmd := exec.Command(llvmMC, "--triple=arm64", "-mcpu=apple-m4", "-filetype=obj", "-o", obj)
			cmd.Stdin = strings.NewReader(text.String())
			var stderr bytes.Buffer
			cmd.Stderr = &stderr
			if err := cmd.Run(); err != nil {
				t.Fatalf("llvm-mc: %v\n%s\n%s", err, stderr.String(), text.String())
			}
			out, err := exec.Command(objdump, "-d", obj).Output()
			if err != nil {
				t.Fatalf("llvm-objdump: %v", err)
			}
			var theirs []byte
			wordRe := regexp.MustCompile(`^\s*[0-9a-f]+:\s+([0-9a-f]{8})\s`)
			for _, line := range strings.Split(string(out), "\n") {
				if m := wordRe.FindStringSubmatch(line); m != nil {
					v, _ := strconv.ParseUint(m[1], 16, 32)
					theirs = append(theirs, wordBytes(uint32(v))...)
				}
			}
			if !bytes.Equal(ours, theirs) {
				t.Errorf("words differ\nours:   %x\ntheirs: %x\n%s", ours, theirs, text.String())
			}
			t.Logf("%s: %d bytes, %d relocations", fn.Name, len(ours), len(relocs))
		})
	}
}
