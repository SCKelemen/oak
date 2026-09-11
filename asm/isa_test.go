package asm

import (
	"sort"
	"strings"
	"testing"
)

// Every mnemonic in the table parses, matches a form, and passes the seam
// checker in a well-formed sample: the coverage witness for the
// general-purpose ISA (docs/spec/94-assembler.md §3).
func TestInstructionTableCoverage(t *testing.T) {
	samples := map[string]string{
		"mov": "mov x9, x0", "add": "add x9, x0, x1, lsl #2", "sub": "sub x9, x0, x1", "adds": "adds x9, x0, x1", "subs": "subs x9, x0, x1",
		"and": "and x9, x0, x1", "orr": "orr x9, x0, x1", "eor": "eor x9, x0, x1", "lsl": "lsl x9, x0, #3", "lsr": "lsr x9, x0, x1", "asr": "asr x9, x0, #1",
		"cmp": "cmp x0, x1", "cmn": "cmn x0, x1", "tst": "tst x0, #8", "ccmp": "cmp x0, x1\n  ccmp x0, x1, #0, eq", "ccmn": "cmp x0, x1\n  ccmn x0, #1, #4, ne",
		"csel": "cmp x0, x1\n  csel x9, x0, x1, lo", "cset": "cmp x0, x1\n  cset x9, lo", "csinc": "cmp x0, x1\n  csinc x9, x0, x1, lo", "csinv": "cmp x0, x1\n  csinv x9, x0, x1, lo",
		"csneg": "cmp x0, x1\n  csneg x9, x0, x1, lo", "cinc": "cmp x0, x1\n  cinc x9, x0, lo", "cneg": "cmp x0, x1\n  cneg x9, x0, lo", "cinv": "cmp x0, x1\n  cinv x9, x0, lo", "csetm": "cmp x0, x1\n  csetm x9, lo",
		"adc": "cmp x0, x1\n  adc x9, x0, x1", "adcs": "cmp x0, x1\n  adcs x9, x0, x1", "sbc": "cmp x0, x1\n  sbc x9, x0, x1", "sbcs": "cmp x0, x1\n  sbcs x9, x0, x1", "ngc": "cmp x0, x1\n  ngc x9, x0", "ngcs": "cmp x0, x1\n  ngcs x9, x0",
		"neg": "neg x9, x0", "negs": "negs x9, x0", "mvn": "mvn x9, x0", "ands": "ands x9, x0, x1", "bic": "bic x9, x0, x1", "bics": "bics x9, x0, x1", "orn": "orn x9, x0, x1", "eon": "eon x9, x0, x1",
		"ror": "ror x9, x0, #5", "extr": "extr x9, x0, x1, #8", "rev": "rev x9, x0", "rev16": "rev16 x9, x0", "rev32": "rev32 x9, x0", "rbit": "rbit x9, x0", "clz": "clz x9, x0", "cls": "cls x9, x0",
		"sxtb": "sxtb x9, w0", "sxth": "sxth x9, w0", "sxtw": "sxtw x9, w0", "uxtb": "uxtb w9, w0", "uxth": "uxth w9, w0",
		"movz": "movz x9, #1, lsl #16", "movn": "movn x9, #1", "movk": "movz x9, #1\n  movk x9, #2, lsl #32",
		"mul": "mul x9, x0, x1", "madd": "madd x9, x0, x1, x0", "msub": "msub x9, x0, x1, x0", "mneg": "mneg x9, x0, x1", "smull": "smull x9, w0, w1", "umull": "umull x9, w0, w1",
		"smaddl": "smaddl x9, w0, w1, x0", "umaddl": "umaddl x9, w0, w1, x0", "smsubl": "smsubl x9, w0, w1, x0", "umsubl": "umsubl x9, w0, w1, x0", "smulh": "smulh x9, x0, x1", "umulh": "umulh x9, x0, x1",
		"udiv": "udiv x9, x0, x1", "sdiv": "sdiv x9, x0, x1", "ubfx": "ubfx x9, x0, #4, #8", "ubfiz": "ubfiz x9, x0, #4, #8", "sbfx": "sbfx x9, x0, #4, #8", "bfi": "mov x9, x0\n  bfi x9, x1, #4, #8",
		"crc32b": "crc32b w9, w0, w1", "crc32h": "crc32h w9, w0, w1", "crc32w": "crc32w w9, w0, w1", "crc32x": "crc32x w9, w0, x1", "crc32cb": "crc32cb w9, w0, w1", "crc32ch": "crc32ch w9, w0, w1", "crc32cw": "crc32cw w9, w0, w1", "crc32cx": "crc32cx w9, w0, x1",
		"cfinv": "cmp x0, x1\n  cfinv",
		"nop":   "nop", "wfe": "wfe", "wfi": "wfi", "sev": "sev", "sevl": "sevl", "yield": "yield", "csdb": "csdb", "esb": "esb", "hint": "hint #7", "clrex": "clrex",
		"dmb": "dmb ish", "dsb": "dsb sy", "isb": "isb", "ssbb": "ssbb", "pssbb": "pssbb",
		"adr": "adr x9, here\nhere:", "adrp": "adrp x9, here\nhere:",
		"bfc": "mov x9, x0\n  bfc x9, #4, #8", "bfm": "mov x9, x0\n  bfm x9, x1, #4, #8", "sbfm": "sbfm x9, x0, #4, #8", "ubfm": "ubfm x9, x0, #4, #8",
		"lslv": "lslv x9, x0, x1", "lsrv": "lsrv x9, x0, x1", "asrv": "asrv x9, x0, x1", "rorv": "rorv x9, x0, x1", "bfxil": "mov x9, x0\n  bfxil x9, x1, #4, #8", "sbfiz": "sbfiz x9, x0, #4, #8", "smnegl": "smnegl x9, w0, w1", "umnegl": "umnegl x9, w0, w1",
	}
	// Memory through the frame and a span parameter, and the atomics.
	frame := map[string]string{
		"ldr": "str x0, [sp, #-16]!\n  ldr x9, [sp], #16", "str": "str x0, [sp, #-16]!\n  ldr x9, [sp], #16", "ldp": "stp x0, x1, [sp, #-16]!\n  ldp x9, x10, [sp], #16", "stp": "stp x0, x1, [sp, #-16]!\n  ldp x9, x10, [sp], #16",
		"ldrb": "str x0, [sp, #-16]!\n  ldrb w9, [sp]\n  add sp, sp, #16", "ldrh": "str x0, [sp, #-16]!\n  ldrh w9, [sp]\n  add sp, sp, #16", "strb": "sub sp, sp, #16\n  strb w0, [sp]\n  add sp, sp, #16", "strh": "sub sp, sp, #16\n  strh w0, [sp]\n  add sp, sp, #16",
		"ldrsb": "str x0, [sp, #-16]!\n  ldrsb x9, [sp]\n  add sp, sp, #16", "ldrsh": "str x0, [sp, #-16]!\n  ldrsh x9, [sp]\n  add sp, sp, #16", "ldrsw": "str x0, [sp, #-16]!\n  ldrsw x9, [sp]\n  add sp, sp, #16", "ldpsw": "stp x0, x1, [sp, #-16]!\n  ldpsw x9, x10, [sp]\n  add sp, sp, #16",
		"ldur": "str x0, [sp, #-16]!\n  ldur x9, [sp, #0]\n  add sp, sp, #16", "stur": "sub sp, sp, #16\n  stur x0, [sp, #8]\n  add sp, sp, #16", "ldurb": "str x0, [sp, #-16]!\n  ldurb w9, [sp]\n  add sp, sp, #16", "ldurh": "str x0, [sp, #-16]!\n  ldurh w9, [sp]\n  add sp, sp, #16",
		"sturb": "sub sp, sp, #16\n  sturb w0, [sp]\n  add sp, sp, #16", "sturh": "sub sp, sp, #16\n  sturh w0, [sp]\n  add sp, sp, #16", "ldursb": "str x0, [sp, #-16]!\n  ldursb x9, [sp]\n  add sp, sp, #16", "ldursh": "str x0, [sp, #-16]!\n  ldursh x9, [sp]\n  add sp, sp, #16", "ldursw": "str x0, [sp, #-16]!\n  ldursw x9, [sp]\n  add sp, sp, #16",
		"prfm": "sub sp, sp, #16\n  prfm pldl1keep, [sp]\n  add sp, sp, #16", "prfum": "sub sp, sp, #16\n  prfum pldl1keep, [sp]\n  add sp, sp, #16", "rprfm": "sub sp, sp, #16\n  rprfm pldkeep, x0, [sp]\n  add sp, sp, #16",
		"ldnp": "stp x0, x1, [sp, #-16]!\n  ldnp x9, x10, [sp]\n  add sp, sp, #16", "stnp": "sub sp, sp, #16\n  stnp x0, x1, [sp]\n  add sp, sp, #16",
		"ldtr": "str x0, [sp, #-16]!\n  ldtr x9, [sp]\n  add sp, sp, #16", "ldtrb": "str x0, [sp, #-16]!\n  ldtrb w9, [sp]\n  add sp, sp, #16", "ldtrh": "str x0, [sp, #-16]!\n  ldtrh w9, [sp]\n  add sp, sp, #16",
		"ldtrsb": "str x0, [sp, #-16]!\n  ldtrsb x9, [sp]\n  add sp, sp, #16", "ldtrsh": "str x0, [sp, #-16]!\n  ldtrsh x9, [sp]\n  add sp, sp, #16", "ldtrsw": "str x0, [sp, #-16]!\n  ldtrsw x9, [sp]\n  add sp, sp, #16",
		"sttr": "sub sp, sp, #16\n  sttr x0, [sp]\n  add sp, sp, #16", "sttrb": "sub sp, sp, #16\n  sttrb w0, [sp]\n  add sp, sp, #16", "sttrh": "sub sp, sp, #16\n  sttrh w0, [sp]\n  add sp, sp, #16",
	}
	span := map[string]string{
		"ldxp": "ldxp x9, x10, [x2]", "ldaxp": "ldaxp x9, x10, [x2]", "stxp": "stxp w9, x0, x1, [x2]", "stlxp": "stlxp w9, x0, x1, [x2]",
		"ldraa": "ldraa x9, [x2]", "ldrab": "ldrab x9, [x2]", "stllr": "stllr x0, [x2]", "stllrb": "stllrb w0, [x2]", "stllrh": "stllrh w0, [x2]",
	}
	for _, order := range []string{"", "a", "l", "al"} {
		span["casp"+order] = "casp" + order + " x0, x1, x0, x1, [x2]"
	}
	for _, name := range []string{"ldar", "ldxr", "ldaxr", "ldapr", "ldlar"} {
		span[name] = name + " x9, [x2]"
		span[name+"b"] = name + "b w9, [x2]"
		span[name+"h"] = name + "h w9, [x2]"
	}
	span["stlr"], span["stlrb"], span["stlrh"] = "stlr x0, [x2]", "stlrb w0, [x2]", "stlrh w0, [x2]"
	for _, name := range []string{"stxr", "stlxr"} {
		span[name] = name + " w9, x0, [x2]"
		span[name+"b"] = name + "b w9, w0, [x2]"
		span[name+"h"] = name + "h w9, w0, [x2]"
	}
	for _, base := range atomicBases {
		if base == "casp" {
			continue
		}
		for _, order := range []string{"", "a", "l", "al"} {
			if strings.HasPrefix(base, "st") {
				// The store-only forms read one register and write none.
				span[base+order] = base + order + " x0, [x2]"
				span[base+order+"b"] = base + order + "b w0, [x2]"
				span[base+order+"h"] = base + order + "h w0, [x2]"
				continue
			}
			// cas reads both registers; the others read the first and write the second.
			second := "x9"
			if base == "cas" {
				second = "x1"
			}
			span[base+order] = base + order + " x0, " + second + ", [x2]"
			span[base+order+"b"] = base + order + "b w0, " + strings.Replace(second, "x", "w", 1) + ", [x2]"
			span[base+order+"h"] = base + order + "h w0, " + strings.Replace(second, "x", "w", 1) + ", [x2]"
		}
	}
	// Floating point and NEON: scalar views seeded from the general
	// registers, vectors from dup.
	fpPrologue := "  fmov d1, x0\n  fmov d2, x1\n  fmov s3, w0\n  fmov s4, w1\n  dup v5.4s, w0\n  dup v6.4s, w1\n  dup v7.16b, w0\n  dup v16.2d, x0\n  dup v17.8h, w1\n  "
	fp := map[string]string{
		"fmov": "fmov d0, d1", "fadd": "fadd d0, d1, d2", "fsub": "fsub d0, d1, d2", "fmul": "fmul s0, s3, s4", "fdiv": "fdiv d0, d1, d2", "fnmul": "fnmul d0, d1, d2", "fmax": "fmax d0, d1, d2", "fmin": "fmin d0, d1, d2", "fmaxnm": "fmaxnm d0, d1, d2", "fminnm": "fminnm d0, d1, d2",
		"fneg": "fneg d0, d1", "fabs": "fabs d0, d1", "fsqrt": "fsqrt d0, d1", "frinta": "frinta d0, d1", "frinti": "frinti d0, d1", "frintm": "frintm d0, d1", "frintn": "frintn d0, d1", "frintp": "frintp d0, d1", "frintx": "frintx d0, d1", "frintz": "frintz d0, d1",
		"fmadd": "fmadd d0, d1, d2, d1", "fmsub": "fmsub d0, d1, d2, d1", "fnmadd": "fnmadd d0, d1, d2, d1", "fnmsub": "fnmsub d0, d1, d2, d1",
		"fcmp": "fcmp d1, d2", "fcmpe": "fcmpe d1, #0.0", "fcsel": "fcmp d1, d2\n  fcsel d0, d1, d2, lo", "fcvt": "fcvt s0, d1",
		"fcvtzs": "fcvtzs x9, d1", "fcvtzu": "fcvtzu w9, s3", "fcvtas": "fcvtas x9, d1", "fcvtau": "fcvtau x9, d1", "fcvtms": "fcvtms x9, d1", "fcvtmu": "fcvtmu x9, d1", "fcvtns": "fcvtns x9, d1", "fcvtnu": "fcvtnu x9, d1", "fcvtps": "fcvtps x9, d1", "fcvtpu": "fcvtpu x9, d1",
		"scvtf": "scvtf d0, x0", "ucvtf": "ucvtf s0, w1", "fcvtn": "fcvtn v0.2s, v16.2d", "fcvtl": "fcvtl v0.2d, v5.2s",
		"facge": "facge v0.4s, v5.4s, v6.4s", "facgt": "facgt d0, d1, d2", "fmaxnmp": "fmaxnmp v0.4s, v5.4s, v6.4s", "fminnmp": "fminnmp d0, v16.2d", "frecpe": "frecpe d0, d1", "frsqrte": "frsqrte v0.4s, v5.4s", "frecpx": "frecpx d0, d1", "frecps": "frecps d0, d1, d2", "frsqrts": "frsqrts v0.4s, v5.4s, v6.4s",
		"fccmp": "fcmp d1, d2\n  fccmp d1, d2, #0, eq", "fccmpe": "fcmp d1, d2\n  fccmpe d1, d2, #4, ne", "fcvtxn": "fcvtxn v0.2s, v16.2d", "fcvtxn2": "mov v0.16b, v7.16b\n  fcvtxn2 v0.4s, v16.2d", "fcvtl2": "fcvtl2 v0.2d, v5.4s", "fcvtn2": "mov v0.16b, v7.16b\n  fcvtn2 v0.4s, v16.2d",
		"bif": "mov v0.16b, v7.16b\n  bif v0.16b, v7.16b, v7.16b", "bit": "mov v0.16b, v7.16b\n  bit v0.16b, v7.16b, v7.16b", "bsl": "mov v0.16b, v7.16b\n  bsl v0.16b, v7.16b, v7.16b",
		"shsub": "shsub v0.4s, v5.4s, v6.4s", "uhsub": "uhsub v0.4s, v5.4s, v6.4s", "srhadd": "srhadd v0.4s, v5.4s, v6.4s", "urhadd": "urhadd v0.4s, v5.4s, v6.4s", "saba": "mov v0.16b, v7.16b\n  saba v0.4s, v5.4s, v6.4s", "uaba": "mov v0.16b, v7.16b\n  uaba v0.4s, v5.4s, v6.4s",
		"sqabs": "sqabs v0.4s, v5.4s", "sqneg": "sqneg d0, d1", "suqadd": "mov v0.16b, v7.16b\n  suqadd v0.4s, v5.4s", "usqadd": "mov v0.16b, v7.16b\n  usqadd v0.4s, v5.4s", "urecpe": "urecpe v0.4s, v5.4s", "ursqrte": "ursqrte v0.4s, v5.4s",
		"sqdmulh": "sqdmulh v0.4s, v5.4s, v6.4s", "sqrdmulh": "sqrdmulh s0, s3, s4", "sqrdmlah": "mov v0.16b, v7.16b\n  sqrdmlah v0.4s, v5.4s, v6.4s", "sqrdmlsh": "mov v0.16b, v7.16b\n  sqrdmlsh v0.4s, v5.4s, v6.4s",
		"sqdmlal": "mov v0.16b, v7.16b\n  sqdmlal v0.4s, v17.4h, v17.4h", "sqdmlsl": "mov v0.16b, v7.16b\n  sqdmlsl v0.4s, v17.4h, v17.4h", "sqdmull": "sqdmull v0.4s, v17.4h, v17.4h",
		"sqdmlal2": "mov v0.16b, v7.16b\n  sqdmlal2 v0.4s, v17.8h, v17.8h", "sqdmlsl2": "mov v0.16b, v7.16b\n  sqdmlsl2 v0.4s, v17.8h, v17.8h", "sqdmull2": "sqdmull2 v0.4s, v17.8h, v17.8h",
		"addhn": "addhn v0.4h, v5.4s, v6.4s", "raddhn": "raddhn v0.4h, v5.4s, v6.4s", "subhn": "subhn v0.4h, v5.4s, v6.4s", "rsubhn": "rsubhn v0.4h, v5.4s, v6.4s",
		"addhn2": "mov v0.16b, v7.16b\n  addhn2 v0.8h, v5.4s, v6.4s", "raddhn2": "mov v0.16b, v7.16b\n  raddhn2 v0.8h, v5.4s, v6.4s", "subhn2": "mov v0.16b, v7.16b\n  subhn2 v0.8h, v5.4s, v6.4s", "rsubhn2": "mov v0.16b, v7.16b\n  rsubhn2 v0.8h, v5.4s, v6.4s",
		"sabal": "mov v0.16b, v7.16b\n  sabal v0.4s, v17.4h, v17.4h", "uabal": "mov v0.16b, v7.16b\n  uabal v0.4s, v17.4h, v17.4h", "sabal2": "mov v0.16b, v7.16b\n  sabal2 v0.4s, v17.8h, v17.8h", "uabal2": "mov v0.16b, v7.16b\n  uabal2 v0.4s, v17.8h, v17.8h",
		"sabdl": "sabdl v0.4s, v17.4h, v17.4h", "uabdl": "uabdl v0.4s, v17.4h, v17.4h", "sabdl2": "sabdl2 v0.4s, v17.8h, v17.8h", "uabdl2": "uabdl2 v0.4s, v17.8h, v17.8h",
		"saddw2": "saddw2 v0.4s, v5.4s, v17.8h", "uaddw2": "uaddw2 v0.4s, v5.4s, v17.8h", "ssubw2": "ssubw2 v0.4s, v5.4s, v17.8h", "usubw2": "usubw2 v0.4s, v5.4s, v17.8h", "ssubl2": "ssubl2 v0.4s, v17.8h, v17.8h", "usubl2": "usubl2 v0.4s, v17.8h, v17.8h",
		"smlal2": "mov v0.16b, v7.16b\n  smlal2 v0.4s, v17.8h, v17.8h", "umlal2": "mov v0.16b, v7.16b\n  umlal2 v0.4s, v17.8h, v17.8h", "smlsl2": "mov v0.16b, v7.16b\n  smlsl2 v0.4s, v17.8h, v17.8h", "umlsl2": "mov v0.16b, v7.16b\n  umlsl2 v0.4s, v17.8h, v17.8h",
		"sqrshl": "sqrshl v0.4s, v5.4s, v6.4s", "uqrshl": "uqrshl d0, d1, d2", "srshr": "srshr v0.4s, v5.4s, #3", "urshr": "urshr d0, d1, #3", "srsra": "mov v0.16b, v7.16b\n  srsra v0.4s, v5.4s, #3", "ursra": "mov v0.16b, v7.16b\n  ursra v0.4s, v5.4s, #3", "sqshlu": "sqshlu v0.4s, v5.4s, #3",
		"sshll2": "sshll2 v0.4s, v17.8h, #0", "ushll2": "ushll2 v0.4s, v17.8h, #0", "shll2": "shll2 v0.4s, v17.8h, #16",
		"shrn2": "mov v0.16b, v7.16b\n  shrn2 v0.8h, v5.4s, #8", "rshrn2": "mov v0.16b, v7.16b\n  rshrn2 v0.8h, v5.4s, #8", "sqshrn2": "mov v0.16b, v7.16b\n  sqshrn2 v0.8h, v5.4s, #8", "uqshrn2": "mov v0.16b, v7.16b\n  uqshrn2 v0.8h, v5.4s, #8",
		"sqrshrn2": "mov v0.16b, v7.16b\n  sqrshrn2 v0.8h, v5.4s, #8", "uqrshrn2": "mov v0.16b, v7.16b\n  uqrshrn2 v0.8h, v5.4s, #8", "sqshrun2": "mov v0.16b, v7.16b\n  sqshrun2 v0.8h, v5.4s, #8", "sqrshrun2": "mov v0.16b, v7.16b\n  sqrshrun2 v0.8h, v5.4s, #8",
		"sqshrun": "sqshrun v0.4h, v5.4s, #8", "sqrshrun": "sqrshrun v0.4h, v5.4s, #8", "sqxtun2": "mov v0.16b, v7.16b\n  sqxtun2 v0.8h, v5.4s",
		"ld2r": "cmp w3, #2\n  b.lo short\n  ld2r {v0.2d, v1.2d}, [x2]\n  mov x0, #0\n  ret\nshort:", "ld3r": "cmp w3, #3\n  b.lo short\n  ld3r {v0.2d, v1.2d, v2.2d}, [x2]\n  mov x0, #0\n  ret\nshort:", "ld4r": "cmp w3, #4\n  b.lo short\n  ld4r {v0.2d, v1.2d, v2.2d, v3.2d}, [x2]\n  mov x0, #0\n  ret\nshort:",
		"mla": "mla v0.4s, v5.4s, v6.4s", "mls": "mls v0.4s, v5.4s, v6.4s", "smax": "smax v0.4s, v5.4s, v6.4s", "smin": "smin v0.4s, v5.4s, v6.4s", "umax": "umax v0.4s, v5.4s, v6.4s", "umin": "umin v0.4s, v5.4s, v6.4s",
		"sabd": "sabd v0.4s, v5.4s, v6.4s", "uabd": "uabd v0.4s, v5.4s, v6.4s", "shadd": "shadd v0.4s, v5.4s, v6.4s", "uhadd": "uhadd v0.4s, v5.4s, v6.4s", "sqadd": "sqadd v0.4s, v5.4s, v6.4s", "uqadd": "uqadd v0.4s, v5.4s, v6.4s", "sqsub": "sqsub v0.4s, v5.4s, v6.4s", "uqsub": "uqsub v0.4s, v5.4s, v6.4s",
		"addp": "addp v0.4s, v5.4s, v6.4s", "smaxp": "smaxp v0.4s, v5.4s, v6.4s", "sminp": "sminp v0.4s, v5.4s, v6.4s", "umaxp": "umaxp v0.4s, v5.4s, v6.4s", "uminp": "uminp v0.4s, v5.4s, v6.4s", "pmul": "pmul v0.16b, v7.16b, v7.16b",
		"fmla": "fmla v0.4s, v5.4s, v6.4s", "fmls": "fmls v0.4s, v5.4s, v6.4s", "fmulx": "fmulx v0.4s, v5.4s, v6.4s", "fabd": "fabd v0.4s, v5.4s, v6.4s", "fmaxp": "fmaxp v0.4s, v5.4s, v6.4s", "fminp": "fminp v0.4s, v5.4s, v6.4s", "faddp": "faddp v0.4s, v5.4s, v6.4s",
		"not": "not v0.16b, v7.16b", "abs": "abs v0.4s, v5.4s", "cnt": "cnt v0.16b, v7.16b", "rev64": "rev64 v0.4s, v5.4s",
		"cmeq": "cmeq v0.4s, v5.4s, v6.4s", "cmgt": "cmgt v0.4s, v5.4s, #0", "cmge": "cmge v0.4s, v5.4s, v6.4s", "cmhi": "cmhi v0.4s, v5.4s, v6.4s", "cmhs": "cmhs v0.4s, v5.4s, v6.4s", "cmtst": "cmtst v0.4s, v5.4s, v6.4s", "cmlt": "cmlt v0.4s, v5.4s, #0", "cmle": "cmle v0.4s, v5.4s, #0",
		"fcmeq": "fcmeq v0.4s, v5.4s, v6.4s", "fcmgt": "fcmgt v0.4s, v5.4s, #0.0", "fcmge": "fcmge v0.4s, v5.4s, v6.4s", "fcmlt": "fcmlt v0.4s, v5.4s, #0.0", "fcmle": "fcmle v0.4s, v5.4s, #0.0",
		"addv": "addv s0, v5.4s", "smaxv": "smaxv s0, v5.4s", "sminv": "sminv s0, v5.4s", "umaxv": "umaxv s0, v5.4s", "uminv": "uminv s0, v5.4s", "fmaxv": "fmaxv s0, v5.4s", "fminv": "fminv s0, v5.4s", "fmaxnmv": "fmaxnmv s0, v5.4s", "fminnmv": "fminnmv s0, v5.4s", "saddlv": "saddlv d0, v5.4s", "uaddlv": "uaddlv d0, v5.4s",
		"shl": "shl v0.4s, v5.4s, #3", "ushr": "ushr v0.4s, v5.4s, #3", "sshr": "sshr v0.4s, v5.4s, #3", "sli": "sli v0.4s, v5.4s, #3", "sri": "sri v0.4s, v5.4s, #3", "ssra": "ssra v0.4s, v5.4s, #3", "usra": "usra v0.4s, v5.4s, #3",
		"shrn": "shrn v0.4h, v5.4s, #8", "rshrn": "rshrn v0.4h, v5.4s, #8", "sqshrn": "sqshrn v0.4h, v5.4s, #8", "uqshrn": "uqshrn v0.4h, v5.4s, #8", "sqrshrn": "sqrshrn v0.4h, v5.4s, #8", "uqrshrn": "uqrshrn v0.4h, v5.4s, #8",
		"sxtl": "sxtl v0.4s, v17.4h", "uxtl": "uxtl v0.4s, v17.4h", "sxtl2": "sxtl2 v0.4s, v17.8h", "uxtl2": "uxtl2 v0.4s, v17.8h",
		"ushll": "ushll v0.4s, v17.4h, #0", "sshll": "sshll v0.4s, v17.4h, #0", "shll": "shll v0.4s, v17.4h, #16", "uqshl": "uqshl v0.4s, v5.4s, #3", "sqshl": "sqshl v0.4s, v5.4s, #3",
		"ushl": "ushl v0.4s, v5.4s, v6.4s", "sshl": "sshl v0.4s, v5.4s, v6.4s", "urshl": "urshl v0.4s, v5.4s, v6.4s", "srshl": "srshl v0.4s, v5.4s, v6.4s",
		"xtn": "xtn v0.4h, v5.4s", "sqxtn": "sqxtn v0.4h, v5.4s", "uqxtn": "uqxtn v0.4h, v5.4s", "sqxtun": "sqxtun v0.4h, v5.4s", "xtn2": "mov v0.16b, v7.16b\n  xtn2 v0.8h, v5.4s", "sqxtn2": "mov v0.16b, v7.16b\n  sqxtn2 v0.8h, v5.4s", "uqxtn2": "mov v0.16b, v7.16b\n  uqxtn2 v0.8h, v5.4s",
		"uaddlp": "uaddlp v0.2d, v5.4s", "saddlp": "saddlp v0.2d, v5.4s", "uadalp": "mov v0.16b, v7.16b\n  uadalp v0.2d, v5.4s", "sadalp": "mov v0.16b, v7.16b\n  sadalp v0.2d, v5.4s",
		"uaddl": "uaddl v0.4s, v17.4h, v17.4h", "saddl": "saddl v0.4s, v17.4h, v17.4h", "usubl": "usubl v0.4s, v17.4h, v17.4h", "ssubl": "ssubl v0.4s, v17.4h, v17.4h", "umlal": "mov v0.16b, v7.16b\n  umlal v0.4s, v17.4h, v17.4h", "smlal": "mov v0.16b, v7.16b\n  smlal v0.4s, v17.4h, v17.4h", "umlsl": "mov v0.16b, v7.16b\n  umlsl v0.4s, v17.4h, v17.4h", "smlsl": "mov v0.16b, v7.16b\n  smlsl v0.4s, v17.4h, v17.4h",
		"uaddw": "uaddw v0.4s, v5.4s, v17.4h", "saddw": "saddw v0.4s, v5.4s, v17.4h", "usubw": "usubw v0.4s, v5.4s, v17.4h", "ssubw": "ssubw v0.4s, v5.4s, v17.4h", "uaddl2": "uaddl2 v0.4s, v17.8h, v17.8h", "saddl2": "saddl2 v0.4s, v17.8h, v17.8h", "umull2": "umull2 v0.4s, v17.8h, v17.8h", "smull2": "smull2 v0.4s, v17.8h, v17.8h",
		"dup": "dup v0.4s, w0", "ins": "mov v0.16b, v7.16b\n  ins v0.s[1], w0", "umov": "umov w9, v5.s[1]", "smov": "smov x9, v5.s[1]",
		"ext": "ext v0.16b, v7.16b, v7.16b, #3", "tbl": "tbl v0.16b, {v7.16b}, v7.16b", "tbx": "mov v0.16b, v7.16b\n  tbx v0.16b, {v7.16b}, v7.16b",
		"zip1": "zip1 v0.4s, v5.4s, v6.4s", "zip2": "zip2 v0.4s, v5.4s, v6.4s", "uzp1": "uzp1 v0.4s, v5.4s, v6.4s", "uzp2": "uzp2 v0.4s, v5.4s, v6.4s", "trn1": "trn1 v0.4s, v5.4s, v6.4s", "trn2": "trn2 v0.4s, v5.4s, v6.4s",
		"movi": "movi v0.4s, #1", "mvni": "mvni v0.4s, #1",
		"ld1": "cmp w3, #2\n  b.lo short\n  ld1 {v0.2d}, [x2]\n  mov x0, #0\n  ret\nshort:", "st1": "cmp w3, #2\n  b.lo short\n  st1 {v16.2d}, [x2]\n  mov x0, #0\n  ret\nshort:", "ld1r": "cmp w3, #1\n  b.lo short\n  ld1r {v0.2d}, [x2]\n  mov x0, #0\n  ret\nshort:",
		"ld2": "cmp w3, #4\n  b.lo short\n  ld2 {v0.2d, v1.2d}, [x2]\n  mov x0, #0\n  ret\nshort:", "st2": "cmp w3, #4\n  b.lo short\n  st2 {v16.2d, v17.2d}, [x2]\n  mov x0, #0\n  ret\nshort:",
		"ld3": "cmp w3, #6\n  b.lo short\n  ld3 {v0.2d, v1.2d, v2.2d}, [x2]\n  mov x0, #0\n  ret\nshort:", "st3": "cmp w3, #6\n  b.lo short\n  st3 {v16.2d, v17.2d, v18.2d}, [x2]\n  mov x0, #0\n  ret\nshort:",
		"ld4": "cmp w3, #8\n  b.lo short\n  ld4 {v0.2d, v1.2d, v2.2d, v3.2d}, [x2]\n  mov x0, #0\n  ret\nshort:", "st4": "cmp w3, #8\n  b.lo short\n  st4 {v16.2d, v17.2d, v18.2d, v19.2d}, [x2]\n  mov x0, #0\n  ret\nshort:",
	}
	apple := map[string]string{
		"pacia": "pacia x9, x0", "pacib": "pacib x9, x0", "pacda": "pacda x9, x0", "pacdb": "pacdb x9, x0", "autia": "autia x9, x0", "autib": "autib x9, x0", "autda": "autda x9, x0", "autdb": "autdb x9, x0",
		"paciza": "mov x9, x0\n  paciza x9", "pacizb": "mov x9, x0\n  pacizb x9", "pacdza": "mov x9, x0\n  pacdza x9", "pacdzb": "mov x9, x0\n  pacdzb x9", "autiza": "mov x9, x0\n  autiza x9", "autizb": "mov x9, x0\n  autizb x9", "autdza": "mov x9, x0\n  autdza x9", "autdzb": "mov x9, x0\n  autdzb x9", "xpaci": "mov x9, x0\n  xpaci x9", "xpacd": "mov x9, x0\n  xpacd x9",
		"paciasp": "paciasp", "pacibsp": "pacibsp", "autiasp": "autiasp", "autibsp": "autibsp", "paciaz": "paciaz", "pacibz": "pacibz", "autiaz": "autiaz", "autibz": "autibz", "pacia1716": "pacia1716", "pacib1716": "pacib1716", "autia1716": "autia1716", "autib1716": "autib1716", "xpaclri": "xpaclri",
		"pacga": "pacga x9, x0, x1",
		"bti":   "bti c", "sb": "sb", "dgh": "dgh", "wfet": "wfet x0", "wfit": "wfit x0",
		"setf8": "setf8 w0", "setf16": "setf16 w0", "rmif": "cmp x0, x1\n  rmif x0, #3, #15", "axflag": "cmp x0, x1\n  axflag", "xaflag": "cmp x0, x1\n  xaflag",
		"fjcvtzs": "fjcvtzs w9, d1",
		"sdot":    "sdot v0.4s, v7.16b, v7.16b", "udot": "udot v0.4s, v7.16b, v7.16b", "usdot": "usdot v0.4s, v7.16b, v7.16b", "sudot": "sudot v0.4s, v7.16b, v7.4b[1]", "bfdot": "bfdot v0.4s, v17.8h, v17.8h",
		"smmla": "smmla v0.4s, v7.16b, v7.16b", "ummla": "ummla v0.4s, v7.16b, v7.16b", "usmmla": "usmmla v0.4s, v7.16b, v7.16b", "bfmmla": "bfmmla v0.4s, v17.8h, v17.8h",
		"bfmlalb": "bfmlalb v0.4s, v17.8h, v17.8h", "bfmlalt": "bfmlalt v0.4s, v17.8h, v17.8h", "bfcvt": "bfcvt h0, s3", "bfcvtn": "bfcvtn v0.4h, v5.4s", "bfcvtn2": "mov v0.16b, v7.16b\n  bfcvtn2 v0.8h, v5.4s",
		"fmlal": "fmlal v0.4s, v17.4h, v17.4h", "fmlsl": "fmlsl v0.4s, v17.4h, v17.4h", "fmlal2": "fmlal2 v0.4s, v17.4h, v17.4h", "fmlsl2": "fmlsl2 v0.4s, v17.4h, v17.4h",
		"fcadd": "fcadd v0.4s, v5.4s, v6.4s, #90", "fcmla": "fcmla v0.4s, v5.4s, v6.4s, #180",
		"frint32z": "frint32z d0, d1", "frint32x": "frint32x v0.4s, v5.4s", "frint64z": "frint64z s0, s3", "frint64x": "frint64x d0, d1",
		"aese": "aese v0.16b, v7.16b", "aesd": "aesd v0.16b, v7.16b", "aesmc": "aesmc v0.16b, v7.16b", "aesimc": "aesimc v0.16b, v7.16b",
		"sha1c": "sha1c q0, s3, v5.4s", "sha1p": "sha1p q0, s3, v5.4s", "sha1m": "sha1m q0, s3, v5.4s", "sha1h": "sha1h s0, s3", "sha1su0": "sha1su0 v0.4s, v5.4s, v6.4s", "sha1su1": "sha1su1 v0.4s, v5.4s",
		"sha256h": "fmov d0, x0\n  sha256h q0, q0, v5.4s", "sha256h2": "fmov d0, x0\n  sha256h2 q0, q0, v5.4s", "sha256su0": "sha256su0 v0.4s, v5.4s", "sha256su1": "sha256su1 v0.4s, v5.4s, v6.4s",
		"sha512h": "fmov d0, x0\n  sha512h q0, q0, v16.2d", "sha512h2": "fmov d0, x0\n  sha512h2 q0, q0, v16.2d", "sha512su0": "sha512su0 v0.2d, v16.2d", "sha512su1": "sha512su1 v0.2d, v16.2d, v16.2d",
		"eor3": "eor3 v0.16b, v7.16b, v7.16b, v7.16b", "bcax": "bcax v0.16b, v7.16b, v7.16b, v7.16b", "rax1": "rax1 v0.2d, v16.2d, v16.2d", "xar": "xar v0.2d, v16.2d, v16.2d, #7", "pmull": "pmull v0.1q, v16.1d, v16.1d", "pmull2": "pmull2 v0.1q, v16.2d, v16.2d",
		"ldapur": "cmp w3, #1\n  b.lo short\n  ldapur x9, [x2]\n  mov x0, #0\n  ret\nshort:", "ldapurb": "cmp w3, #1\n  b.lo short\n  ldapurb w9, [x2]\n  mov x0, #0\n  ret\nshort:", "ldapurh": "cmp w3, #1\n  b.lo short\n  ldapurh w9, [x2]\n  mov x0, #0\n  ret\nshort:",
		"ldapursb": "cmp w3, #1\n  b.lo short\n  ldapursb x9, [x2]\n  mov x0, #0\n  ret\nshort:", "ldapursh": "cmp w3, #1\n  b.lo short\n  ldapursh x9, [x2]\n  mov x0, #0\n  ret\nshort:", "ldapursw": "cmp w3, #1\n  b.lo short\n  ldapursw x9, [x2]\n  mov x0, #0\n  ret\nshort:",
		"stlur": "cmp w3, #1\n  b.lo short\n  stlur x0, [x2]\n  mov x0, #0\n  ret\nshort:", "stlurb": "cmp w3, #1\n  b.lo short\n  stlurb w0, [x2]\n  mov x0, #0\n  ret\nshort:", "stlurh": "cmp w3, #1\n  b.lo short\n  stlurh w0, [x2]\n  mov x0, #0\n  ret\nshort:",
		"retaa": "mov x0, #0\n  retaa", "retab": "mov x0, #0\n  retab", "braa": "braa x1, x0", "brab": "brab x1, x0", "braaz": "braaz x1", "brabz": "brabz x1",
		"blraa": "str x30, [sp, #-16]!\n  blraa x1, x0\n  ldr x30, [sp], #16", "blrab": "str x30, [sp, #-16]!\n  blrab x1, x0\n  ldr x30, [sp], #16", "blraaz": "str x30, [sp, #-16]!\n  blraaz x1\n  ldr x30, [sp], #16", "blrabz": "str x30, [sp, #-16]!\n  blrabz x1\n  ldr x30, [sp], #16",
	}
	system := map[string]string{
		"mrs": "mrs x9, cntvct_el0", "msr": "msr cntvoff_el2, x0", "dc": "dc civac, x0", "ic": "ic iallu", "tlbi": "tlbi vmalle1is", "at": "at s1e1r, x0",
		"cfp": "cfp rctx, x0", "cpp": "cpp rctx, x0", "dvp": "dvp rctx, x0",
		"svc": "svc #0", "hvc": "hvc #0", "smc": "smc #0",
	}
	control := map[string]string{
		"b": "b done\ndone:\n  mov x0, #0", "b.": "cmp x0, x1\n  b.lo done\ndone:\n  mov x0, #0", "cbz": "cbz x0, done\ndone:\n  mov x0, #0", "cbnz": "cbnz x0, done\ndone:\n  mov x0, #0",
		"tbz": "tbz x0, #3, done\ndone:\n  mov x0, #0", "tbnz": "tbnz x0, #3, done\ndone:\n  mov x0, #0", "bl": "bl helper", "blr": "blr x1", "br": "br x1", "ret": "ret", "eret": "eret", "eretaa": "eretaa", "eretab": "eretab", "brk": "brk #1",
	}
	names := make([]string, 0, len(instructionTable))
	for name := range instructionTable {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		if spec := instructionTable[name]; spec.tableForms && len(spec.forms) == 0 {
			continue // SVE/SME: covered by the generated table's differential (sme_test.go)
		}
		body, decl := "", "f: (a, b: u64, s: [*]u64) -> u64"
		prologue, epilogue := "  bind x0 = a\n  bind x1 = b\n  bind x2, w3 = s\n  clobber x9, x10, x30\n  frame 16\n", "\n  mov x0, #0\n  ret"
		switch {
		case apple[name] != "":
			prologue += "  clobber v0, v1, v2, v3, v4, v5, v6, v7, v16, v17, v18, v19\n"
			body = fpPrologue + apple[name]
			switch name {
			case "retaa", "retab", "braa", "brab", "braaz", "brabz", "ldapur", "ldapurb", "ldapurh", "ldapursb", "ldapursh", "ldapursw", "stlur", "stlurb", "stlurh":
				epilogue = "\n  mov x0, #0\n  ret"
				if strings.HasPrefix(name, "ret") || strings.HasPrefix(name, "bra") || strings.HasPrefix(name, "brb") {
					epilogue = ""
				}
			}
		case fp[name] != "":
			prologue += "  clobber v0, v1, v2, v3, v4, v5, v6, v7, v16, v17, v18, v19\n"
			body = fpPrologue + fp[name]
		case samples[name] != "":
			body = "  " + samples[name]
		case frame[name] != "":
			body = "  " + frame[name]
		case span[name] != "":
			body = "  cmp w3, #2\n  b.lo short\n  " + span[name] + "\n  mov x0, #0\n  ret\nshort:\n  mov x0, #0\n  ret"
			epilogue = ""
		case system[name] != "":
			prologue = "  system\n" + prologue
			body = "  " + system[name]
		case control[name] != "":
			body = "  " + control[name]
			switch name {
			case "br":
				body = "  br x1"
				epilogue = ""
			case "ret":
				body = "  mov x0, #0\n  ret"
				epilogue = ""
			case "eret", "eretaa", "eretab":
				decl = "f: (a, b: u64, s: [*]u64) -> never"
				prologue = "  system\n" + prologue
				epilogue = ""
			case "brk":
				epilogue = ""
			case "bl", "blr":
				body = "  str x30, [sp, #-16]!\n  " + control[name] + "\n  ldr x30, [sp], #16"
			}
		default:
			t.Errorf("no coverage sample for %s", name)
			continue
		}
		unit, errs := ParseUnit("cov.oakasm", decl+" = {\n"+prologue+body+epilogue+"\n}\n")
		if len(errs) != 0 {
			t.Errorf("%s: parse: %v", name, errs)
			continue
		}
		sig, err := parseSignature(decl)
		if err != nil {
			t.Fatal(err)
		}
		if findings := Check(unit.Functions[0], sig, map[string]bool{"helper": true}); len(findings) != 0 {
			t.Errorf("%s: checker rejected the sample: %v", name, findings)
		}
		// Round trip through the emitter: every operand renders.
		for _, item := range unit.Functions[0].Items {
			if instr, isInstr := item.(Instruction); isInstr {
				if text := renderInstruction(unit.Functions[0], instr, func(s string) string { return s }, map[string]int{}, map[string]bool{}); strings.Contains(text, "?") {
					t.Errorf("%s: operand failed to render: %q", name, text)
				}
			}
		}
	}
}

// The verifier's semantics for the modeled groups.
func TestVerifyGeneralPurposeISA(t *testing.T) {
	cases := []struct{ name, decl, oak, asm string }{
		{"shifted operand", "f: (a, b: u32) -> u32", "a + (b << u32(3))", "  bind w0 = a\n  bind w1 = b\n  add w0, w0, w1, lsl #3\n  ret"},
		{"extended operand", "f: (a: u64, b: u32) -> u64", "a + (u64(b) << u64(2))", "  bind x0 = a\n  bind w1 = b\n  add x0, x0, w1, uxtw #2\n  ret"},
		{"bic", "f: (a, b: u32) -> u32", "a & ^b", "  bind w0 = a\n  bind w1 = b\n  bic w0, w0, w1\n  ret"},
		{"orn", "f: (a, b: u32) -> u32", "a | ^b", "  bind w0 = a\n  bind w1 = b\n  orn w0, w0, w1\n  ret"},
		{"eon", "f: (a, b: u32) -> u32", "a ^ ^b", "  bind w0 = a\n  bind w1 = b\n  eon w0, w0, w1\n  ret"},
		{"ror", "f: (a: u32) -> u32", "(a >> u32(8)) | (a << u32(24))", "  bind w0 = a\n  ror w0, w0, #8\n  ret"},
		{"extr", "f: (hi, lo: u32) -> u32", "(lo >> u32(8)) | (hi << u32(24))", "  bind w0 = hi\n  bind w1 = lo\n  extr w0, w0, w1, #8\n  ret"},
		{"rev", "f: (a: u32) -> u32", "(a >> u32(24)) | ((a >> u32(8)) & u32(0xFF00)) | ((a << u32(8)) & u32(0xFF0000)) | (a << u32(24))", "  bind w0 = a\n  rev w0, w0\n  ret"},
		{"uxth", "f: (a: u32) -> u32", "a & u32(0xFFFF)", "  bind w0 = a\n  uxth w0, w0\n  ret"},
		{"sxtb as arithmetic", "f: (a: u32) -> u32", "(a & u32(0xFF)) ^ (((a >> u32(7)) & u32(1)) * u32(0xFFFFFF00))", "  bind w0 = a\n  sxtb w0, w0\n  ret"},
		{"movz/movk", "f: () -> u64", "u64(0x1234) | (u64(0x5678) << u64(32))", "  movz x0, #0x1234\n  movk x0, #0x5678, lsl #32\n  ret"},
		{"movn", "f: () -> u32", "^u32(0x10)", "  movn w0, #0x10\n  ret"},
		{"csinc", "f: (a, b: u32) -> u32", "a < b ? a | b + u32(1)", "  bind w0 = a\n  bind w1 = b\n  cmp w0, w1\n  csinc w0, w0, w1, lo\n  ret"},
		{"csetm", "f: (a, b: u32) -> u32", "a == b ? u32(0xFFFFFFFF) | u32(0)", "  bind w0 = a\n  bind w1 = b\n  cmp w0, w1\n  csetm w0, eq\n  ret"},
		{"cmn", "f: (a, b: u32) -> Bool", "a + b == u32(0)", "  bind w0 = a\n  bind w1 = b\n  cmn w0, w1\n  cset w0, eq\n  ret"},
		{"adc carry chain", "f: (alo, ahi, blo, bhi: u32) -> u32", "ahi + bhi + (alo + blo < alo ? u32(1) | u32(0))", "  bind w0 = alo\n  bind w1 = ahi\n  bind w2 = blo\n  bind w3 = bhi\n  clobber w9\n  adds w9, w0, w2\n  adc w0, w1, w3\n  ret"},
		{"umull", "f: (a, b: u32) -> u64", "u64(a) * u64(b)", "  bind w0 = a\n  bind w1 = b\n  umull x0, w0, w1\n  ret"},
		{"ldrsw", "f: (v: []i32) -> i64", "len(v) == u32(0) ? i64(0) | i64(v[0])", "  bind x0, w1 = v\n  cmp w1, #1\n  b.lo empty\n  ldrsw x0, [x0]\n  ret\nempty:\n  mov x0, #0\n  ret"},
		{"clz", "f: (a: u32) -> u32", "a == u32(0) ? u32(32) | (a >> u32(31) == u32(1) ? u32(0) | (a >> u32(30) == u32(1) ? u32(1) | u32(2)))", "  bind w0 = a\n  clz w0, w0\n  ret"},
	}
	for _, c := range cases {
		verdict := verifyCase(t, c.decl, c.oak, c.asm)
		switch c.name {
		case "umull":
			// A symbolic 32×32 product is BDD-hard: evidence or proof.
			if verdict.Kind != VerdictProven && verdict.Kind != VerdictWitnessed {
				t.Fatalf("%s: must be proven or witness-checked, got %s: %s", c.name, verdict.Kind, verdict.Message)
			}
		case "clz":
			// The Oak spelling only covers a >= 2^29; elsewhere it differs — a
			// genuine mismatch the verifier must find.
			if verdict.Kind != VerdictMismatch {
				t.Fatalf("%s: the partial spelling must be a mismatch, got %s: %s", c.name, verdict.Kind, verdict.Message)
			}
		default:
			if verdict.Kind != VerdictProven {
				t.Fatalf("%s: must be proven, got %s: %s", c.name, verdict.Kind, verdict.Message)
			}
		}
	}
	// A full clz specification by a counted loop is proven.
	clz := verifyCase(t, "clz32: (a: u32) -> u32", "{\n  n: u32 = u32(0)\n  x: u32 = a\n  i: u32 = u32(0)\n  while i < u32(32) {\n    (x & u32(0x80000000)) == u32(0) && n == i ? { n = n + u32(1) } | { }\n    x = x << u32(1)\n    i = i + u32(1)\n  }\n  n\n}", "  bind w0 = a\n  clz w0, w0\n  ret")
	if clz.Kind != VerdictProven {
		t.Fatalf("clz against its loop specification must be proven, got %s: %s", clz.Kind, clz.Message)
	}
	// Division and the ordered/atomic accesses are outside the subset.
	div := verifyCase(t, "half: (a, b: u32) -> u32", "a", "  bind w0 = a\n  bind w1 = b\n  udiv w0, w0, w1\n  ret")
	if div.Kind == VerdictProven {
		t.Fatalf("udiv must not be proven against the identity: %s", div.Message)
	}
	atomic := verifyCase(t, "bump: (s: [*]u32) -> u32", "u32(0)", "  bind x0, w1 = s\n  clobber w9, w10\n  cmp w1, #1\n  b.lo short\n  mov w9, #1\n  ldadd w9, w10, [x0]\n  mov w0, w10\n  ret\nshort:\n  mov w0, #0\n  ret")
	if atomic.Kind != VerdictTrusted || !strings.Contains(atomic.Message, "atomic") {
		t.Fatalf("an atomic must be trusted, got %s: %s", atomic.Kind, atomic.Message)
	}
}

// Floating-point parameters bind to their scalar views; the checker keeps
// arrangements consistent and the verifier trusts vector bodies.
func TestFloatingPointContract(t *testing.T) {
	if findings := checkBody(t, "scale: (x: f32, k: f64) -> f64", "  bind s0 = x\n  bind d1 = k\n  clobber d2\n  fcvt d2, s0\n  fmul d0, d2, d1\n  ret"); len(findings) != 0 {
		t.Fatalf("an f32/f64 body must be accepted: %v", findings)
	}
	if findings := checkBody(t, "scale: (x: f32) -> f32", "  bind d0 = x\n  ret"); len(findings) == 0 || !strings.Contains(strings.Join(findings, "\n"), "arrives in s0") {
		t.Fatalf("binding f32 to d0 must be refused, got %v", findings)
	}
	if findings := checkBody(t, "mix: (a: u64) -> u64", "  bind x0 = a\n  clobber v0, v1\n  dup v0.4s, w0\n  dup v1.2d, x0\n  add v0.4s, v0.4s, v1.2d\n  ret"); len(findings) == 0 || !strings.Contains(strings.Join(findings, "\n"), "disagree") {
		t.Fatalf("mixed arrangements must be refused, got %v", findings)
	}
	if _, ok := parseRegister("v0.s[4]"); ok {
		t.Fatal("lane 4 of a .s view is past the register and must not parse")
	}
	trusted := verifyCase(t, "twice: (x: f64) -> f64", "x + x", "  bind d0 = x\n  fadd d0, d0, d0\n  ret")
	if trusted.Kind != VerdictTrusted {
		t.Fatalf("an FP body must be trusted, got %s: %s", trusted.Kind, trusted.Message)
	}
}
