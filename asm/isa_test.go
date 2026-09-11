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
		"sxtb": "sxtb x9, x0", "sxth": "sxth x9, x0", "sxtw": "sxtw x9, w0", "uxtb": "uxtb w9, w0", "uxth": "uxth w9, w0",
		"movz": "movz x9, #1, lsl #16", "movn": "movn x9, #1", "movk": "movz x9, #1\n  movk x9, #2, lsl #32",
		"mul": "mul x9, x0, x1", "madd": "madd x9, x0, x1, x0", "msub": "msub x9, x0, x1, x0", "mneg": "mneg x9, x0, x1", "smull": "smull x9, w0, w1", "umull": "umull x9, w0, w1",
		"smaddl": "smaddl x9, w0, w1, x0", "umaddl": "umaddl x9, w0, w1, x0", "smsubl": "smsubl x9, w0, w1, x0", "umsubl": "umsubl x9, w0, w1, x0", "smulh": "smulh x9, x0, x1", "umulh": "umulh x9, x0, x1",
		"udiv": "udiv x9, x0, x1", "sdiv": "sdiv x9, x0, x1", "ubfx": "ubfx x9, x0, #4, #8", "ubfiz": "ubfiz x9, x0, #4, #8", "sbfx": "sbfx x9, x0, #4, #8", "bfi": "mov x9, x0\n  bfi x9, x1, #4, #8",
		"crc32b": "crc32b w9, w0, w1", "crc32h": "crc32h w9, w0, w1", "crc32w": "crc32w w9, w0, w1", "crc32x": "crc32x w9, w0, x1", "crc32cb": "crc32cb w9, w0, w1", "crc32ch": "crc32ch w9, w0, w1", "crc32cw": "crc32cw w9, w0, w1", "crc32cx": "crc32cx w9, w0, x1",
		"cfinv": "cmp x0, x1\n  cfinv",
		"nop":   "nop", "wfe": "wfe", "wfi": "wfi", "sev": "sev", "sevl": "sevl", "yield": "yield", "csdb": "csdb", "esb": "esb", "hint": "hint #7", "clrex": "clrex",
		"dmb": "dmb ish", "dsb": "dsb sy", "isb": "isb",
	}
	// Memory through the frame and a span parameter, and the atomics.
	frame := map[string]string{
		"ldr": "str x0, [sp, #-16]!\n  ldr x9, [sp], #16", "str": "str x0, [sp, #-16]!\n  ldr x9, [sp], #16", "ldp": "stp x0, x1, [sp, #-16]!\n  ldp x9, x10, [sp], #16", "stp": "stp x0, x1, [sp, #-16]!\n  ldp x9, x10, [sp], #16",
		"ldrb": "str x0, [sp, #-16]!\n  ldrb w9, [sp]\n  add sp, sp, #16", "ldrh": "str x0, [sp, #-16]!\n  ldrh w9, [sp]\n  add sp, sp, #16", "strb": "sub sp, sp, #16\n  strb w0, [sp]\n  add sp, sp, #16", "strh": "sub sp, sp, #16\n  strh w0, [sp]\n  add sp, sp, #16",
		"ldrsb": "str x0, [sp, #-16]!\n  ldrsb x9, [sp]\n  add sp, sp, #16", "ldrsh": "str x0, [sp, #-16]!\n  ldrsh x9, [sp]\n  add sp, sp, #16", "ldrsw": "str x0, [sp, #-16]!\n  ldrsw x9, [sp]\n  add sp, sp, #16", "ldpsw": "stp x0, x1, [sp, #-16]!\n  ldpsw x9, x10, [sp]\n  add sp, sp, #16",
		"ldur": "str x0, [sp, #-16]!\n  ldur x9, [sp, #0]\n  add sp, sp, #16", "stur": "sub sp, sp, #16\n  stur x0, [sp, #8]\n  add sp, sp, #16", "ldurb": "str x0, [sp, #-16]!\n  ldurb w9, [sp]\n  add sp, sp, #16", "ldurh": "str x0, [sp, #-16]!\n  ldurh w9, [sp]\n  add sp, sp, #16",
		"sturb": "sub sp, sp, #16\n  sturb w0, [sp]\n  add sp, sp, #16", "sturh": "sub sp, sp, #16\n  sturh w0, [sp]\n  add sp, sp, #16", "ldursb": "str x0, [sp, #-16]!\n  ldursb x9, [sp]\n  add sp, sp, #16", "ldursh": "str x0, [sp, #-16]!\n  ldursh x9, [sp]\n  add sp, sp, #16", "ldursw": "str x0, [sp, #-16]!\n  ldursw x9, [sp]\n  add sp, sp, #16",
		"prfm": "sub sp, sp, #16\n  prfm pldl1keep, [sp]\n  add sp, sp, #16",
	}
	span := map[string]string{}
	for _, name := range []string{"ldar", "ldxr", "ldaxr", "ldapr"} {
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
		for _, order := range []string{"", "a", "l", "al"} {
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
	system := map[string]string{
		"mrs": "mrs x9, cntvct_el0", "msr": "msr cntvoff_el2, x0", "dc": "dc civac, x0", "ic": "ic iallu", "tlbi": "tlbi vmalle1is", "at": "at s1e1r, x0",
		"svc": "svc #0", "hvc": "hvc #0", "smc": "smc #0",
	}
	control := map[string]string{
		"b": "b done\ndone:\n  mov x0, #0", "b.": "cmp x0, x1\n  b.lo done\ndone:\n  mov x0, #0", "cbz": "cbz x0, done\ndone:\n  mov x0, #0", "cbnz": "cbnz x0, done\ndone:\n  mov x0, #0",
		"tbz": "tbz x0, #3, done\ndone:\n  mov x0, #0", "tbnz": "tbnz x0, #3, done\ndone:\n  mov x0, #0", "bl": "bl helper", "blr": "blr x1", "br": "br x1", "ret": "ret", "eret": "eret", "brk": "brk #1",
	}
	names := make([]string, 0, len(instructionTable))
	for name := range instructionTable {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		body, decl := "", "f: (a, b: u64, s: [*]u64) -> u64"
		prologue, epilogue := "  bind x0 = a\n  bind x1 = b\n  bind x2, w3 = s\n  clobber x9, x10, x30\n  frame 16\n", "\n  mov x0, #0\n  ret"
		switch {
		case samples[name] != "":
			body = "  " + samples[name]
		case frame[name] != "":
			body = "  " + frame[name]
		case span[name] != "":
			body = "  cmp w3, #1\n  b.lo short\n  " + span[name] + "\n  mov x0, #0\n  ret\nshort:\n  mov x0, #0\n  ret"
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
			case "eret":
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
