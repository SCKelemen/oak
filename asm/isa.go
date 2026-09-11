package asm

// The A64 general-purpose instruction set beyond the v1 core
// (docs/spec/94-assembler.md §3, coverage table): data processing with
// carry, negated logical forms, rotates and bit manipulation, extends,
// wide moves, the conditional-select family, wide multiplies and division,
// sign-extending and unscaled loads, exclusive and acquire/release
// accesses and the LSE atomics, indirect transfers, hints, exceptions,
// and cache/TLB maintenance. Every entry states its operand forms and
// effects for the seam checker; the verifier models the bitvector-valued
// ones (asm/isa_semantics.go) and trusts the rest.

import "strings"

func init() {
	add := func(name string, spec instructionSpec) {
		spec.sysregOperand = -1
		instructionTable[name] = spec
	}
	rr := func(n int) []form { // n register operands, all X or all W
		x := make(form, n)
		w := make(form, n)
		for i := range x {
			x[i], w[i] = opX, opW
		}
		return []form{x, w}
	}
	// Arithmetic with carry; negations.
	for _, name := range []string{"adc", "sbc"} {
		add(name, instructionSpec{forms: rr(3), readsFlags: true})
	}
	for _, name := range []string{"adcs", "sbcs"} {
		add(name, instructionSpec{forms: rr(3), readsFlags: true, setsFlags: true})
	}
	add("ngc", instructionSpec{forms: rr(2), readsFlags: true})
	add("ngcs", instructionSpec{forms: rr(2), readsFlags: true, setsFlags: true})
	add("negs", instructionSpec{forms: rr(2), setsFlags: true})
	add("cmn", instructionSpec{forms: []form{{opX, opX}, {opW, opW}, {opX, opImm}, {opW, opImm}}, setsFlags: true})
	add("ccmn", instructionSpec{forms: []form{{opX, opX, opImm, opCond}, {opW, opW, opImm, opCond}, {opX, opImm, opImm, opCond}, {opW, opImm, opImm, opCond}}, readsFlags: true, setsFlags: true})
	// Logical forms.
	add("ands", instructionSpec{forms: regForms3(), setsFlags: true})
	add("bics", instructionSpec{forms: rr(3), setsFlags: true})
	for _, name := range []string{"bic", "orn", "eon"} {
		add(name, instructionSpec{forms: rr(3)})
	}
	// Rotates, extraction, bit manipulation, extends.
	add("ror", instructionSpec{forms: []form{{opX, opX, opImm}, {opW, opW, opImm}, {opX, opX, opX}, {opW, opW, opW}}})
	add("extr", instructionSpec{forms: []form{{opX, opX, opX, opImm}, {opW, opW, opW, opImm}}})
	for _, name := range []string{"rev", "rev16", "rbit", "clz", "cls"} {
		add(name, instructionSpec{forms: rr(2)})
	}
	add("rev32", instructionSpec{forms: []form{{opX, opX}}})
	for _, name := range []string{"sxtb", "sxth", "uxtb", "uxth"} {
		add(name, instructionSpec{forms: rr(2)})
	}
	add("sxtw", instructionSpec{forms: []form{{opX, opW}}})
	// Wide moves.
	for _, name := range []string{"movz", "movn", "movk"} {
		add(name, instructionSpec{forms: []form{{opX, opImm}, {opW, opImm}}})
	}
	// The conditional-select family.
	for _, name := range []string{"csinc", "csinv", "csneg"} {
		add(name, instructionSpec{forms: []form{{opX, opX, opX, opCond}, {opW, opW, opW, opCond}}, readsFlags: true})
	}
	add("cinv", instructionSpec{forms: []form{{opX, opX, opCond}, {opW, opW, opCond}}, readsFlags: true})
	add("csetm", instructionSpec{forms: []form{{opX, opCond}, {opW, opCond}}, readsFlags: true})
	// Wide multiplies and division.
	for _, name := range []string{"smull", "umull"} {
		add(name, instructionSpec{forms: []form{{opX, opW, opW}}})
	}
	for _, name := range []string{"smaddl", "umaddl", "smsubl", "umsubl"} {
		add(name, instructionSpec{forms: []form{{opX, opW, opW, opX}}})
	}
	for _, name := range []string{"smulh", "umulh"} {
		add(name, instructionSpec{forms: []form{{opX, opX, opX}}})
	}
	for _, name := range []string{"mneg", "udiv", "sdiv"} {
		add(name, instructionSpec{forms: rr(3)})
	}
	// Sign-extending and unscaled loads and stores.
	add("ldrsb", instructionSpec{forms: []form{{opW, opMem}, {opX, opMem}}, memory: true})
	add("ldrsh", instructionSpec{forms: []form{{opW, opMem}, {opX, opMem}}, memory: true})
	add("ldrsw", instructionSpec{forms: []form{{opX, opMem}}, memory: true})
	add("ldpsw", instructionSpec{forms: []form{{opX, opX, opMem}}, memory: true})
	add("ldur", instructionSpec{forms: []form{{opX, opMem}, {opW, opMem}}, memory: true})
	add("stur", instructionSpec{forms: []form{{opX, opMem}, {opW, opMem}}, memory: true})
	for _, name := range []string{"ldurb", "ldurh", "sturb", "sturh"} {
		add(name, instructionSpec{forms: []form{{opW, opMem}}, memory: true})
	}
	add("ldursb", instructionSpec{forms: []form{{opW, opMem}, {opX, opMem}}, memory: true})
	add("ldursh", instructionSpec{forms: []form{{opW, opMem}, {opX, opMem}}, memory: true})
	add("ldursw", instructionSpec{forms: []form{{opX, opMem}}, memory: true})
	add("prfm", instructionSpec{forms: []form{{opOption, opMem}}, memory: true})
	// Acquire/release and exclusive accesses.
	for _, name := range []string{"ldar", "ldxr", "ldaxr", "ldapr"} {
		add(name, instructionSpec{forms: []form{{opX, opMem}, {opW, opMem}}, memory: true})
		add(name+"b", instructionSpec{forms: []form{{opW, opMem}}, memory: true})
		add(name+"h", instructionSpec{forms: []form{{opW, opMem}}, memory: true})
	}
	add("stlr", instructionSpec{forms: []form{{opX, opMem}, {opW, opMem}}, memory: true})
	add("stlrb", instructionSpec{forms: []form{{opW, opMem}}, memory: true})
	add("stlrh", instructionSpec{forms: []form{{opW, opMem}}, memory: true})
	for _, name := range []string{"stxr", "stlxr"} {
		add(name, instructionSpec{forms: []form{{opW, opX, opMem}, {opW, opW, opMem}}, memory: true})
		add(name+"b", instructionSpec{forms: []form{{opW, opW, opMem}}, memory: true})
		add(name+"h", instructionSpec{forms: []form{{opW, opW, opMem}}, memory: true})
	}
	// LSE atomics: <op>{,a,l,al}{,b,h} xS, xT, [xB]  (b/h only in w form).
	for _, base := range []string{"ldadd", "ldclr", "ldeor", "ldset", "ldsmax", "ldsmin", "ldumax", "ldumin", "swp", "cas"} {
		for _, order := range []string{"", "a", "l", "al"} {
			add(base+order, instructionSpec{forms: []form{{opX, opX, opMem}, {opW, opW, opMem}}, memory: true})
			add(base+order+"b", instructionSpec{forms: []form{{opW, opW, opMem}}, memory: true})
			add(base+order+"h", instructionSpec{forms: []form{{opW, opW, opMem}}, memory: true})
		}
	}
	add("clrex", instructionSpec{forms: []form{{opNone}, {opImm}}})
	// Indirect transfers.
	add("br", instructionSpec{forms: []form{{opX}}, branch: branchReturn})
	add("blr", instructionSpec{forms: []form{{opX}}, branch: branchCall, clobbersCallerSaved: true})
	instructionTable["ret"] = instructionSpec{forms: []form{{opNone}, {opX}}, branch: branchReturn, sysregOperand: -1}
	// Hints, traps, exceptions.
	for _, name := range []string{"wfe", "wfi", "sev", "sevl", "yield", "csdb", "esb"} {
		add(name, instructionSpec{forms: []form{{opNone}}})
	}
	add("hint", instructionSpec{forms: []form{{opImm}}})
	add("brk", instructionSpec{forms: []form{{opImm}}, branch: branchReturn})
	for _, name := range []string{"svc", "hvc", "smc"} {
		add(name, instructionSpec{forms: []form{{opImm}}, system: true, clobbersCallerSaved: true})
	}
	// Cache, TLB, and address-translation maintenance.
	add("dc", instructionSpec{forms: []form{{opOption, opX}}, system: true, barrier: true})
	add("ic", instructionSpec{forms: []form{{opOption}, {opOption, opX}}, system: true, barrier: true})
	add("tlbi", instructionSpec{forms: []form{{opOption}, {opOption, opX}}, system: true, barrier: true})
	add("at", instructionSpec{forms: []form{{opOption, opX}}, system: true, barrier: true})
	// CRC and flag manipulation.
	for _, name := range []string{"crc32b", "crc32h", "crc32w", "crc32cb", "crc32ch", "crc32cw"} {
		add(name, instructionSpec{forms: []form{{opW, opW, opW}}})
	}
	for _, name := range []string{"crc32x", "crc32cx"} {
		add(name, instructionSpec{forms: []form{{opW, opW, opX}}})
	}
	add("cfinv", instructionSpec{forms: []form{{opNone}}, readsFlags: true, setsFlags: true})
}

// memorySize is the byte footprint of one load/store, from the mnemonic
// (sub-word accesses, sign-extending loads, unscaled forms, atomics with a
// b/h suffix) or the register width.
func memorySize(mnemonic string, class RegClass) int64 {
	if class == ClassV {
		return 16 // refined per register view by memorySizeReg
	}
	switch mnemonic {
	case "ldrb", "strb", "ldrsb", "ldurb", "sturb", "ldursb", "ldarb", "ldxrb", "ldaxrb", "ldaprb", "stlrb", "stxrb", "stlxrb", "ldapurb", "ldapursb", "stlurb":
		return 1
	case "ldrh", "strh", "ldrsh", "ldurh", "sturh", "ldursh", "ldarh", "ldxrh", "ldaxrh", "ldaprh", "stlrh", "stxrh", "stlxrh", "ldapurh", "ldapursh", "stlurh":
		return 2
	case "ldrsw", "ldursw", "ldapursw":
		return 4
	case "ldpsw":
		return 8
	case "prfm":
		return 8
	}
	if isAtomic(mnemonic) {
		if strings.HasSuffix(mnemonic, "b") && !strings.HasSuffix(mnemonic, "ab") || atomicSuffix(mnemonic) == "b" {
			return 1
		}
		if atomicSuffix(mnemonic) == "h" {
			return 2
		}
	}
	width := int64(8)
	if class == ClassW {
		width = 4
	}
	if mnemonic == "ldp" || mnemonic == "stp" {
		return 2 * width
	}
	return width
}

// memorySizeReg is memorySize with the register's vector view taken into
// account: ldr d0 moves 8 bytes, ldr q0 16, ldp s0, s1 8.
func memorySizeReg(mnemonic string, reg Register) int64 {
	if reg.Class == ClassV {
		if mnemonic == "ld1r" {
			return int64(laneBytes(reg.Vec)) // one element, replicated
		}
		size := reg.VecBytes()
		if mnemonic == "ldp" || mnemonic == "stp" {
			return 2 * size
		}
		return size
	}
	return memorySize(mnemonic, reg.Class)
}

// isStructureAccess: ld1–ld4/st1–st4 move every register of their list.
func isStructureAccess(mnemonic string) bool {
	switch mnemonic {
	case "ld1", "st1", "ld2", "st2", "ld3", "st3", "ld4", "st4":
		return true
	}
	return false
}

var atomicBases = []string{"ldadd", "ldclr", "ldeor", "ldset", "ldsmax", "ldsmin", "ldumax", "ldumin", "swp", "cas"}

// isAtomic reports an LSE atomic mnemonic.
func isAtomic(mnemonic string) bool {
	for _, base := range atomicBases {
		if strings.HasPrefix(mnemonic, base) {
			rest := strings.TrimPrefix(mnemonic, base)
			for _, order := range []string{"", "a", "l", "al"} {
				for _, size := range []string{"", "b", "h"} {
					if rest == order+size {
						return true
					}
				}
			}
		}
	}
	return false
}

// atomicSuffix is the size suffix ("", "b", "h") of an LSE atomic.
func atomicSuffix(mnemonic string) string {
	for _, base := range atomicBases {
		if strings.HasPrefix(mnemonic, base) {
			rest := strings.TrimPrefix(mnemonic, base)
			rest = strings.TrimPrefix(strings.TrimPrefix(rest, "al"), "a")
			rest = strings.TrimPrefix(rest, "l")
			return rest
		}
	}
	return ""
}

// atomicBase is the operation name of an LSE atomic ("ldadd", "cas", ...).
func atomicBase(mnemonic string) string {
	for _, base := range atomicBases {
		if strings.HasPrefix(mnemonic, base) {
			return base
		}
	}
	return ""
}

// isSignExtendingLoad: the loads whose element is sign-extended into the
// register.
func isSignExtendingLoad(mnemonic string) bool {
	switch mnemonic {
	case "ldrsb", "ldrsh", "ldrsw", "ldursb", "ldursh", "ldursw":
		return true
	}
	return false
}

// isPlainLoad: loads that read one element per destination register with
// no ordering or exclusivity semantics the verifier must model.
func isPlainLoad(mnemonic string) bool {
	switch mnemonic {
	case "ldr", "ldrb", "ldrh", "ldur", "ldurb", "ldurh", "ldrsb", "ldrsh", "ldrsw", "ldursb", "ldursh", "ldursw":
		return true
	}
	return false
}
