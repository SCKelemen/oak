package asm

// Apple M-series coverage (ARMv8.4–8.6 plus arm64e; docs/spec/94-assembler.md
// §3): pointer authentication, branch target identification, the
// flag-manipulation extensions, RCpc2 loads and stores, FP16 scalar
// arithmetic, dot products and int8 matrix multiply, BF16, FHM, complex
// arithmetic, JavaScript conversion, frint32/64, the crypto extensions, and
// the scalar NEON integer forms. The seam checker enforces forms and
// effects; the bitvector verifier trusts all of it.

func init() {
	add := func(name string, spec instructionSpec) {
		spec.sysregOperand = -1
		instructionTable[name] = spec
	}
	extend := func(name string, forms ...form) {
		spec, known := instructionTable[name]
		if !known {
			spec = instructionSpec{sysregOperand: -1}
		}
		spec.forms = append(spec.forms, forms...)
		instructionTable[name] = spec
	}
	// Pointer authentication (arm64e). Register forms sign or authenticate
	// the first operand with the modifier in the second; the z forms use a
	// zero modifier; the sp/lr forms are transparent to the discipline.
	for _, name := range []string{"pacia", "pacib", "pacda", "pacdb", "autia", "autib", "autda", "autdb"} {
		add(name, instructionSpec{forms: []form{{opX, opX}}})
	}
	for _, name := range []string{"paciza", "pacizb", "pacdza", "pacdzb", "autiza", "autizb", "autdza", "autdzb", "xpaci", "xpacd"} {
		add(name, instructionSpec{forms: []form{{opX}}})
	}
	for _, name := range []string{"paciasp", "pacibsp", "autiasp", "autibsp", "paciaz", "pacibz", "autiaz", "autibz", "pacia1716", "pacib1716", "autia1716", "autib1716", "xpaclri"} {
		add(name, instructionSpec{forms: []form{{opNone}}})
	}
	add("pacga", instructionSpec{forms: []form{{opX, opX, opX}}})
	for _, name := range []string{"retaa", "retab"} {
		add(name, instructionSpec{forms: []form{{opNone}}, branch: branchReturn})
	}
	for _, name := range []string{"braa", "brab"} {
		add(name, instructionSpec{forms: []form{{opX, opX}, {opX, opSP}}, branch: branchReturn})
	}
	for _, name := range []string{"braaz", "brabz"} {
		add(name, instructionSpec{forms: []form{{opX}}, branch: branchReturn})
	}
	for _, name := range []string{"blraa", "blrab"} {
		add(name, instructionSpec{forms: []form{{opX, opX}, {opX, opSP}}, branch: branchCall, clobbersCallerSaved: true})
	}
	for _, name := range []string{"blraaz", "blrabz"} {
		add(name, instructionSpec{forms: []form{{opX}}, branch: branchCall, clobbersCallerSaved: true})
	}
	// Branch target identification, speculation barriers, hints with timeouts.
	add("bti", instructionSpec{forms: []form{{opNone}, {opOption}}})
	add("sb", instructionSpec{forms: []form{{opNone}}, barrier: true})
	add("dgh", instructionSpec{forms: []form{{opNone}}})
	for _, name := range []string{"wfet", "wfit"} {
		add(name, instructionSpec{forms: []form{{opX}}})
	}
	// Flag manipulation (FlagM, FlagM2).
	for _, name := range []string{"setf8", "setf16"} {
		add(name, instructionSpec{forms: []form{{opW}}, setsFlags: true})
	}
	add("rmif", instructionSpec{forms: []form{{opX, opImm, opImm}}, readsFlags: true, setsFlags: true})
	for _, name := range []string{"axflag", "xaflag"} {
		add(name, instructionSpec{forms: []form{{opNone}}, readsFlags: true, setsFlags: true})
	}
	// RCpc2: unscaled acquire loads and release stores.
	add("ldapur", instructionSpec{forms: []form{{opX, opMem}, {opW, opMem}}, memory: true})
	for _, name := range []string{"ldapurb", "ldapurh"} {
		add(name, instructionSpec{forms: []form{{opW, opMem}}, memory: true})
	}
	for _, name := range []string{"ldapursb", "ldapursh"} {
		add(name, instructionSpec{forms: []form{{opW, opMem}, {opX, opMem}}, memory: true})
	}
	add("ldapursw", instructionSpec{forms: []form{{opX, opMem}}, memory: true})
	add("stlur", instructionSpec{forms: []form{{opX, opMem}, {opW, opMem}}, memory: true})
	for _, name := range []string{"stlurb", "stlurh"} {
		add(name, instructionSpec{forms: []form{{opW, opMem}}, memory: true})
	}
	// FP16 scalar arithmetic: the h view joins the s/d forms.
	for _, name := range []string{"fadd", "fsub", "fmul", "fdiv", "fnmul", "fmax", "fmin", "fmaxnm", "fminnm"} {
		extend(name, form{opFH, opFH, opFH})
	}
	for _, name := range []string{"fneg", "fabs", "fsqrt", "frinta", "frinti", "frintm", "frintn", "frintp", "frintx", "frintz"} {
		extend(name, form{opFH, opFH})
	}
	for _, name := range []string{"fmadd", "fmsub", "fnmadd", "fnmsub"} {
		extend(name, form{opFH, opFH, opFH, opFH})
	}
	for _, name := range []string{"fcmp", "fcmpe"} {
		extend(name, form{opFH, opFH}, form{opFH, opFImm})
	}
	extend("fcsel", form{opFH, opFH, opFH, opCond})
	extend("fmov", form{opFH, opFH}, form{opFH, opW}, form{opW, opFH}, form{opFH, opFImm})
	for _, name := range []string{"fcvtzs", "fcvtzu", "fcvtas", "fcvtau", "fcvtms", "fcvtmu", "fcvtns", "fcvtnu", "fcvtps", "fcvtpu"} {
		extend(name, form{opW, opFH}, form{opX, opFH})
	}
	for _, name := range []string{"scvtf", "ucvtf"} {
		extend(name, form{opFH, opW}, form{opFH, opX})
	}
	// Dot products, int8 matrix multiply, BF16, FHM, complex, JavaScript,
	// frint32/64.
	for _, name := range []string{"sdot", "udot", "usdot", "sudot", "bfdot"} {
		add(name, instructionSpec{forms: []form{{opVA, opVA, opVA}, {opVA, opVA, opVL}}})
	}
	for _, name := range []string{"smmla", "ummla", "usmmla", "bfmmla"} {
		add(name, instructionSpec{forms: []form{{opVA, opVA, opVA}}})
	}
	for _, name := range []string{"bfmlalb", "bfmlalt"} {
		add(name, instructionSpec{forms: []form{{opVA, opVA, opVA}, {opVA, opVA, opVL}}})
	}
	add("bfcvt", instructionSpec{forms: []form{{opFH, opFS}}})
	add("bfcvtn", instructionSpec{forms: []form{{opVA, opVA}}})
	add("bfcvtn2", instructionSpec{forms: []form{{opVA, opVA}}})
	for _, name := range []string{"fmlal", "fmlsl", "fmlal2", "fmlsl2"} {
		add(name, instructionSpec{forms: []form{{opVA, opVA, opVA}, {opVA, opVA, opVL}}})
	}
	add("fcadd", instructionSpec{forms: []form{{opVA, opVA, opVA, opImm}}})
	add("fcmla", instructionSpec{forms: []form{{opVA, opVA, opVA, opImm}, {opVA, opVA, opVL, opImm}}})
	add("fjcvtzs", instructionSpec{forms: []form{{opW, opFD}}})
	for _, name := range []string{"frint32z", "frint32x", "frint64z", "frint64x"} {
		add(name, instructionSpec{forms: []form{{opFS, opFS}, {opFD, opFD}, {opVA, opVA}}})
	}
	// Crypto: AES, SHA1, SHA2, SHA512, SHA3, polynomial multiply.
	for _, name := range []string{"aese", "aesd", "aesmc", "aesimc"} {
		add(name, instructionSpec{forms: []form{{opVA, opVA}}})
	}
	for _, name := range []string{"sha1c", "sha1p", "sha1m"} {
		add(name, instructionSpec{forms: []form{{opFQ, opFS, opVA}}})
	}
	add("sha1h", instructionSpec{forms: []form{{opFS, opFS}}})
	add("sha1su0", instructionSpec{forms: []form{{opVA, opVA, opVA}}})
	add("sha1su1", instructionSpec{forms: []form{{opVA, opVA}}})
	for _, name := range []string{"sha256h", "sha256h2", "sha512h", "sha512h2"} {
		add(name, instructionSpec{forms: []form{{opFQ, opFQ, opVA}}})
	}
	for _, name := range []string{"sha256su0", "sha512su0"} {
		add(name, instructionSpec{forms: []form{{opVA, opVA}}})
	}
	for _, name := range []string{"sha256su1", "sha512su1"} {
		add(name, instructionSpec{forms: []form{{opVA, opVA, opVA}}})
	}
	for _, name := range []string{"eor3", "bcax"} {
		add(name, instructionSpec{forms: []form{{opVA, opVA, opVA, opVA}}})
	}
	add("rax1", instructionSpec{forms: []form{{opVA, opVA, opVA}}})
	add("xar", instructionSpec{forms: []form{{opVA, opVA, opVA, opImm}}})
	for _, name := range []string{"pmull", "pmull2"} {
		add(name, instructionSpec{forms: []form{{opVA, opVA, opVA}}})
	}
	// Scalar NEON integer forms on the d view (and b/h/s for the saturating
	// and pairwise ones).
	for _, name := range []string{"add", "sub", "cmeq", "cmgt", "cmge", "cmhi", "cmhs", "cmtst"} {
		extend(name, form{opFD, opFD, opFD})
	}
	for _, name := range []string{"cmeq", "cmgt", "cmge", "cmlt", "cmle"} {
		extend(name, form{opFD, opFD, opImm})
	}
	for _, name := range []string{"shl", "sshr", "ushr", "sli", "sri", "ssra", "usra"} {
		extend(name, form{opFD, opFD, opImm})
	}
	for _, name := range []string{"sqadd", "uqadd", "sqsub", "uqsub", "ushl", "sshl", "urshl", "srshl", "sqshl", "uqshl"} {
		extend(name, form{opFB, opFB, opFB}, form{opFH, opFH, opFH}, form{opFS, opFS, opFS}, form{opFD, opFD, opFD})
	}
	for _, name := range []string{"abs", "neg"} {
		extend(name, form{opFD, opFD})
	}
	extend("addp", form{opFD, opVA})
	for _, name := range []string{"sqxtn", "uqxtn", "sqxtun"} {
		extend(name, form{opFB, opFH}, form{opFH, opFS}, form{opFS, opFD})
	}
}

// pacTransparent: the pointer-authentication instructions that sign or
// authenticate the link register in place. The signature is not a value
// the checker tracks: they neither read nor write x30 for the callee-saved
// discipline, so `paciasp` may open a prologue before the link register is
// saved.
func pacTransparent(mnemonic string) bool {
	switch mnemonic {
	case "paciasp", "pacibsp", "autiasp", "autibsp", "paciaz", "pacibz", "autiaz", "autibz", "pacia1716", "pacib1716", "autia1716", "autib1716", "xpaclri":
		return true
	}
	return false
}

// pacInPlace: the one-register pointer-authentication forms read and write
// their operand.
func pacInPlace(mnemonic string) bool {
	switch mnemonic {
	case "paciza", "pacizb", "pacdza", "pacdzb", "autiza", "autizb", "autdza", "autdzb", "xpaci", "xpacd":
		return true
	}
	return false
}
