package asm

// Floating-point and NEON coverage for the seam checker
// (docs/spec/94-assembler.md §3). Scalar FP travels in the s/d views of the
// vector registers; vectors carry an arrangement. The checker enforces
// operand forms, arrangement agreement, lane bounds, and the vector
// clobber discipline; the bitvector verifier does not model these
// instructions and trusts them per §5.

import "fmt"

func init() {
	add := func(name string, spec instructionSpec) {
		spec.sysregOperand = -1
		instructionTable[name] = spec
	}
	scalar := func(n int) []form { // n scalar operands, all s or all d (h where noted)
		out := []form{}
		for _, class := range []operandClass{opFS, opFD} {
			f := make(form, n)
			for i := range f {
				f[i] = class
			}
			out = append(out, f)
		}
		return out
	}
	vector := func(n int) []form { // n arranged vector operands
		f := make(form, n)
		for i := range f {
			f[i] = opVA
		}
		return []form{f}
	}
	// Scalar floating point.
	add("fmov", instructionSpec{forms: append(scalar(2), form{opFS, opW}, form{opFD, opX}, form{opW, opFS}, form{opX, opFD}, form{opFS, opFImm}, form{opFD, opFImm}, form{opVA, opFImm}, form{opX, opVL}, form{opVL, opX})})
	for _, name := range []string{"fadd", "fsub", "fmul", "fdiv", "fnmul", "fmax", "fmin", "fmaxnm", "fminnm"} {
		add(name, instructionSpec{forms: append(scalar(3), vector(3)...)})
	}
	for _, name := range []string{"fneg", "fabs", "fsqrt", "frinta", "frinti", "frintm", "frintn", "frintp", "frintx", "frintz"} {
		add(name, instructionSpec{forms: append(scalar(2), vector(2)...)})
	}
	for _, name := range []string{"fmadd", "fmsub", "fnmadd", "fnmsub"} {
		add(name, instructionSpec{forms: scalar(4)})
	}
	for _, name := range []string{"fcmp", "fcmpe"} {
		add(name, instructionSpec{forms: append(scalar(2), form{opFS, opFImm}, form{opFD, opFImm}), setsFlags: true})
	}
	add("fcsel", instructionSpec{forms: []form{{opFS, opFS, opFS, opCond}, {opFD, opFD, opFD, opCond}}, readsFlags: true})
	add("fcvt", instructionSpec{forms: []form{{opFS, opFD}, {opFD, opFS}, {opFH, opFS}, {opFS, opFH}, {opFH, opFD}, {opFD, opFH}}})
	for _, name := range []string{"fcvtzs", "fcvtzu", "fcvtas", "fcvtau", "fcvtms", "fcvtmu", "fcvtns", "fcvtnu", "fcvtps", "fcvtpu"} {
		add(name, instructionSpec{forms: append([]form{{opW, opFS}, {opX, opFS}, {opW, opFD}, {opX, opFD}}, vector(2)...)})
	}
	for _, name := range []string{"scvtf", "ucvtf"} {
		add(name, instructionSpec{forms: append([]form{{opFS, opW}, {opFS, opX}, {opFD, opW}, {opFD, opX}}, vector(2)...)})
	}
	add("fcvtn", instructionSpec{forms: vector(2)})
	add("fcvtl", instructionSpec{forms: vector(2)})
	// Vector integer arithmetic and logic.
	for _, name := range []string{"mla", "mls", "smax", "smin", "umax", "umin", "sabd", "uabd", "shadd", "uhadd", "sqadd", "uqadd", "sqsub", "uqsub", "addp", "smaxp", "sminp", "umaxp", "uminp", "pmul", "fmla", "fmls", "fmulx", "fabd", "fmaxp", "fminp", "faddp"} {
		add(name, instructionSpec{forms: vector(3)})
	}
	for _, name := range []string{"add", "sub", "mul", "and", "orr", "eor", "bic", "orn"} {
		spec := instructionTable[name]
		spec.forms = append(spec.forms, vector(3)...)
		instructionTable[name] = spec
	}
	for _, name := range []string{"neg", "mvn", "not", "abs", "cnt", "rev16", "rev32", "rev64", "clz", "cls", "rbit"} {
		spec, known := instructionTable[name]
		if !known {
			spec = instructionSpec{}
		}
		spec.forms = append(spec.forms, vector(2)...)
		spec.sysregOperand = -1
		instructionTable[name] = spec
	}
	// Vector compares (register and against zero).
	for _, name := range []string{"cmeq", "cmgt", "cmge", "cmhi", "cmhs", "cmtst", "fcmeq", "fcmgt", "fcmge"} {
		add(name, instructionSpec{forms: append(vector(3), form{opVA, opVA, opImm}, form{opVA, opVA, opFImm})})
	}
	for _, name := range []string{"cmlt", "cmle", "fcmlt", "fcmle"} {
		add(name, instructionSpec{forms: []form{{opVA, opVA, opImm}, {opVA, opVA, opFImm}}})
	}
	// Reductions to a scalar.
	for _, name := range []string{"addv", "smaxv", "sminv", "umaxv", "uminv", "fmaxv", "fminv", "fmaxnmv", "fminnmv"} {
		add(name, instructionSpec{forms: []form{{opFS, opVA}, {opFH, opVA}, {opFD, opVA}, {opFQ, opVA}}})
	}
	for _, name := range []string{"saddlv", "uaddlv"} {
		add(name, instructionSpec{forms: []form{{opFH, opVA}, {opFS, opVA}, {opFD, opVA}}})
	}
	// Vector shifts, widening and narrowing.
	for _, name := range []string{"shl", "ushr", "sshr", "sli", "sri", "ssra", "usra", "shrn", "rshrn", "sqshrn", "uqshrn", "sqrshrn", "uqrshrn", "ushll", "sshll", "shll", "uqshl", "sqshl"} {
		add(name, instructionSpec{forms: []form{{opVA, opVA, opImm}}})
	}
	for _, name := range []string{"ushl", "sshl", "urshl", "srshl"} {
		add(name, instructionSpec{forms: vector(3)})
	}
	for _, name := range []string{"xtn", "sqxtn", "uqxtn", "sqxtun", "xtn2", "sqxtn2", "uqxtn2", "uaddlp", "saddlp", "uadalp", "sadalp"} {
		add(name, instructionSpec{forms: vector(2)})
	}
	for _, name := range []string{"uaddl", "saddl", "usubl", "ssubl", "umull", "smull", "umlal", "smlal", "umlsl", "smlsl", "uaddw", "saddw", "usubw", "ssubw", "uaddl2", "saddl2", "umull2", "smull2"} {
		spec, known := instructionTable[name]
		if !known {
			spec = instructionSpec{}
		}
		spec.forms = append(spec.forms, vector(3)...)
		spec.sysregOperand = -1
		instructionTable[name] = spec
	}
	// Moves, inserts, extracts, permutes.
	add("dup", instructionSpec{forms: []form{{opVA, opW}, {opVA, opX}, {opVA, opVL}, {opFS, opVL}, {opFD, opVL}, {opFH, opVL}}})
	add("ins", instructionSpec{forms: []form{{opVL, opW}, {opVL, opX}, {opVL, opVL}}})
	add("umov", instructionSpec{forms: []form{{opW, opVL}, {opX, opVL}}})
	add("smov", instructionSpec{forms: []form{{opW, opVL}, {opX, opVL}}})
	mov := instructionTable["mov"]
	mov.forms = append(mov.forms, form{opVA, opVA}, form{opW, opVL}, form{opX, opVL}, form{opVL, opW}, form{opVL, opX}, form{opVL, opVL})
	instructionTable["mov"] = mov
	add("ext", instructionSpec{forms: []form{{opVA, opVA, opVA, opImm}}})
	for _, name := range []string{"tbl", "tbx"} {
		add(name, instructionSpec{forms: []form{{opVA, opList, opVA}}})
	}
	for _, name := range []string{"zip1", "zip2", "uzp1", "uzp2", "trn1", "trn2"} {
		add(name, instructionSpec{forms: vector(3)})
	}
	for _, name := range []string{"movi", "mvni"} {
		add(name, instructionSpec{forms: []form{{opVA, opImm}, {opFD, opImm}}})
	}
	// Structure loads and stores.
	for _, name := range []string{"ld1", "st1", "ld2", "st2", "ld3", "st3", "ld4", "st4", "ld1r"} {
		add(name, instructionSpec{forms: []form{{opList, opMem}}, memory: true})
	}
	// Scalar and vector loads/stores through the general table: ldr/str/
	// ldp/stp/ldur/stur accept the scalar views and q registers.
	for _, name := range []string{"ldr", "str", "ldur", "stur"} {
		spec := instructionTable[name]
		spec.forms = append(spec.forms, form{opFS, opMem}, form{opFD, opMem}, form{opFQ, opMem}, form{opFH, opMem})
		instructionTable[name] = spec
	}
	for _, name := range []string{"ldp", "stp"} {
		spec := instructionTable[name]
		spec.forms = append(spec.forms, form{opFS, opFS, opMem}, form{opFD, opFD, opMem}, form{opFQ, opFQ, opMem})
		instructionTable[name] = spec
	}
}

// vectorDiscipline checks the arrangement and lane rules of one
// instruction: arranged operands agree unless the instruction widens,
// narrows, or reduces; structure loads use one arrangement; lane indices
// are already bounded at parse time. It returns "" when the instruction
// is well-formed.
func vectorDiscipline(instr Instruction) string {
	var arranged []Register
	for _, operand := range instr.Operands {
		switch o := operand.(type) {
		case Register:
			if o.Class == ClassV && o.Lane < 0 {
				if _, isArrangement := vectorArrangements[o.Vec]; isArrangement {
					arranged = append(arranged, o)
				}
			}
		case RegisterList:
			arranged = append(arranged, o.Regs...)
		}
	}
	if len(arranged) < 2 || mixedArrangementAllowed(instr.Mnemonic) {
		return ""
	}
	for _, reg := range arranged[1:] {
		if reg.Vec != arranged[0].Vec {
			return fmt.Sprintf("arrangements %s and %s disagree", arranged[0].Text, reg.Text)
		}
	}
	return ""
}

// mixedArrangementAllowed: the widening, narrowing, and pairwise-long
// instructions relate different arrangements by definition.
func mixedArrangementAllowed(mnemonic string) bool {
	switch mnemonic {
	case "ushll", "sshll", "shll", "xtn", "xtn2", "sqxtn", "sqxtn2", "uqxtn", "uqxtn2", "sqxtun", "shrn", "rshrn", "sqshrn", "uqshrn", "sqrshrn", "uqrshrn",
		"uaddlp", "saddlp", "uadalp", "sadalp", "uaddl", "saddl", "usubl", "ssubl", "umull", "smull", "umlal", "smlal", "umlsl", "smlsl", "uaddw", "saddw", "usubw", "ssubw",
		"uaddl2", "saddl2", "umull2", "smull2", "fcvtn", "fcvtl", "fcvtzs", "fcvtzu", "scvtf", "ucvtf", "tbl", "tbx", "ext":
		return true
	}
	return false
}
