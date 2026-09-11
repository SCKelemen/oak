package asm

// The encoding table's shape (docs/spec/94-assembler.md §9). The table
// itself, `isaEncodings` in encodings_gen.go, is generated from Arm's A64 ISA
// XML by asm/internal/isagen: one entry per encoding on features the Apple
// M-series has, with the fixed bits, the named fields, and every assembler
// template reading mapped operand by operand to the fields it encodes.

// isaEncoding is one instruction encoding.
type isaEncoding struct {
	Name      string     // Arm's encoding name, e.g. ADD_32_addsub_shift
	Mnemonic  string     // lower case; aliases carry their own mnemonic
	Mask      uint32     // the fixed bits
	Value     uint32     // their values
	Fields    []isaField // the named bit fields
	Forms     []isaForm  // the template readings (optional groups present or absent)
	Alias     string     // for an alias: the template of the instruction it stands for
	AliasCond string     // and the condition under which the alias is preferred
	// Mode is the PSTATE the instruction needs (from Arm's Check* call):
	// "" anywhere, sm (streaming SVE mode), za (the ZA array enabled), smza
	// (both), nosm (Advanced SIMD illegal in streaming mode).
	Mode string
	// Flags marks an Execute that writes NZCV (whilelt, the SVE compares).
	Flags bool
}

// isaField is a named bit field: bits [Hi-Width+1, Hi].
type isaField struct {
	Name  string
	Hi    int
	Width int
}

// isaForm is one operand list, with the field values that operands the
// reading omits leave at their stated defaults (`ret` → Rn = 30).
type isaForm struct {
	Operands []isaOperand
	Defaults []isaDefault
}

type isaDefault struct {
	Field string
	Value uint32
}

// isaOperand is one template operand mapped to the fields it encodes.
//
// Kinds: gp (general register; Width 32/64, or 0 when a table on Fields[1:]
// chooses; SP/ZR say which spelling of register 31 is admitted), fp (scalar
// SIMD&FP register of Width bits, or 0 with Sizes on the size fields),
// vecarr (arranged vector: Fields[0] the register, Sub[0] the arrangement
// table, or Text a fixed arrangement), veclane (element: Fields the
// register fields, Sub the size table and the index), imm (Fields, range,
// Scale, Offset, Special), fimm (a floating-point immediate), label
// (PC-relative, Scale), table (a spelled word encoded by a value table),
// cond, sysreg, mem (Sub: base, then offset or index/extend/amount; Mode
// off/pre/post), list (Sub: the registers), text (a fixed word).
//
// Scalable kinds (SVE/SME): zreg (a z register; Text the fixed element
// letter or Sub[0] the size table; Scale/Offset the "times N"/"plus N" of
// a list head), zlane (a z element: Sub the size table and the idx
// immediate), preg (a predicate; Qual the fixed /M or /Z, or a <ZM> table
// in Sub), pnreg (a predicate-as-counter, Offset 8, optional idx), tile (a
// ZA tile: Fields, or Special fixed with the number in Offset), slice (a
// ZA slice or vector: Sub tile, hv, elem, idx, offs, group; Count the
// consecutive slices named), zlist (Count consecutive z registers from
// Sub[0], or one slice), tilemask (zero's list of tiles in Fields).
type isaOperand struct {
	Sym      string
	Kind     string
	Fields   []string
	Width    int
	SP, ZR   bool
	Min, Max int64
	HasRange bool
	Scale    int64
	Offset   int64
	Mode     string
	Text     string
	Special  string
	Count    int
	Qual     string
	Table    []isaTableRow
	Sizes    []isaTableRow
	Sub      []isaOperand
}

// isaTableRow maps a spelling to the bits of each field in the operand's
// field list ('x' marks a wildcard bit).
type isaTableRow struct {
	Bits []string
	Text string
}

// sysRegEncoding is a system register's op0:op1:CRn:CRm:op2 and whether MRS
// (Read) and MSR (Write) may name it. The table, `systemRegisterEncodings`
// in sysregs_gen.go, is generated from Arm's SysReg XML by
// asm/internal/sysreggen.
type sysRegEncoding struct {
	Op0, Op1, CRn, CRm, Op2 uint32
	Read, Write             bool
}
