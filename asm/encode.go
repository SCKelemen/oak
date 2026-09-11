package asm

import (
	"fmt"
	"math/bits"
	"regexp"
	"strconv"
	"strings"
)

// The native encoder (docs/spec/94-assembler.md §9): a checked asm function
// to AArch64 machine words, from the table Arm's ISA XML generated
// (encodings_gen.go). Each instruction is matched against the template
// readings of its mnemonic; the operands are written into the named fields
// exactly as Arm's operand explanations state (register numbers, scaled and
// offset immediates, value tables for spelled words, PC-relative labels);
// aliases whose operands are computed are rewritten to the instruction they
// stand for through Arm's own equivalence template. Encodability failures
// are errors, never silent.
//
// The C emission path remains the default; the encoder is checked against
// the host toolchain's assembler in encode_test.go.

// Relocation records a reference to a symbol outside the function.
type Relocation struct {
	Offset int    // byte offset of the instruction in the function
	Kind   string // branch26 (b/bl), condbr19 (b.cond/cbz/ldr literal), tbz14, adr21, adrp21
	Symbol string
}

// EncodeFunction encodes every instruction of a checked function, resolving
// labels within it; references to other symbols become relocations.
func EncodeFunction(fn *Function) ([]byte, []Relocation, error) {
	labels := map[string]int64{}
	offset := int64(0)
	for _, item := range fn.Items {
		switch it := item.(type) {
		case Label:
			labels[it.Name] = offset
		case Instruction:
			offset += 4
		case Align:
			offset = alignUp(offset, it.Bytes)
		}
	}
	var out []byte
	var relocs []Relocation
	offset = 0
	for _, item := range fn.Items {
		switch it := item.(type) {
		case Instruction:
			word, reloc, err := EncodeInstruction(it, offset, labels)
			if err != nil {
				return nil, nil, fmt.Errorf("%s:%d: %w", fn.Name, it.Line, err)
			}
			if reloc != nil {
				reloc.Offset = int(offset)
				relocs = append(relocs, *reloc)
			}
			out = append(out, byte(word), byte(word>>8), byte(word>>16), byte(word>>24))
			offset += 4
		case Align:
			for offset%it.Bytes != 0 {
				out = append(out, 0x1f, 0x20, 0x03, 0xd5) // nop
				offset += 4
			}
		}
	}
	return out, relocs, nil
}

func alignUp(n, to int64) int64 {
	if to <= 0 {
		return n
	}
	return (n + to - 1) / to * to
}

// EncodeInstruction encodes one instruction at byte offset pc within its
// function. labels resolve local symbols; any other symbol yields a
// relocation and a zero displacement.
func EncodeInstruction(instr Instruction, pc int64, labels map[string]int64) (uint32, *Relocation, error) {
	operands := instr.Operands
	if instr.Mnemonic == "b." {
		operands = append([]Operand{Condition{Code: instr.Cond}}, operands...)
	}
	// `mov` with an immediate is an assembler choice among movz, movn, and
	// orr with a bitmask; Arm's aliases each cover one case.
	if instr.Mnemonic == "mov" && len(operands) == 2 {
		if imm, isImm := operands[1].(Immediate); isImm {
			if reg, isReg := operands[0].(Register); isReg && reg.Class != ClassSP {
				return encodeMovImmediate(reg, imm.Value)
			}
		}
	}
	var lastErr error
	var reasons []string
	for i := range isaEncodings {
		enc := &isaEncodings[i]
		if enc.Mnemonic != instr.Mnemonic {
			continue
		}
		for f := range enc.Forms {
			word, reloc, err := encodeWith(enc, &enc.Forms[f], operands, pc, labels)
			if err == nil {
				return word, reloc, nil
			}
			if _, shape := err.(shapeMismatch); !shape {
				lastErr = err
			} else if len(reasons) < 12 {
				reasons = append(reasons, enc.Name+": "+err.Error())
			}
		}
	}
	// Scaled loads and stores fall back to their unscaled spelling when the
	// offset is not a multiple of the access size, as assemblers do.
	if unscaled, ok := unscaledSpelling[instr.Mnemonic]; ok {
		if mem, isMem := lastOperand(operands).(Memory); isMem && mem.Mode == MemOffset && mem.Index == nil {
			retry := instr
			retry.Mnemonic = unscaled
			if word, reloc, err := EncodeInstruction(retry, pc, labels); err == nil {
				return word, reloc, nil
			}
		}
	}
	if lastErr != nil {
		return 0, nil, lastErr
	}
	return 0, nil, fmt.Errorf("%s: no encoding admits operands %s (%s)", instr.Mnemonic, describeOperands(instr.Operands), strings.Join(reasons, "; "))
}

var unscaledSpelling = map[string]string{"ldr": "ldur", "str": "stur", "ldrb": "ldurb", "strb": "sturb", "ldrh": "ldurh", "strh": "sturh", "ldrsb": "ldursb", "ldrsh": "ldursh", "ldrsw": "ldursw", "prfm": "prfum"}

func lastOperand(ops []Operand) Operand {
	if len(ops) == 0 {
		return nil
	}
	return ops[len(ops)-1]
}

// shapeMismatch: the operands do not fit this reading (try the next); other
// errors are encodability failures of a reading that did fit.
type shapeMismatch struct{ why string }

func (m shapeMismatch) Error() string { return m.why }

func mismatch(format string, args ...interface{}) error {
	return shapeMismatch{fmt.Sprintf(format, args...)}
}

// encoder holds one attempt: the word under construction, the fields
// written so far, and the operand values bound by symbol (for aliases).
type encoder struct {
	enc      *isaEncoding
	word     uint32
	written  map[string]uint32
	bindings map[string]Operand
	values   map[string]int64
	esizes   []int64 // element widths the operands implied, in order
	// Modifiers the reading consumed: shifted/extended registers, and a
	// shifted immediate (`#imm, lsl #12`).
	consumed                 []Register
	consumedShiftedImmediate bool
	consumedExtend           bool
	sawSP                    bool
	writeImmh                bool // arrangement tables over immh write it (no shift immediate follows)
}

func encodeWith(enc *isaEncoding, form *isaForm, operands []Operand, pc int64, labels map[string]int64) (uint32, *Relocation, error) {
	e := &encoder{enc: enc, word: enc.Value, written: map[string]uint32{}, bindings: map[string]Operand{}, values: map[string]int64{}, writeImmh: true}
	for _, fop := range form.Operands {
		if fop.Special == "shift-immh" || fop.Special == "fbits" {
			e.writeImmh = false // the shift immediate carries the element size
		}
	}
	for _, d := range form.Defaults {
		if err := e.setField(d.Field, d.Value); err != nil {
			return 0, nil, err
		}
	}
	var reloc *Relocation
	oi := 0
	prev := Operand(nil)
	for fi := 0; fi < len(form.Operands); fi++ {
		fop := &form.Operands[fi]
		// Modifiers attach to the previous instruction operand.
		if fop.Kind == "table" && (fop.Sym == "<shift>" || fop.Sym == "<extend>") || fop.Kind == "text" && (fop.Text == "LSL" || fop.Text == "MSL") {
			if err := e.modifier(form.Operands, &fi, prev); err != nil {
				return 0, nil, err
			}
			continue
		}
		if oi >= len(operands) {
			return 0, nil, mismatch("too few operands")
		}
		op := operands[oi]
		oi++
		prev = op
		r, err := e.operand(fop, op, pc, labels)
		if err != nil {
			return 0, nil, err
		}
		if r != nil {
			reloc = r
		}
	}
	if oi != len(operands) {
		return 0, nil, mismatch("too many operands")
	}
	// A modifier the instruction carries that the reading did not consume
	// (e.g. `add x0, x1, x2, lsl #3` against the plain-register reading).
	for _, op := range operands {
		switch m := op.(type) {
		case Shifted:
			if !e.consumedModifier(m.Reg) {
				return 0, nil, mismatch("shift not admitted here")
			}
		case Extended:
			if !e.consumedModifier(m.Reg) {
				return 0, nil, mismatch("extend not admitted here")
			}
		case Immediate:
			if m.Shift != 0 && !e.consumedShiftedImmediate {
				return 0, nil, mismatch("shifted immediate not admitted here")
			}
		}
	}
	// Arm's rule for the extended-register forms: the extend may be omitted
	// only when a stack-pointer operand makes the form unambiguous (and
	// then reads as LSL); otherwise `add x0, x1, x2` is the shifted-register
	// instruction.
	if strings.Contains(enc.Name, "addsub_ext") && !e.consumedExtend {
		if !e.sawSP {
			return 0, nil, mismatch("extended-register form without an extend")
		}
		option := uint32(0b011) // UXTX/LSL
		if w, ok := e.values["width"]; ok && w == 32 {
			option = 0b010 // UXTW/LSL
		}
		if err := e.setField("option", option); err != nil {
			return 0, nil, err
		}
	}
	computed := false
	for _, fop := range form.Operands {
		if fop.Special == "computed" {
			computed = true
		}
	}
	if enc.Alias != "" {
		if computed {
			return e.alias(pc, labels) // the equivalence template computes the fields
		}
		holds, unbound := e.aliasCondHolds()
		if !holds {
			if unbound {
				// The condition names a field the alias's operands did not
				// write (`Rn == Rm` for cinc): the equivalence sets it.
				return e.alias(pc, labels)
			}
			return 0, nil, mismatch("alias condition %q does not hold", enc.AliasCond)
		}
	}
	if err := e.checkTables(); err != nil {
		return 0, nil, err
	}
	return e.word, reloc, nil
}

// operand writes one instruction operand through one template operand.
func (e *encoder) operand(fop *isaOperand, op Operand, pc int64, labels map[string]int64) (*Relocation, error) {
	e.bindings[fop.Sym] = op
	switch fop.Kind {
	case "gp":
		reg, ok := registerOf(op)
		if !ok {
			return nil, mismatch("%s wants a general register", fop.Sym)
		}
		return nil, e.gpRegister(fop, reg)
	case "fp":
		reg, ok := op.(Register)
		if !ok || reg.Class != ClassV || reg.Lane >= 0 || reg.Vec == "" {
			return nil, mismatch("%s wants a scalar SIMD&FP register", fop.Sym)
		}
		if _, arranged := vectorArrangements[reg.Vec]; arranged {
			return nil, mismatch("%s wants a scalar view", fop.Sym)
		}
		width := scalarVectorWidths[reg.Vec[0]] * 8
		letter := strings.ToUpper(reg.Vec[:1])
		if fop.Width != 0 {
			if width != fop.Width {
				return nil, mismatch("%s is %d bits", fop.Sym, fop.Width)
			}
			e.esizes = append(e.esizes, int64(width))
			if _, isWidth := e.values["width"]; !isWidth {
				e.values["width"] = int64(width)
			}
			return nil, e.setField(fop.Fields[0], uint32(reg.Num))
		}
		// Size chosen by a table on the remaining fields; a table on immh
		// only fixes the element size the shift immediate encodes later.
		if err := e.setField(fop.Fields[0], uint32(reg.Num)); err != nil {
			return nil, err
		}
		if len(fop.Fields) > 1 && fop.Fields[1] == "immh" {
			row, ok := tableRow(fop.Sizes, letter)
			if !ok {
				return nil, mismatch("%s does not admit %s", fop.Sym, letter)
			}
			e.esizes = append(e.esizes, int64(width))
			if e.writeImmh {
				return nil, e.writePattern("immh", row.Bits[0])
			}
			return nil, nil
		}
		return nil, e.table(fop.Fields[1:], fop.Sizes, letter, fop.Sym)
	case "vecarr":
		reg, ok := op.(Register)
		if !ok || reg.Class != ClassV || reg.Lane >= 0 {
			return nil, mismatch("%s wants an arranged vector", fop.Sym)
		}
		if _, arranged := vectorArrangements[reg.Vec]; !arranged {
			return nil, mismatch("%s wants an arranged vector", fop.Sym)
		}
		if err := e.setField(fop.Fields[0], uint32(reg.Num)); err != nil {
			return nil, err
		}
		arr := strings.ToUpper(reg.Vec)
		if fop.Text != "" {
			if arr != fop.Text {
				return nil, mismatch("%s wants arrangement %s", fop.Sym, fop.Text)
			}
			e.rememberElementSize(fop.Text)
			return nil, nil
		}
		if len(fop.Sub) == 0 {
			return nil, fmt.Errorf("%s: arrangement without a table", fop.Sym)
		}
		sub := &fop.Sub[0]
		if len(sub.Fields) >= 1 && sub.Fields[0] == "immh" {
			// Tables over immh (and Q): immh comes from the shift immediate
			// when one follows, else from the table; Q is written.
			row, ok := tableRow(sub.Table, arr)
			if !ok {
				return nil, mismatch("%s does not admit %s", fop.Sym, reg.Vec)
			}
			e.rememberElementSize(arr)
			if e.writeImmh {
				if err := e.writePattern("immh", row.Bits[0]); err != nil {
					return nil, err
				}
			}
			if len(sub.Fields) == 2 {
				return nil, e.writePattern(sub.Fields[1], row.Bits[1])
			}
			return nil, nil
		}
		return nil, e.table(sub.Fields, sub.Table, arr, fop.Sym)
	case "veclane":
		reg, ok := op.(Register)
		if !ok || reg.Class != ClassV || reg.Lane < 0 {
			return nil, mismatch("%s wants a vector element", fop.Sym)
		}
		return nil, e.lane(fop, reg)
	case "imm":
		imm, ok := op.(Immediate)
		if !ok {
			return nil, mismatch("%s wants an immediate", fop.Sym)
		}
		return nil, e.immediate(fop, imm)
	case "fimm":
		f, ok := op.(FloatImmediate)
		if !ok {
			return nil, mismatch("%s wants a floating-point immediate", fop.Sym)
		}
		return nil, e.floatImmediate(fop, f)
	case "label":
		sym, ok := op.(Symbol)
		if !ok {
			return nil, mismatch("%s wants a label", fop.Sym)
		}
		return e.label(fop, sym, pc, labels)
	case "cond":
		cond, ok := op.(Condition)
		if !ok {
			return nil, mismatch("%s wants a condition", fop.Sym)
		}
		return nil, e.condition(fop, cond.Code)
	case "table":
		text := ""
		switch v := op.(type) {
		case Option:
			text = strings.ToUpper(v.Name)
		case Immediate:
			if fop.Special == "table-or-imm" {
				return nil, e.writeFields(fop.Fields, uint64(v.Value))
			}
			text = "#" + strconv.FormatInt(v.Value, 10)
		case SysReg:
			text = strings.ToUpper(v.Name)
		case Register:
			text = strings.ToUpper(v.Text)
		default:
			return nil, mismatch("%s wants a spelled word", fop.Sym)
		}
		return nil, e.table(fop.Fields, fop.Table, text, fop.Sym)
	case "sysreg":
		reg, ok := op.(SysReg)
		if !ok {
			return nil, mismatch("%s wants a system register", fop.Sym)
		}
		return nil, e.sysreg(fop, reg.Name)
	case "mem":
		mem, ok := op.(Memory)
		if !ok {
			return nil, mismatch("%s wants a memory operand", fop.Sym)
		}
		return nil, e.memory(fop, mem)
	case "list":
		list, ok := op.(RegisterList)
		if !ok {
			return nil, mismatch("%s wants a register list", fop.Sym)
		}
		if len(list.Regs) != len(fop.Sub) {
			return nil, mismatch("%s wants %d registers", fop.Sym, len(fop.Sub))
		}
		for i, reg := range list.Regs {
			if reg.Num != (list.Regs[0].Num+i)%32 {
				return nil, fmt.Errorf("%s: register list must be consecutive", fop.Sym)
			}
		}
		return e.operand(&fop.Sub[0], list.Regs[0], pc, labels)
	case "text":
		return nil, e.fixedText(fop, op)
	}
	return nil, fmt.Errorf("%s: operand kind %q is not encodable", fop.Sym, fop.Kind)
}

func tableHas(rows []isaTableRow, text string) bool {
	_, ok := tableRow(rows, text)
	return ok
}

func tableRow(rows []isaTableRow, text string) (isaTableRow, bool) {
	text = strings.ToUpper(strings.TrimSpace(text))
	for _, row := range rows {
		if row.Text == text || row.Text == strings.TrimPrefix(text, "#") || "#"+row.Text == text {
			return row, true
		}
	}
	return isaTableRow{}, false
}

// registerOf unwraps a register from a plain, shifted, or extended operand.
func registerOf(op Operand) (Register, bool) {
	switch v := op.(type) {
	case Register:
		return v, true
	case Shifted:
		return v.Reg, true
	case Extended:
		return v.Reg, true
	}
	return Register{}, false
}

func (e *encoder) gpRegister(fop *isaOperand, reg Register) error {
	var num uint32
	width := 64
	switch {
	case reg.Class == ClassSP:
		if !fop.SP {
			return mismatch("%s does not admit sp", fop.Sym)
		}
		if fop.Width == 32 {
			return mismatch("%s is 32 bits; wsp is not modeled", fop.Sym)
		}
		num = 31
		e.sawSP = true
	case reg.Class == ClassX || reg.Class == ClassW:
		if reg.Num == 31 && !fop.ZR {
			return mismatch("%s does not admit the zero register", fop.Sym)
		}
		if reg.Class == ClassW {
			width = 32
		}
		if fop.Width != 0 && fop.Width != width {
			return mismatch("%s is %d bits", fop.Sym, fop.Width)
		}
		if fop.Width == 0 && len(fop.Table) > 0 {
			// <R><m>: the width must agree with the option field once the
			// extend is known; remembered and checked by checkTables.
			e.values["width:"+fop.Sym] = int64(width)
		}
		num = uint32(reg.Num)
	default:
		return mismatch("%s wants a general register", fop.Sym)
	}
	if _, isWidth := e.values["width"]; !isWidth && fop.Width != 0 {
		e.values["width"] = int64(fop.Width)
	}
	field := fop.Fields[0]
	if strings.HasPrefix(field, "+") {
		// <X(t+1)>: must be the register after the one in the named field.
		base, ok := e.written[field[1:]]
		if !ok || (base+1)%32 != num {
			return fmt.Errorf("%s must be the register after %s", fop.Sym, field[1:])
		}
		return nil
	}
	return e.setField(field, num)
}

// lane encodes `<Vm>.<Ts>[<index>]`: the element size table, the register
// (split over M:Rm for word and doubleword elements, Rm alone for
// halfwords), and the index bits over H, L, M as Arm's tables state.
func (e *encoder) lane(fop *isaOperand, reg Register) error {
	letter := strings.ToUpper(reg.Vec)
	if fop.Text != "" {
		// `.4B[i]` / `.2H[i]`: 32-bit groups of bytes or halfwords (the dot
		// products); the register carries the letter, the group is
		// indexed like a word element.
		if strings.TrimLeft(fop.Text, "0123456789") != letter {
			return mismatch("%s wants element size %s", fop.Sym, fop.Text)
		}
		if fop.Text == "4B" || fop.Text == "2H" {
			letter = "S"
		}
	}
	var indexOp *isaOperand
	for i := range fop.Sub {
		sub := &fop.Sub[i]
		switch {
		case sub.Kind == "table":
			if err := e.table(sub.Fields, sub.Table, letter, fop.Sym); err != nil {
				return err
			}
		case sub.Special == "index":
			indexOp = sub
		case sub.Kind == "text":
			want, _ := strconv.Atoi(sub.Text)
			if reg.Lane != want {
				return mismatch("%s wants lane %d", fop.Sym, want)
			}
		}
	}
	// The register's own fields: the size fields the tables write are not
	// part of the number ("(size :: M :: Rm)" names them together).
	var regFields []string
	for _, f := range fop.Fields {
		switch f {
		case "size", "sz", "Q", "immh":
			continue
		}
		regFields = append(regFields, f)
	}
	if indexOp == nil {
		return e.writeFields(regFields, uint64(reg.Num))
	}
	indexFields := strings.Join(indexOp.Fields, ":")
	if indexFields == "imm5" || strings.Contains(indexFields, "imm4") {
		if err := e.writeFields(regFields, uint64(reg.Num)); err != nil {
			return err
		}
		return e.laneIndexImm(indexOp, letter, reg.Lane)
	}
	// H:L:M-style. The register number's fifth bit lives in M for S and D
	// elements; for H (and B) elements M is an index bit and Rm is 4 bits.
	_, hasM := e.fieldDef("M")
	usesM := false
	for _, f := range indexOp.Fields {
		if f == "M" {
			usesM = true
		}
	}
	var n int
	switch letter {
	case "B":
		n = 4
	case "H":
		n = 3
	case "S":
		n = 2
	case "D":
		n = 1
	}
	// Arm's per-size formula, when the explanation tabulates one ("size
	// <index> 01 UInt(H:L:M) 10 UInt(H:L)"): the row whose size bits match
	// names the index fields.
	var order []string
	if len(indexOp.Table) > 0 {
		sizeFields := indexOp.Fields[:len(indexOp.Fields)-len(indexOrderFields(indexOp.Fields))]
		if len(sizeFields) == 0 {
			// The rows are keyed by the encoding's size field even when the
			// index's own field list omits it.
			for _, candidate := range []string{"size", "sz", "Q"} {
				if _, ok := e.fieldDef(candidate); ok {
					sizeFields = []string{candidate}
					break
				}
			}
		}
		for _, row := range indexOp.Table {
			if len(row.Bits) == len(sizeFields) && e.rowMatches(sizeFields, row.Bits) {
				order = strings.Split(row.Text, ":")
				break
			}
		}
		if len(order) > 0 {
			n = len(order)
			usesM = false
			for _, f := range order {
				if f == "M" {
					usesM = true
				}
			}
		}
	}
	if reg.Lane >= 1<<uint(n) {
		return fmt.Errorf("lane %d is outside a vector of %s", reg.Lane, letter)
	}
	if hasM && usesM && (letter == "S" || letter == "D") {
		if err := e.setField("M", uint32(reg.Num>>4)); err != nil {
			return err
		}
		if err := e.setField("Rm", uint32(reg.Num&15)); err != nil {
			return err
		}
	} else if hasM && usesM {
		if reg.Num > 15 {
			return fmt.Errorf("%s: element registers of %s are v0-v15", fop.Sym, letter)
		}
		if err := e.setField("Rm", uint32(reg.Num)); err != nil {
			return err
		}
	} else if err := e.writeFields(regFields, uint64(reg.Num)); err != nil {
		return err
	}
	if len(order) == 0 {
		order = indexOrderFields(indexOp.Fields)
	}
	if len(order) < n {
		return fmt.Errorf("%s: index of %d bits over fields %v", fop.Sym, n, indexOp.Fields)
	}
	return e.writeFields(order[:n], uint64(reg.Lane))
}

// indexOrderFields: the H, L, M index fields of a field list, in that order.
func indexOrderFields(fields []string) []string {
	var order []string
	for _, name := range []string{"H", "L", "M"} {
		for _, f := range fields {
			if f == name {
				order = append(order, name)
			}
		}
	}
	return order
}

// laneIndexImm: dup/ins/umov/smov indexes in imm5 (index above a size marker
// bit) and imm4 (index shifted by the element's byte width).
func (e *encoder) laneIndexImm(fop *isaOperand, letter string, lane int) error {
	bytesOf := map[string]int{"B": 1, "H": 2, "S": 4, "D": 8}[letter]
	if bytesOf == 0 {
		return fmt.Errorf("element size %s", letter)
	}
	if lane >= 16/bytesOf {
		return fmt.Errorf("lane %d is outside the register", lane)
	}
	shift := uint(bits.TrailingZeros(uint(bytesOf)))
	fields := strings.Join(fop.Fields, ":")
	if fields == "imm5" {
		return e.setField("imm5", uint32(lane)<<(shift+1)|uint32(bytesOf))
	}
	return e.setField("imm4", uint32(lane)<<shift)
}

// immediate writes a plain immediate: range, scale, offset, then the field.
func (e *encoder) immediate(fop *isaOperand, imm Immediate) error {
	e.values[fop.Sym] = imm.Value
	switch fop.Special {
	case "computed":
		return nil // the alias rewrite computes the field from this value
	case "index":
		// A byte index with per-arrangement formulas (ext's imm4): the
		// value goes in the last field named; the arrangement bounds it.
		return e.writeFields(fop.Fields[len(fop.Fields)-1:], uint64(imm.Value))
	case "bitmask":
		return e.bitmask(fop, imm.Value)
	case "wide":
		return e.wide(fop, imm)
	case "movi":
		return e.moviImmediate(fop, imm.Value)
	case "shift-immh":
		return e.shiftImmh(fop, imm.Value)
	case "fbits":
		return e.fbits(fop, imm.Value)
	case "sub64":
		if imm.Value < 1 || imm.Value > 64 {
			return fmt.Errorf("%s: %d is outside 1..64", fop.Sym, imm.Value)
		}
		return e.writeFields(fop.Fields, uint64(64-imm.Value))
	}
	if len(fop.Table) > 0 {
		return e.table(fop.Fields, fop.Table, "#"+strconv.FormatInt(imm.Value, 10), fop.Sym)
	}
	v := imm.Value
	if fop.HasRange && (v < fop.Min || v > fop.Max) {
		return fmt.Errorf("%s: %d is outside %d..%d", fop.Sym, v, fop.Min, fop.Max)
	}
	scale := fop.Scale
	if scale <= 0 {
		scale = 1
	}
	if v%scale != 0 {
		return fmt.Errorf("%s: %d is not a multiple of %d", fop.Sym, v, scale)
	}
	encoded := v/scale - fop.Offset
	if len(fop.Fields) == 0 {
		return fmt.Errorf("%s: immediate with no field", fop.Sym)
	}
	width := e.fieldsWidth(fop.Fields)
	if encoded < 0 {
		encoded &= (1 << uint(width)) - 1 // two's complement in the field
	}
	if encoded >= 1<<uint(width) {
		return fmt.Errorf("%s: %d does not fit %d bits", fop.Sym, v, width)
	}
	return e.writeFields(fop.Fields, uint64(encoded))
}

// wide: a 16-bit immediate (movz/movn/movk); the shift is a modifier.
func (e *encoder) wide(fop *isaOperand, imm Immediate) error {
	if imm.Value < 0 || imm.Value > 0xffff {
		return fmt.Errorf("%s: %d is not a 16-bit immediate", fop.Sym, imm.Value)
	}
	return e.writeFields([]string{"imm16"}, uint64(imm.Value))
}

// bitmask encodes a logical immediate (N:immr:imms), the inverse of Arm's
// DecodeBitMasks: the value must be a rotation of a run of ones replicated
// across elements of 2, 4, 8, 16, 32, or 64 bits.
func (e *encoder) bitmask(fop *isaOperand, value int64) error {
	width := 64
	if w, ok := e.values["width"]; ok {
		width = int(w)
	}
	if width == 32 {
		value &= 0xffffffff // a negative spelling of a 32-bit pattern
	}
	n, immr, imms, ok := encodeBitmask(uint64(value), width)
	if !ok {
		return fmt.Errorf("%s: %#x is not a %d-bit bitmask immediate", fop.Sym, uint64(value), width)
	}
	if _, hasN := e.fieldDef("N"); hasN {
		if err := e.setField("N", n); err != nil {
			return err
		}
	} else if n != 0 {
		return fmt.Errorf("%s: %#x needs a 64-bit element", fop.Sym, uint64(value))
	}
	if err := e.setField("immr", immr); err != nil {
		return err
	}
	return e.setField("imms", imms)
}

// encodeBitmask returns N, immr, imms for value at the register width.
func encodeBitmask(value uint64, width int) (n, immr, imms uint32, ok bool) {
	if width == 32 {
		if value>>32 != 0 {
			return 0, 0, 0, false
		}
		value |= value << 32
	}
	if value == 0 || value == ^uint64(0) {
		return 0, 0, 0, false
	}
	// The element size: the smallest e such that value repeats every e bits.
	size := 64
	for size > 2 {
		half := size / 2
		mask := uint64(1)<<uint(half) - 1
		if value&mask != (value>>uint(half))&mask {
			break
		}
		size = half
	}
	if width == 32 && size == 64 {
		return 0, 0, 0, false
	}
	mask := ^uint64(0)
	if size < 64 {
		mask = uint64(1)<<uint(size) - 1
	}
	elem := value & mask
	ones := bits.OnesCount64(elem)
	run := ^uint64(0)
	if ones < 64 {
		run = uint64(1)<<uint(ones) - 1
	}
	// Rotate the element right until it is the run of ones at bit 0.
	rot := -1
	for i := 0; i < size; i++ {
		if elem == run {
			rot = i
			break
		}
		elem = ((elem >> 1) | (elem << uint(size-1))) & mask
	}
	if rot < 0 {
		return 0, 0, 0, false
	}
	// The value is the run rotated left by rot, i.e. rotated right by size-rot.
	immr = uint32((size - rot) % size)
	switch size {
	case 64:
		n, imms = 1, uint32(ones-1)
	case 32:
		imms = uint32(ones - 1)
	case 16:
		imms = 0b100000 | uint32(ones-1)
	case 8:
		imms = 0b110000 | uint32(ones-1)
	case 4:
		imms = 0b111000 | uint32(ones-1)
	case 2:
		imms = 0b111100 | uint32(ones-1)
	}
	return n, immr, imms, true
}

// moviImmediate: the 8-bit modified immediate of movi/mvni/orr/bic (vector),
// and the 64-bit byte-mask form (every byte 0x00 or 0xff).
func (e *encoder) moviImmediate(fop *isaOperand, value int64) error {
	if fop.Sym == "#<imm>" {
		var imm8 uint64
		for i := 0; i < 8; i++ {
			b := (uint64(value) >> uint(8*i)) & 0xff
			switch b {
			case 0xff:
				imm8 |= 1 << uint(i)
			case 0:
			default:
				return fmt.Errorf("%s: %#x is not a byte mask", fop.Sym, uint64(value))
			}
		}
		return e.writeFields(fop.Fields, imm8)
	}
	if value < 0 || value > 0xff {
		return fmt.Errorf("%s: %d is not an 8-bit immediate", fop.Sym, value)
	}
	return e.writeFields(fop.Fields, uint64(value))
}

// shiftImmh: vector shift amounts in immh:immb, which also carry the element
// size: left shifts encode esize+shift, right shifts 2*esize-shift. The
// element is the destination's for narrowing shifts and the source's for
// the long ones.
func (e *encoder) shiftImmh(fop *isaOperand, value int64) error {
	if len(e.esizes) == 0 {
		return fmt.Errorf("%s: element size unknown before the shift", fop.Sym)
	}
	esize := e.esizes[0]
	name := e.enc.Mnemonic
	if strings.Contains(name, "shll") || strings.Contains(name, "xtl") {
		esize = e.esizes[len(e.esizes)-1] // widening: the source element
	}
	left := strings.Contains(name, "shl") || strings.HasPrefix(name, "sli") || strings.HasPrefix(name, "sqshlu")
	var code int64
	if left {
		if value < 0 || value >= esize {
			return fmt.Errorf("%s: shift %d is outside 0..%d", fop.Sym, value, esize-1)
		}
		code = esize + value
	} else {
		if value < 1 || value > esize {
			return fmt.Errorf("%s: shift %d is outside 1..%d", fop.Sym, value, esize)
		}
		code = 2*esize - value
	}
	return e.writeFields([]string{"immh", "immb"}, uint64(code))
}

// fbits: fixed-point fraction bits in immh:immb as 2*esize-fbits.
func (e *encoder) fbits(fop *isaOperand, value int64) error {
	if len(e.esizes) == 0 {
		return fmt.Errorf("%s: element size unknown before the fraction bits", fop.Sym)
	}
	esize := e.esizes[0]
	if value < 1 || value > esize {
		return fmt.Errorf("%s: %d fraction bits is outside 1..%d", fop.Sym, value, esize)
	}
	return e.writeFields([]string{"immh", "immb"}, uint64(2*esize-value))
}

// floatImmediate encodes the 8-bit modified floating-point immediate.
func (e *encoder) floatImmediate(fop *isaOperand, f FloatImmediate) error {
	if fop.Kind == "text" || fop.Text == "#0.0" {
		if f.Value != 0 {
			return fmt.Errorf("%s: only #0.0 is admitted", fop.Sym)
		}
		return nil
	}
	imm8, ok := encodeFP8(f.Value)
	if !ok {
		return fmt.Errorf("%s: %g is not a modified floating-point immediate", fop.Sym, f.Value)
	}
	fields := fop.Fields
	if len(fields) == 0 {
		fields = []string{"imm8"}
	}
	return e.writeFields(fields, uint64(imm8))
}

// encodeFP8 finds the 8-bit immediate whose expansion is v (sign, 3-bit
// exponent, 4-bit fraction).
func encodeFP8(v float64) (uint32, bool) {
	for imm := 0; imm < 256; imm++ {
		if expandFP8(uint32(imm)) == v {
			return uint32(imm), true
		}
	}
	return 0, false
}

// expandFP8: (-1)^a × (16+efgh)/16 × 2^(bcd, with b inverted, minus 3).
func expandFP8(imm uint32) float64 {
	sign := (imm >> 7) & 1
	frac := imm & 0xf
	e3 := int(((imm>>6)&1)^1)<<2 | int((imm>>4)&3)
	value := float64(16+frac) / 16
	for shift := e3 - 3; shift > 0; shift-- {
		value *= 2
	}
	for shift := e3 - 3; shift < 0; shift++ {
		value /= 2
	}
	if sign == 1 {
		value = -value
	}
	return value
}

// label writes a PC-relative displacement, or records a relocation.
func (e *encoder) label(fop *isaOperand, sym Symbol, pc int64, labels map[string]int64) (*Relocation, error) {
	fields := strings.Join(fop.Fields, ":")
	kind := map[string]string{"imm26": "branch26", "imm19": "condbr19", "imm14": "tbz14", "immhi:immlo": "adr21"}[fields]
	if fop.Scale == 4096 {
		kind = "adrp21"
	}
	target, local := labels[sym.Name]
	if !local {
		return &Relocation{Kind: kind, Symbol: sym.Name}, nil
	}
	disp := target - pc
	scale := fop.Scale
	if scale <= 0 {
		scale = 1
	}
	if disp%scale != 0 {
		return nil, fmt.Errorf("label %s: displacement %d is not a multiple of %d", sym.Name, disp, scale)
	}
	if fop.HasRange && (disp < fop.Min || disp > fop.Max) {
		return nil, fmt.Errorf("label %s: displacement %d is out of range", sym.Name, disp)
	}
	encoded := disp / scale
	width := e.fieldsWidth(fop.Fields)
	if encoded < 0 {
		encoded &= (1 << uint(width)) - 1
	}
	return nil, e.writeFields(fop.Fields, uint64(encoded))
}

var conditionCodesByName = map[string]uint32{"eq": 0, "ne": 1, "cs": 2, "hs": 2, "cc": 3, "lo": 3, "mi": 4, "pl": 5, "vs": 6, "vc": 7, "hi": 8, "ls": 9, "ge": 10, "lt": 11, "gt": 12, "le": 13, "al": 14, "nv": 15}

func (e *encoder) condition(fop *isaOperand, code string) error {
	v, ok := conditionCodesByName[strings.ToLower(code)]
	if !ok {
		return fmt.Errorf("unknown condition %q", code)
	}
	if fop.Sym == "<invcond>" {
		if v >= 14 {
			return fmt.Errorf("%s does not admit %s", fop.Sym, code)
		}
		v ^= 1
	}
	e.values[fop.Sym] = int64(v)
	return e.writeFields(fop.Fields, uint64(v))
}

// sysreg encodes `S<op0>_<op1>_<Cn>_<Cm>_<op2>` or a named system register.
func (e *encoder) sysreg(fop *isaOperand, name string) error {
	name = strings.ToLower(name)
	var op0, op1, crn, crm, op2 uint32
	if strings.HasPrefix(name, "s") && strings.Count(name, "_") == 4 {
		parts := strings.Split(name[1:], "_")
		vals := make([]uint32, 5)
		for i, p := range parts {
			p = strings.TrimPrefix(p, "c")
			v, err := strconv.Atoi(p)
			if err != nil {
				return fmt.Errorf("system register %q", name)
			}
			vals[i] = uint32(v)
		}
		op0, op1, crn, crm, op2 = vals[0], vals[1], vals[2], vals[3], vals[4]
	} else {
		enc, ok := systemRegisterEncodings[name]
		if !ok {
			return fmt.Errorf("system register %q is not one Arm's SysReg release names (spell it S<op0>_<op1>_<Cn>_<Cm>_<op2>)", name)
		}
		if e.enc.Mnemonic == "mrs" && !enc.Read {
			return fmt.Errorf("system register %s is not readable", name)
		}
		if e.enc.Mnemonic == "msr" && !enc.Write {
			return fmt.Errorf("system register %s is not writable", name)
		}
		op0, op1, crn, crm, op2 = enc.Op0, enc.Op1, enc.CRn, enc.CRm, enc.Op2
	}
	if op0 < 2 || op0 > 3 {
		return fmt.Errorf("system register %q: op0 must be 2 or 3", name)
	}
	for _, w := range []struct {
		field string
		value uint32
	}{{"o0", op0 - 2}, {"op1", op1}, {"CRn", crn}, {"CRm", crm}, {"op2", op2}} {
		if err := e.setField(w.field, w.value); err != nil {
			return err
		}
	}
	return nil
}

// memory writes a memory operand: base, then offset or index with extend
// and amount, in the reading's addressing mode.
func (e *encoder) memory(fop *isaOperand, mem Memory) error {
	mode := map[MemMode]string{MemOffset: "off", MemPreIndex: "pre", MemPostIndex: "post"}[mem.Mode]
	if mode != fop.Mode {
		return mismatch("%s: addressing mode", fop.Sym)
	}
	if len(fop.Sub) == 0 {
		return fmt.Errorf("%s: memory operand without a base", fop.Sym)
	}
	if err := e.gpRegister(&fop.Sub[0], mem.Base); err != nil {
		return err
	}
	hasOffset, hasIndex, hasAmount := false, false, false
	extend := strings.ToUpper(mem.Extend)
	if extend == "" && mem.Index != nil {
		extend = "UXTW"
		if mem.Index.Class == ClassX {
			extend = "LSL"
		}
	}
	for i := 1; i < len(fop.Sub); i++ {
		sub := &fop.Sub[i]
		switch sub.Sym {
		case "off":
			hasOffset = true
			if mem.Index != nil {
				return mismatch("%s: register offset", fop.Sym)
			}
			if err := e.immediate(sub, Immediate{Value: mem.Offset}); err != nil {
				return err
			}
		case "idx":
			hasIndex = true
			if mem.Index == nil {
				return mismatch("%s: immediate offset", fop.Sym)
			}
			idx := *mem.Index
			if sub.Width == 64 && idx.Class != ClassX || sub.Width == 32 && idx.Class != ClassW {
				return mismatch("%s: index register width", fop.Sym)
			}
			if err := e.setField("Rm", uint32(idx.Num)); err != nil {
				return err
			}
		case "<extend>":
			if err := e.table(sub.Fields, sub.Table, extend, fop.Sym); err != nil {
				return err
			}
			if mem.Index != nil {
				wantW := extend == "UXTW" || extend == "SXTW"
				if wantW != (mem.Index.Class == ClassW) {
					return mismatch("%s: %s takes a %s index", fop.Sym, extend, map[bool]string{true: "w", false: "x"}[wantW])
				}
			}
		case "LSL":
			if extend != "LSL" {
				return mismatch("%s: this reading spells LSL", fop.Sym)
			}
		case "<amount>":
			hasAmount = true
			if len(sub.Table) > 0 {
				if err := e.table(sub.Fields, sub.Table, "#"+strconv.Itoa(mem.Shift), fop.Sym); err != nil {
					return err
				}
			} else if err := e.immediate(sub, Immediate{Value: int64(mem.Shift)}); err != nil {
				return err
			}
		}
	}
	if !hasOffset && !hasIndex && (mem.Offset != 0 || mem.Index != nil) {
		return mismatch("%s: base only", fop.Sym)
	}
	if hasIndex && !hasAmount && mem.Shift != 0 {
		return mismatch("%s: shift not admitted", fop.Sym)
	}
	return nil
}

// modifier consumes `<shift> #<amount>` / `<extend> #<amount>` / `LSL #<n>`
// readings against the modifier carried by the previous operand.
func (e *encoder) modifier(ops []isaOperand, fi *int, prev Operand) error {
	fop := &ops[*fi]
	nextImm := func() (*isaOperand, bool) {
		if *fi+1 < len(ops) && ops[*fi+1].Kind == "imm" {
			*fi++
			return &ops[*fi], true
		}
		return nil, false
	}
	switch fop.Sym {
	case "<shift>":
		if imm, isImm := prev.(Immediate); isImm {
			// `#<imm>{, <shift>}` of add/sub: the table spells LSL #0 / LSL #12.
			if imm.MSL {
				return mismatch("msl on an add/sub immediate")
			}
			e.consumedShiftedImmediate = true
			return e.table(fop.Fields, fop.Table, "LSL #"+strconv.FormatInt(imm.Shift, 10), fop.Sym)
		}
		sh, ok := prev.(Shifted)
		if !ok {
			return mismatch("shift wants a shifted register")
		}
		e.consumed = append(e.consumed, sh.Reg)
		if err := e.table(fop.Fields, fop.Table, strings.ToUpper(sh.Kind), fop.Sym); err != nil {
			return err
		}
		if next, ok := nextImm(); ok {
			return e.immediate(next, Immediate{Value: sh.Amount})
		}
		return nil
	case "<extend>":
		ext, ok := prev.(Extended)
		if !ok {
			return mismatch("extend wants an extended register")
		}
		e.consumed = append(e.consumed, ext.Reg)
		e.consumedExtend = true
		if err := e.table(fop.Fields, fop.Table, strings.ToUpper(ext.Kind), fop.Sym); err != nil {
			return err
		}
		if next, ok := nextImm(); ok {
			return e.immediate(next, Immediate{Value: ext.Amount})
		}
		if ext.Amount != 0 {
			return mismatch("extend amount not admitted here")
		}
		return nil
	}
	// `LSL #<n>` / `MSL #<n>` after an immediate (movz/movk/movn, the
	// vector immediates), or `LSL #<amount>` on a register spelled so.
	if imm, isImm := prev.(Immediate); isImm {
		if imm.MSL != (fop.Text == "MSL") {
			return mismatch("%s wants the %s shift", fop.Sym, strings.ToLower(fop.Text))
		}
		e.consumedShiftedImmediate = true
		if *fi+1 < len(ops) {
			next := &ops[*fi+1]
			switch next.Kind {
			case "imm":
				*fi++
				return e.immediate(next, Immediate{Value: imm.Shift})
			case "table":
				*fi++
				return e.table(next.Fields, next.Table, strconv.FormatInt(imm.Shift, 10), next.Sym)
			case "text":
				*fi++
				want, _ := strconv.ParseInt(strings.TrimPrefix(next.Text, "#"), 10, 64)
				if imm.Shift != want {
					return mismatch("shift %d", want)
				}
				return nil
			}
		}
		return nil
	}
	sh, ok := prev.(Shifted)
	if !ok || strings.ToUpper(sh.Kind) != fop.Text {
		return mismatch("%s wants a shifted operand", fop.Text)
	}
	e.consumed = append(e.consumed, sh.Reg)
	if next, ok := nextImm(); ok {
		return e.immediate(next, Immediate{Value: sh.Amount})
	}
	return nil
}

func (e *encoder) consumedModifier(reg Register) bool {
	for _, r := range e.consumed {
		if r.Class == reg.Class && r.Num == reg.Num {
			return true
		}
	}
	return false
}

// fixedText matches a literal word of the template: a register (WZR, XZR,
// WSP, SP in alias targets), `#0`, or an option word.
func (e *encoder) fixedText(fop *isaOperand, op Operand) error {
	want := strings.ToUpper(fop.Text)
	switch v := op.(type) {
	case Register:
		if strings.ToUpper(v.Text) == want {
			return nil
		}
		if (want == "WZR" && v.Class == ClassW || want == "XZR" && v.Class == ClassX) && v.Num == 31 {
			return nil
		}
		if want == "SP" && v.Class == ClassSP {
			return nil
		}
	case Immediate:
		if want == "#"+strconv.FormatInt(v.Value, 10) {
			return nil
		}
	case FloatImmediate:
		if want == "#0.0" && v.Value == 0 {
			return nil
		}
	case Option:
		if strings.ToUpper(v.Name) == want {
			return nil
		}
	}
	return mismatch("%s wants %s", fop.Sym, fop.Text)
}

// table writes the bits a spelled word maps to; rows may name several
// fields, and 'x' bits are wildcards left as already written.
func (e *encoder) table(fields []string, rows []isaTableRow, text, sym string) error {
	row, ok := tableRow(rows, text)
	if !ok {
		return mismatch("%s: %s is not one of its spellings", sym, text)
	}
	if len(row.Bits) != len(fields) {
		return fmt.Errorf("%s: table row for %s names %d fields, expected %d", sym, text, len(row.Bits), len(fields))
	}
	for i, field := range fields {
		if err := e.writePattern(field, row.Bits[i]); err != nil {
			return err
		}
	}
	e.rememberElementSize(row.Text)
	return nil
}

// writePattern writes a bit pattern ('x' bits untouched) into a field.
func (e *encoder) writePattern(field, pattern string) error {
	if !strings.ContainsRune(pattern, 'x') {
		v, err := strconv.ParseUint(pattern, 2, 32)
		if err != nil {
			return fmt.Errorf("table bits %q", pattern)
		}
		return e.setField(field, uint32(v))
	}
	low, width, ok := e.fieldBits(field)
	if !ok {
		return fmt.Errorf("encoding %s has no field %q", e.enc.Name, field)
	}
	for b := 0; b < len(pattern) && b < width; b++ {
		ch := pattern[b]
		if ch == 'x' {
			continue
		}
		pos := uint(low + width - 1 - b)
		e.word &^= 1 << pos
		if ch == '1' {
			e.word |= 1 << pos
		}
	}
	return nil
}

// rememberElementSize keeps the element width an arrangement implies, for
// the vector shift and fixed-point immediates that follow.
func (e *encoder) rememberElementSize(text string) {
	if _, isArr := vectorArrangements[strings.ToLower(text)]; !isArr {
		return
	}
	switch text[len(text)-1] {
	case 'B':
		e.esizes = append(e.esizes, 8)
	case 'H':
		e.esizes = append(e.esizes, 16)
	case 'S':
		e.esizes = append(e.esizes, 32)
	case 'D':
		e.esizes = append(e.esizes, 64)
	}
}

// checkTables verifies the register-width tables (`<R><m>`) against the
// option bits the extend wrote.
func (e *encoder) checkTables() error {
	for key, width := range e.values {
		if !strings.HasPrefix(key, "width:") {
			continue
		}
		sym := strings.TrimPrefix(key, "width:")
		for _, form := range e.enc.Forms {
			for _, fop := range form.Operands {
				if fop.Sym != sym || len(fop.Table) == 0 || len(fop.Fields) < 2 {
					continue
				}
				letter := "X"
				if width == 32 {
					letter = "W"
				}
				for _, row := range fop.Table {
					if e.rowMatches(fop.Fields[1:], row.Bits) {
						if row.Text != letter {
							return mismatch("%s: register width %s does not match the extend", sym, letter)
						}
						return nil
					}
				}
				return mismatch("%s: no width for the extend written", sym)
			}
		}
	}
	return nil
}

func (e *encoder) rowMatches(fields []string, bitsPerField []string) bool {
	if len(fields) != len(bitsPerField) {
		return false
	}
	for i, field := range fields {
		pattern := bitsPerField[i]
		low, width, ok := e.fieldBits(field)
		if !ok {
			return false
		}
		for b := 0; b < len(pattern) && b < width; b++ {
			if pattern[b] == 'x' {
				continue
			}
			bit := (e.word >> uint(low+width-1-b)) & 1
			if (pattern[b] == '1') != (bit == 1) {
				return false
			}
		}
	}
	return true
}

// ---- alias conditions -------------------------------------------------------------

// aliasCondHolds evaluates Arm's alias condition over the fields written:
// `Rd == '11111' || Rn == '11111'`, `UInt(imms) < UInt(immr)`,
// `!(IsZero(imm16) && hw != '00')`, `Unconditionally`, `Never`. unbound
// reports that the condition read a field no operand wrote. An unparseable
// condition counts as holding.
func (e *encoder) aliasCondHolds() (holds, unbound bool) {
	cond := strings.TrimSpace(e.enc.AliasCond)
	switch cond {
	case "", "Unconditionally":
		return true, false
	case "Never":
		return false, true
	}
	p := &condParser{s: cond, e: e}
	v, err := p.or()
	if err != nil || p.rest() != "" {
		return true, false
	}
	return v, p.unbound
}

type condParser struct {
	s       string
	i       int
	e       *encoder
	unbound bool
}

func (p *condParser) rest() string { return strings.TrimSpace(p.s[p.i:]) }

func (p *condParser) skip() {
	for p.i < len(p.s) && p.s[p.i] == ' ' {
		p.i++
	}
}

func (p *condParser) or() (bool, error) {
	v, err := p.and()
	if err != nil {
		return false, err
	}
	for {
		p.skip()
		if !strings.HasPrefix(p.s[p.i:], "||") {
			return v, nil
		}
		p.i += 2
		w, err := p.and()
		if err != nil {
			return false, err
		}
		v = v || w
	}
}

func (p *condParser) and() (bool, error) {
	v, err := p.not()
	if err != nil {
		return false, err
	}
	for {
		p.skip()
		if !strings.HasPrefix(p.s[p.i:], "&&") {
			return v, nil
		}
		p.i += 2
		w, err := p.not()
		if err != nil {
			return false, err
		}
		v = v && w
	}
}

func (p *condParser) not() (bool, error) {
	p.skip()
	if p.i < len(p.s) && p.s[p.i] == '!' && !strings.HasPrefix(p.s[p.i:], "!=") {
		p.i++
		v, err := p.not()
		return !v, err
	}
	if p.i < len(p.s) && p.s[p.i] == '(' {
		p.i++
		v, err := p.or()
		if err != nil {
			return false, err
		}
		p.skip()
		if p.i >= len(p.s) || p.s[p.i] != ')' {
			return false, fmt.Errorf("missing )")
		}
		p.i++
		return v, nil
	}
	return p.compare()
}

func (p *condParser) compare() (bool, error) {
	p.skip()
	if strings.HasPrefix(p.s[p.i:], "IsZero(") {
		p.i += len("IsZero(")
		v, err := p.value()
		if err != nil {
			return false, err
		}
		p.skip()
		if p.i >= len(p.s) || p.s[p.i] != ')' {
			return false, fmt.Errorf("missing )")
		}
		p.i++
		return v == 0, nil
	}
	if strings.HasPrefix(p.s[p.i:], "Unconditionally") {
		p.i += len("Unconditionally")
		return true, nil
	}
	left, err := p.value()
	if err != nil {
		return false, err
	}
	p.skip()
	var op string
	for _, candidate := range []string{"==", "!=", "<=", ">=", "<", ">"} {
		if strings.HasPrefix(p.s[p.i:], candidate) {
			op = candidate
			break
		}
	}
	if op == "" {
		return false, fmt.Errorf("comparison expected at %q", p.s[p.i:])
	}
	p.i += len(op)
	right, err := p.value()
	if err != nil {
		return false, err
	}
	switch op {
	case "==":
		return left == right, nil
	case "!=":
		return left != right, nil
	case "<":
		return left < right, nil
	case ">":
		return left > right, nil
	case "<=":
		return left <= right, nil
	}
	return left >= right, nil
}

// value: UInt(F), F, 'bits', a number, with + and - between them.
func (p *condParser) value() (int64, error) {
	v, err := p.atom()
	if err != nil {
		return 0, err
	}
	for {
		p.skip()
		if p.i < len(p.s) && (p.s[p.i] == '+' || p.s[p.i] == '-') {
			opch := p.s[p.i]
			p.i++
			w, err := p.atom()
			if err != nil {
				return 0, err
			}
			if opch == '+' {
				v += w
			} else {
				v -= w
			}
			continue
		}
		return v, nil
	}
}

func (p *condParser) atom() (int64, error) {
	p.skip()
	if p.i >= len(p.s) {
		return 0, fmt.Errorf("value expected")
	}
	if strings.HasPrefix(p.s[p.i:], "UInt(") {
		p.i += len("UInt(")
		v, err := p.atom()
		if err != nil {
			return 0, err
		}
		p.skip()
		if p.i >= len(p.s) || p.s[p.i] != ')' {
			return 0, fmt.Errorf("missing )")
		}
		p.i++
		return v, nil
	}
	if p.s[p.i] == '\'' {
		end := strings.IndexByte(p.s[p.i+1:], '\'')
		if end < 0 {
			return 0, fmt.Errorf("unterminated bits")
		}
		v, err := strconv.ParseInt(p.s[p.i+1:p.i+1+end], 2, 64)
		p.i += end + 2
		return v, err
	}
	j := p.i
	for j < len(p.s) && (p.s[j] >= 'a' && p.s[j] <= 'z' || p.s[j] >= 'A' && p.s[j] <= 'Z' || p.s[j] >= '0' && p.s[j] <= '9' || p.s[j] == '_') {
		j++
	}
	if j == p.i {
		return 0, fmt.Errorf("unexpected %q", p.s[p.i:])
	}
	tok := p.s[p.i:j]
	p.i = j
	if n, err := strconv.ParseInt(tok, 10, 64); err == nil {
		return n, nil
	}
	if _, ok := p.e.fieldDef(tok); ok {
		if _, written := p.e.written[tok]; !written {
			low, width, _ := p.e.fieldBits(tok)
			if p.e.enc.Mask&(uint32(1<<uint(width)-1)<<uint(low)) == 0 {
				p.unbound = true // neither an operand nor a fixed bit set it
			}
		}
		return int64(p.e.fieldValue(tok)), nil
	}
	return 0, fmt.Errorf("unknown field %s", tok)
}

// fieldValue reads a field from the word under construction.
func (e *encoder) fieldValue(name string) uint32 {
	low, width, ok := e.fieldBits(name)
	if !ok {
		return 0
	}
	return (e.word >> uint(low)) & (1<<uint(width) - 1)
}

// ---- alias rewriting ---------------------------------------------------------

// alias rewrites the matched alias to the instruction it stands for, via
// Arm's equivalence template with the bound operands substituted and its
// immediate expressions evaluated, and encodes that.
func (e *encoder) alias(pc int64, labels map[string]int64) (uint32, *Relocation, error) {
	var lastErr error
	for _, reading := range expandOptionalGroups(e.enc.Alias) {
		mnemonic, text := splitAliasTemplate(reading)
		mnemonic = strings.ToLower(mnemonic)
		// A `{2}` in the target follows the alias's own spelling.
		if strings.Contains(e.enc.Alias, "{2}") && strings.HasSuffix(e.enc.Mnemonic, "2") != strings.HasSuffix(mnemonic, "2") {
			continue
		}
		operands, err := e.aliasOperands(splitTopLevel(text))
		if err != nil {
			lastErr = err
			continue
		}
		target := Instruction{Mnemonic: mnemonic, Operands: operands}
		if strings.HasPrefix(target.Mnemonic, "b.") {
			target.Mnemonic = "b."
		}
		word, reloc, err := EncodeInstruction(target, pc, labels)
		if err == nil {
			return word, reloc, nil
		}
		lastErr = err
	}
	if lastErr == nil {
		lastErr = fmt.Errorf("no reading of the equivalence applies")
	}
	return 0, nil, fmt.Errorf("%s: alias %q: %w", e.enc.Mnemonic, e.enc.Alias, lastErr)
}

func expandOptionalGroups(s string) []string {
	depth, start := 0, -1
	for i, r := range s {
		switch r {
		case '{':
			if depth == 0 && !(i+1 < len(s) && s[i+1] == ' ') {
				start = i
			}
			depth++
		case '}':
			depth--
			if depth == 0 && start >= 0 && s[start+1] != ' ' {
				inner := s[start+1 : i]
				with := s[:start] + inner + s[i+1:]
				without := s[:start] + s[i+1:]
				return append(expandOptionalGroups(with), expandOptionalGroups(without)...)
			}
		}
	}
	return []string{s}
}

func splitAliasTemplate(t string) (string, string) {
	if i := strings.IndexByte(t, ' '); i >= 0 {
		return t[:i], strings.TrimSpace(t[i+1:])
	}
	return t, ""
}

func splitTopLevel(s string) []string {
	var out []string
	depth := 0
	last := 0
	for i, r := range s {
		switch r {
		case '(', '[', '<', '{':
			depth++
		case ')', ']', '>', '}':
			depth--
		case ',':
			if depth == 0 {
				out = append(out, strings.TrimSpace(s[last:i]))
				last = i + 1
			}
		}
	}
	if rest := strings.TrimSpace(s[last:]); rest != "" {
		out = append(out, rest)
	}
	return out
}

// aliasOperands realizes the tokens of one equivalence reading. A modifier
// token (`<shift> #<amount>`, `<extend> #<amount>`) is satisfied by the
// modifier the bound register already carries; a reading that spells a
// modifier the operands lack, or omits one they carry, does not apply.
func (e *encoder) aliasOperands(tokens []string) ([]Operand, error) {
	var operands []Operand
	spelledModifier := false
	for _, tok := range tokens {
		switch {
		case strings.HasPrefix(tok, "<shift>"), strings.HasPrefix(tok, "<extend>"):
			spelledModifier = true
			if len(operands) == 0 {
				return nil, fmt.Errorf("modifier %q without an operand", tok)
			}
			switch operands[len(operands)-1].(type) {
			case Shifted, Extended:
			default:
				return nil, fmt.Errorf("reading spells %q but the operand carries no modifier", tok)
			}
			continue
		case strings.HasPrefix(tok, "LSL #"), strings.HasPrefix(tok, "LSR #"), strings.HasPrefix(tok, "ASR #"), strings.HasPrefix(tok, "ROR #"):
			amount, err := e.evalImmediate(strings.TrimSpace(tok[4:]))
			if err != nil {
				return nil, err
			}
			if len(operands) == 0 {
				return nil, fmt.Errorf("modifier %q without an operand", tok)
			}
			switch prev := operands[len(operands)-1].(type) {
			case Register:
				operands[len(operands)-1] = Shifted{Reg: prev, Kind: strings.ToLower(tok[:3]), Amount: amount}
			case Immediate:
				operands[len(operands)-1] = Immediate{Value: prev.Value, Shift: amount}
			default:
				return nil, fmt.Errorf("modifier %q on %T", tok, prev)
			}
			continue
		}
		op, err := e.aliasOperand(tok)
		if err != nil {
			return nil, err
		}
		operands = append(operands, op)
	}
	if !spelledModifier {
		for _, op := range operands {
			switch op.(type) {
			case Shifted, Extended:
				return nil, fmt.Errorf("reading omits the modifier the operand carries")
			}
		}
	}
	return operands, nil
}

// aliasOperand realizes one token of an equivalence template.
func (e *encoder) aliasOperand(tok string) (Operand, error) {
	if strings.HasPrefix(tok, "#") {
		v, err := e.evalImmediate(tok)
		if err != nil {
			return nil, err
		}
		return Immediate{Value: v}, nil
	}
	if strings.HasPrefix(tok, "[") {
		for sym, op := range e.bindings {
			if strings.HasPrefix(sym, "[") {
				return op, nil
			}
		}
		return nil, fmt.Errorf("memory operand %s unbound", tok)
	}
	if op, ok := e.bindings[tok]; ok {
		return op, nil
	}
	switch tok {
	case "<invcond>", "<cond>":
		other := "<cond>"
		if tok == "<cond>" {
			other = "<invcond>"
		}
		if op, ok := e.bindings[other]; ok {
			c := op.(Condition)
			return Condition{Code: invertCondition(c.Code)}, nil
		}
	case "WZR":
		return Register{Text: "wzr", Class: ClassW, Num: 31}, nil
	case "XZR":
		return Register{Text: "xzr", Class: ClassX, Num: 31}, nil
	case "SP", "WSP":
		return Register{Text: "sp", Class: ClassSP, Num: -1}, nil
	}
	// The same register under another width or role: <Xn> for a bound <Wn>
	// (sxtb), <Xm> for <Xn> when the alias states Rn == Rm (cinc).
	if m := aliasRegRe.FindStringSubmatch(tok); m != nil {
		for sym, op := range e.bindings {
			bm := aliasRegRe.FindStringSubmatch(sym)
			if bm == nil {
				continue
			}
			sameRole := bm[2] == m[2]
			paired := strings.Contains(e.enc.AliasCond, "Rn == Rm") && (m[2] == "m" && bm[2] == "n" || m[2] == "n" && bm[2] == "m")
			if !sameRole && !paired {
				continue
			}
			reg, ok := registerOf(op)
			if !ok {
				continue
			}
			if m[1] == "X" && reg.Class == ClassW {
				return Register{Text: "x" + strconv.Itoa(reg.Num), Class: ClassX, Num: reg.Num}, nil
			}
			if m[1] == "W" && reg.Class == ClassX {
				return Register{Text: "w" + strconv.Itoa(reg.Num), Class: ClassW, Num: reg.Num}, nil
			}
			return op, nil
		}
	}
	return nil, fmt.Errorf("symbol %s unbound", tok)
}

var aliasRegRe = regexp.MustCompile(`^<([WX])([a-z]+\d?)(\|W?SP)?>$`)

func invertCondition(code string) string {
	v := conditionCodesByName[strings.ToLower(code)] ^ 1
	names := []string{"eq", "ne", "hs", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al", "nv"}
	return names[v]
}

// evalImmediate evaluates `#<sym>`, `#(<a>-1)`, `#(-<lsb> MOD 32)`,
// `#(31-<shift>)`, `#0`.
func (e *encoder) evalImmediate(text string) (int64, error) {
	text = strings.TrimSpace(strings.TrimPrefix(text, "#"))
	p := &exprParser{s: text, e: e}
	v, err := p.expr()
	if err != nil {
		return 0, err
	}
	p.skip()
	if p.i != len(p.s) {
		return 0, fmt.Errorf("expression %q: trailing %q", text, p.s[p.i:])
	}
	return v, nil
}

type exprParser struct {
	s string
	i int
	e *encoder
}

func (p *exprParser) skip() {
	for p.i < len(p.s) && p.s[p.i] == ' ' {
		p.i++
	}
}

func (p *exprParser) expr() (int64, error) {
	v, err := p.term()
	if err != nil {
		return 0, err
	}
	for {
		p.skip()
		switch {
		case p.i < len(p.s) && p.s[p.i] == '+':
			p.i++
			w, err := p.term()
			if err != nil {
				return 0, err
			}
			v += w
		case p.i < len(p.s) && p.s[p.i] == '-':
			p.i++
			w, err := p.term()
			if err != nil {
				return 0, err
			}
			v -= w
		case strings.HasPrefix(p.s[p.i:], "MOD"):
			p.i += 3
			w, err := p.term()
			if err != nil {
				return 0, err
			}
			if w == 0 {
				return 0, fmt.Errorf("MOD 0")
			}
			v = ((v % w) + w) % w
		default:
			return v, nil
		}
	}
}

func (p *exprParser) term() (int64, error) {
	p.skip()
	if p.i >= len(p.s) {
		return 0, fmt.Errorf("expression ends early")
	}
	switch c := p.s[p.i]; {
	case c == '(':
		p.i++
		v, err := p.expr()
		if err != nil {
			return 0, err
		}
		p.skip()
		if p.i >= len(p.s) || p.s[p.i] != ')' {
			return 0, fmt.Errorf("missing )")
		}
		p.i++
		return v, nil
	case c == '-':
		p.i++
		v, err := p.term()
		return -v, err
	case c == '<':
		end := strings.IndexByte(p.s[p.i:], '>')
		if end < 0 {
			return 0, fmt.Errorf("unterminated symbol")
		}
		sym := p.s[p.i : p.i+end+1]
		p.i += end + 1
		if v, ok := p.e.values["#"+sym]; ok {
			return v, nil
		}
		if v, ok := p.e.values[sym]; ok {
			return v, nil
		}
		if op, ok := p.e.bindings["#"+sym]; ok {
			if imm, isImm := op.(Immediate); isImm {
				return imm.Value, nil
			}
		}
		return 0, fmt.Errorf("symbol %s has no value", sym)
	case c >= '0' && c <= '9':
		j := p.i
		for j < len(p.s) && (p.s[j] >= '0' && p.s[j] <= '9' || p.s[j] == 'x' || p.s[j] >= 'a' && p.s[j] <= 'f' || p.s[j] >= 'A' && p.s[j] <= 'F') {
			j++
		}
		v, err := strconv.ParseInt(p.s[p.i:j], 0, 64)
		if err != nil {
			return 0, err
		}
		p.i = j
		return v, nil
	}
	return 0, fmt.Errorf("unexpected %q", p.s[p.i:])
}

// ---- mov immediates ------------------------------------------------------------

// encodeMovImmediate chooses movz, movn, or orr with a bitmask for `mov
// reg, #imm`, as Arm's three aliases prescribe (movz when one 16-bit chunk
// is set, movn when one chunk of the complement is set, otherwise a
// logical immediate).
func encodeMovImmediate(reg Register, value int64) (uint32, *Relocation, error) {
	width := 64
	if reg.Class == ClassW {
		width = 32
		if value < 0 {
			value &= 0xffffffff
		}
	}
	uv := uint64(value)
	if width == 32 && uv>>32 != 0 {
		return 0, nil, fmt.Errorf("mov: %#x does not fit 32 bits", uv)
	}
	chunks := width / 16
	nonzero, position := 0, 0
	for i := 0; i < chunks; i++ {
		if (uv>>uint(16*i))&0xffff != 0 {
			nonzero++
			position = i
		}
	}
	if nonzero <= 1 {
		return EncodeInstruction(Instruction{Mnemonic: "movz", Operands: []Operand{reg, Immediate{Value: int64((uv >> uint(16*position)) & 0xffff), Shift: int64(16 * position)}}}, 0, nil)
	}
	inv := ^uv
	if width == 32 {
		inv &= 0xffffffff
	}
	nonzero, position = 0, 0
	for i := 0; i < chunks; i++ {
		if (inv>>uint(16*i))&0xffff != 0 {
			nonzero++
			position = i
		}
	}
	if nonzero <= 1 {
		return EncodeInstruction(Instruction{Mnemonic: "movn", Operands: []Operand{reg, Immediate{Value: int64((inv >> uint(16*position)) & 0xffff), Shift: int64(16 * position)}}}, 0, nil)
	}
	zr := Register{Text: "xzr", Class: ClassX, Num: 31}
	if width == 32 {
		zr = Register{Text: "wzr", Class: ClassW, Num: 31}
	}
	return EncodeInstruction(Instruction{Mnemonic: "orr", Operands: []Operand{reg, zr, Immediate{Value: value}}}, 0, nil)
}

// ---- fields --------------------------------------------------------------------

func (e *encoder) fieldDef(name string) (isaField, bool) {
	base := name
	if i := strings.IndexAny(name, "[<"); i >= 0 {
		base = name[:i]
	}
	for _, f := range e.enc.Fields {
		if f.Name == base {
			return f, true
		}
	}
	return isaField{}, false
}

// fieldBits resolves a field reference, possibly a slice (`op2[2:1]`,
// `cmode[1]`, `CRm<0>`), to its low bit position and width.
func (e *encoder) fieldBits(name string) (low, width int, ok bool) {
	f, found := e.fieldDef(name)
	if !found {
		return 0, 0, false
	}
	low, width = f.Hi-f.Width+1, f.Width
	i := strings.IndexAny(name, "[<")
	if i < 0 {
		return low, width, true
	}
	spec := strings.Trim(name[i:], "[]<>")
	hi, lo := 0, 0
	if j := strings.IndexByte(spec, ':'); j >= 0 {
		hi, _ = strconv.Atoi(spec[:j])
		lo, _ = strconv.Atoi(spec[j+1:])
	} else {
		hi, _ = strconv.Atoi(spec)
		lo = hi
	}
	if lo < 0 || hi < lo || hi >= f.Width {
		return 0, 0, false
	}
	return low + lo, hi - lo + 1, true
}

func (e *encoder) fieldWidth(name string) int {
	_, width, _ := e.fieldBits(name)
	return width
}

func (e *encoder) fieldsWidth(names []string) int {
	total := 0
	for _, n := range names {
		total += e.fieldWidth(n)
	}
	return total
}

// setField writes a whole field (or slice); a second write must agree with
// the first (the same field named by two operands, as in cinc's Rn and Rm).
func (e *encoder) setField(name string, value uint32) error {
	low, width, ok := e.fieldBits(name)
	if !ok {
		return fmt.Errorf("encoding %s has no field %q", e.enc.Name, name)
	}
	if value >= 1<<uint(width) {
		return fmt.Errorf("field %s: %d does not fit %d bits", name, value, width)
	}
	mask := uint32(1<<uint(width)-1) << uint(low)
	if fixed := e.enc.Mask & mask; fixed != 0 {
		// The field overlaps fixed bits of this encoding (an alias's
		// constraint such as Rn == 11111): the value must agree.
		if e.enc.Value&fixed != (value<<uint(low))&fixed {
			return mismatch("field %s is fixed in %s", name, e.enc.Name)
		}
	}
	if prev, written := e.written[name]; written && prev != value {
		return mismatch("field %s written twice (%d then %d)", name, prev, value)
	}
	e.written[name] = value
	e.word = e.word&^mask | value<<uint(low)
	if name == "sf" {
		if value == 1 {
			e.values["width"] = 64
		} else {
			e.values["width"] = 32
		}
	}
	return nil
}

// writeFields distributes a value over several fields, most significant first.
func (e *encoder) writeFields(names []string, value uint64) error {
	total := e.fieldsWidth(names)
	if total == 0 {
		return fmt.Errorf("no fields to write for %v", names)
	}
	if value >= 1<<uint(total) {
		return fmt.Errorf("%d does not fit %d bits (%v)", value, total, names)
	}
	shift := total
	for _, n := range names {
		w := e.fieldWidth(n)
		shift -= w
		part := uint32((value >> uint(shift)) & (1<<uint(w) - 1))
		if err := e.setField(n, part); err != nil {
			return err
		}
	}
	return nil
}
