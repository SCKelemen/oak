// Package wasm implements Oak's experimental, import-free Core Wasm profile.
// Structural checks and execution tests are not a formal refinement proof.
package wasm

import (
	"fmt"
	"sort"
	"strconv"
	"unicode/utf8"

	"github.com/SCKelemen/oak/optir"
	"github.com/SCKelemen/oak/wasm/check"
)

const Profile = "oak.wasm.scalar.v1"

// Export retains Oak types: Wasm's i32 alone cannot distinguish Bool/u32/i32.
type Export struct {
	Name       string       `json:"name"`
	Parameters []optir.Type `json:"parameters"`
	Result     optir.Type   `json:"result"`
}

type Module struct {
	Bytes   []byte   `json:"bytes"`
	Exports []Export `json:"exports"`
	Profile string   `json:"profile"`
	// Always false until source-to-decoded-bytes refinement is implemented.
	TranslationVerified bool          `json:"translationVerified"`
	ByteValidation      *check.Report `json:"byteValidation,omitempty"`
}

type function struct {
	cfg        optir.CFG
	entry      optir.Block
	index      uint32
	locals     map[optir.ValueID]uint32
	types      map[optir.ValueID]optir.Type
	localTypes []byte
	blocks     map[optir.BlockID]int
}

func valueType(t optir.Type) (byte, error) {
	switch t {
	case "u32", "i32", "Bool", "()":
		return 0x7f, nil
	case "u64", "i64":
		return 0x7e, nil
	default:
		return 0, fmt.Errorf("wasm: unsupported type %s in %s", t, Profile)
	}
}

// Emit is all-or-nothing. It uses the checked raw CFG, not an optimized
// candidate whose equivalence has not been established for this target.
func Emit(cfgs []optir.CFG) (Module, error) {
	out, err := EncodeCandidate(cfgs)
	if err != nil {
		return Module{}, err
	}
	report, err := out.ValidateBytes()
	if err != nil {
		return Module{}, fmt.Errorf("wasm: emitted bytes refused: %w", err)
	}
	out.ByteValidation = &report
	return out, nil
}

// EncodeCandidate is untrusted materialization for a compiler artifact graph.
// It enforces the input subset but does NOT independently admit output bytes.
// Use Emit for the safe combined API, or gate this result with ValidateBytes.
// Its result has no ByteValidation report or translation-verification authority.
func EncodeCandidate(cfgs []optir.CFG) (Module, error) {
	if len(cfgs) == 0 || len(cfgs) > 128 {
		return Module{}, fmt.Errorf("wasm: need 1..128 functions")
	}
	ordered := append([]optir.CFG(nil), cfgs...)
	sort.Slice(ordered, func(i, j int) bool { return ordered[i].Name < ordered[j].Name })
	functions := make([]*function, 0, len(ordered))
	byName := map[string]*function{}
	total := 0
	for _, cfg := range ordered {
		if cfg.Name == "" || len(cfg.Name) > 256 || !utf8.ValidString(cfg.Name) || byName[cfg.Name] != nil {
			return Module{}, fmt.Errorf("wasm: invalid or duplicate function name %q", cfg.Name)
		}
		if len(cfg.Blocks) == 0 || len(cfg.Blocks) > 128 || len(cfg.Results) != 1 {
			return Module{}, fmt.Errorf("wasm: %s needs 1..128 blocks and one Oak result", cfg.Name)
		}
		f := &function{cfg: cfg, index: uint32(len(functions)), locals: map[optir.ValueID]uint32{}, types: map[optir.ValueID]optir.Type{}, blocks: map[optir.BlockID]int{}}
		for i, b := range cfg.Blocks {
			if b.ID == cfg.Entry {
				f.entry = b
			}
			f.blocks[b.ID] = i
			total += len(b.Operations) + len(b.Parameters)
			for _, op := range b.Operations {
				if len(op.Results) != 1 || len(op.Operands) > 64 || len(op.Attributes) > 1 {
					return Module{}, fmt.Errorf("wasm: unsupported operation shape %s", op.Code)
				}
				for _, a := range op.Attributes {
					if len(a.Value) > 256 {
						return Module{}, fmt.Errorf("wasm: oversized operation attribute")
					}
				}
			}
		}
		if total > 16384 || len(f.entry.Parameters) > 64 {
			return Module{}, fmt.Errorf("wasm: scalar profile size limit exceeded")
		}
		if _, err := valueType(cfg.Results[0]); err != nil {
			return Module{}, err
		}
		if _, err := optir.AnalyzeSCCP(cfg); err != nil {
			return Module{}, fmt.Errorf("wasm: %s: %w", cfg.Name, err)
		}
		define := func(v optir.Value) error {
			if _, exists := f.locals[v.ID]; exists {
				return nil
			}
			t, err := valueType(v.Type)
			if err != nil {
				return err
			}
			f.locals[v.ID] = uint32(len(f.localTypes))
			f.types[v.ID] = v.Type
			f.localTypes = append(f.localTypes, t)
			return nil
		}
		for _, p := range f.entry.Parameters {
			if p.Type == "()" {
				return Module{}, fmt.Errorf("wasm: Unit parameters are not supported")
			}
			if err := define(p); err != nil {
				return Module{}, err
			}
		}
		for _, b := range cfg.Blocks {
			for _, p := range b.Parameters {
				if err := define(p); err != nil {
					return Module{}, err
				}
			}
			for _, op := range b.Operations {
				if err := define(op.Results[0]); err != nil {
					return Module{}, err
				}
			}
		}
		functions = append(functions, f)
		byName[cfg.Name] = f
	}
	var types, decls, exports, code binary
	types.u(uint64(len(functions)))
	decls.u(uint64(len(functions)))
	exports.u(uint64(len(functions)))
	code.u(uint64(len(functions)))
	out := Module{Profile: Profile}
	for _, f := range functions {
		types.op(0x60)
		types.u(uint64(len(f.entry.Parameters)))
		e := Export{Name: f.cfg.Name, Result: f.cfg.Results[0], Parameters: []optir.Type{}}
		for _, p := range f.entry.Parameters {
			t, _ := valueType(p.Type)
			types.op(t)
			e.Parameters = append(e.Parameters, p.Type)
		}
		if f.cfg.Results[0] == "()" {
			types.u(0)
		} else {
			types.u(1)
			t, _ := valueType(f.cfg.Results[0])
			types.op(t)
		}
		decls.u(uint64(f.index))
		exports.name(f.cfg.Name)
		exports.op(0)
		exports.u(uint64(f.index))
		body, err := f.body(byName)
		if err != nil {
			return Module{}, fmt.Errorf("wasm: %s: %w", f.cfg.Name, err)
		}
		code.u(uint64(len(body)))
		code = append(code, body...)
		out.Exports = append(out.Exports, e)
	}
	b := binary{0, 0x61, 0x73, 0x6d, 1, 0, 0, 0}
	b.section(1, types)
	b.section(3, decls)
	b.section(7, exports)
	b.section(10, code)
	out.Bytes = []byte(b)
	return out, nil
}

// ValidateBytes rechecks actual bytes and the carrier-level export manifest.
// Never trust a stored ByteValidation report after mutation. Carrier matching
// cannot distinguish Bool/u32/i32, or prove that a named function implements Oak.
func (m Module) ValidateBytes() (check.Report, error) {
	if m.Profile != Profile || m.TranslationVerified {
		return check.Report{}, fmt.Errorf("wasm: unsupported profile or translation-verification claim")
	}
	report, err := check.Validate(m.Bytes)
	if err != nil {
		return check.Report{}, err
	}
	if report.Profile != m.Profile || len(report.Exports) != len(m.Exports) {
		return check.Report{}, fmt.Errorf("wasm: byte export manifest disagrees")
	}
	carrier := func(t optir.Type) check.ValueType {
		switch t {
		case "Bool", "u32", "i32":
			return check.I32
		case "u64", "i64":
			return check.I64
		default:
			return ""
		}
	}
	for i, e := range m.Exports {
		actual := report.Exports[i]
		if e.Name != actual.Name || len(e.Parameters) != len(actual.Parameters) {
			return check.Report{}, fmt.Errorf("wasm: export name/arity mismatch")
		}
		for j, p := range e.Parameters {
			if carrier(p) != actual.Parameters[j] {
				return check.Report{}, fmt.Errorf("wasm: export parameter carrier mismatch")
			}
		}
		if e.Result == "()" {
			if len(actual.Results) != 0 {
				return check.Report{}, fmt.Errorf("wasm: Unit export has a byte result")
			}
		} else if len(actual.Results) != 1 || carrier(e.Result) != actual.Results[0] {
			return check.Report{}, fmt.Errorf("wasm: export result carrier mismatch")
		}
	}
	return report, nil
}

func (f *function) body(functions map[string]*function) (binary, error) {
	var b binary
	// A single returning block needs no dispatcher or program-counter local.
	// Do not select this path for a single-block back edge, even if an analysis
	// claims it is unreachable: this emitter consumes the checked raw CFG.
	direct := len(f.cfg.Blocks) == 1 && f.entry.Terminator.Kind == optir.TerminatorReturn
	loop, structuredLoop := f.matchLoop()
	diamond, structuredDiamond := f.matchDiamond()
	dispatch := !direct && !structuredLoop && !structuredDiamond
	extra := 0
	if dispatch {
		extra = 1
	}
	// One group per SSA local, plus the optional i32 program counter. Entry
	// parameters already occupy local slots; local indices are never reordered.
	n := len(f.entry.Parameters)
	b.u(uint64(len(f.localTypes) - n + extra))
	for _, t := range f.localTypes[n:] {
		b.u(1)
		b.op(t)
	}
	if dispatch {
		b.u(1)
		b.op(0x7f)
	}
	pc := uint32(len(f.localTypes))
	for _, p := range f.entry.Parameters {
		if p.Type == "Bool" {
			f.get(&b, p.ID)
			b.i32(1)
			b.op(0x4b, 0x04, 0x40, 0x00, 0x0b)
		}
	}
	if direct {
		if err := f.operations(&b, f.entry, functions); err != nil {
			return nil, err
		}
		f.returnValue(&b, f.entry.Terminator)
		b.op(0x0b) // function end returns the result already on the operand stack
		return b, nil
	}
	if structuredLoop {
		if err := f.loopBody(&b, loop, functions); err != nil {
			return nil, err
		}
		return b, nil
	}
	if structuredDiamond {
		if err := f.diamondBody(&b, diamond, functions); err != nil {
			return nil, err
		}
		return b, nil
	}
	b.i32(int32(f.blocks[f.cfg.Entry]))
	b.local(0x21, pc)
	b.op(0x03, 0x40) // loop, empty block type
	for i, block := range f.cfg.Blocks {
		b.local(0x20, pc)
		b.i32(int32(i))
		b.op(0x46, 0x04, 0x40)
		if err := f.operations(&b, block, functions); err != nil {
			return nil, err
		}
		switch t := block.Terminator; t.Kind {
		case optir.TerminatorReturn:
			f.returnValue(&b, t)
			b.op(0x0f)
		case optir.TerminatorBranch:
			f.edge(&b, t.True, pc, 1)
		case optir.TerminatorCondBranch:
			f.get(&b, t.Condition)
			b.op(0x04, 0x40)
			f.edge(&b, t.True, pc, 2)
			b.op(0x05)
			f.edge(&b, t.False, pc, 2)
			b.op(0x0b)
		default:
			return nil, fmt.Errorf("unsupported terminator %s", t.Kind)
		}
		b.op(0x0b)
	}
	b.op(0x00, 0x0b, 0x00, 0x0b) // invalid PC traps; unreachable after loop; function end
	return b, nil
}

// Structural recognizers share bounds-checked lookup, not reachability guesses.
func (f *function) lookupBlock(id optir.BlockID) (optir.Block, bool) {
	i, ok := f.blocks[id]
	if !ok || i < 0 || i >= len(f.cfg.Blocks) {
		return optir.Block{}, false
	}
	return f.cfg.Blocks[i], true
}

func (f *function) operations(b *binary, block optir.Block, functions map[string]*function) error {
	for _, op := range block.Operations {
		if err := f.operation(b, op, functions); err != nil {
			return err
		}
	}
	return nil
}

func (f *function) returnValue(b *binary, t optir.Terminator) {
	if f.cfg.Results[0] != "()" {
		f.get(b, t.Values[0])
	}
}

func (f *function) get(b *binary, id optir.ValueID) { b.local(0x20, f.locals[id]) }
func (f *function) edge(b *binary, e optir.Edge, pc, depth uint32) {
	f.edgeValues(b, e)
	b.i32(int32(f.blocks[e.Target]))
	b.local(0x21, pc)
	b.op(0x0c)
	b.u(uint64(depth))
}

func (f *function) edgeValues(b *binary, e optir.Edge) {
	// Parallel copies: snapshot ALL incoming values before writing any phi.
	for _, a := range e.Arguments {
		f.get(b, a)
	}
	params := f.cfg.Blocks[f.blocks[e.Target]].Parameters
	for i := len(params) - 1; i >= 0; i-- {
		b.local(0x21, f.locals[params[i].ID])
	}
}

func (f *function) operation(b *binary, op optir.Operation, functions map[string]*function) error {
	if op.MemoryAccessID != "" {
		return fmt.Errorf("memory is outside %s", Profile)
	}
	switch op.Code {
	case optir.OpIntDiv, optir.OpIntRem:
		if len(op.Effects) != 1 || op.Effects[0] != optir.EffectTrap {
			return fmt.Errorf("%s requires exactly the trap effect in %s", op.Code, Profile)
		}
	case optir.OpCall:
		// Its actual effects come from the checked in-module callee.
	default:
		if len(op.Effects) != 0 {
			return fmt.Errorf("effects of %s are outside %s", op.Code, Profile)
		}
	}
	r := op.Results[0]
	wide := r.Type == "u64" || r.Type == "i64"
	if len(op.Attributes) != 0 && op.Code != optir.OpConstInt && op.Code != optir.OpConstBool && op.Code != optir.OpCall {
		return fmt.Errorf("unexpected attributes on %s", op.Code)
	}
	switch op.Code {
	case optir.OpConstUnit:
		b.i32(0)
	case optir.OpConstBool:
		if op.Attributes[0].Value == "true" {
			b.i32(1)
		} else {
			b.i32(0)
		}
	case optir.OpConstInt:
		v := op.Attributes[0].Value
		var bits uint64
		var err error
		if r.Type == "u32" || r.Type == "u64" {
			bits, err = strconv.ParseUint(v, 10, 64)
		} else {
			var signed int64
			signed, err = strconv.ParseInt(v, 10, 64)
			bits = uint64(signed)
		}
		if err != nil {
			return err
		}
		if wide {
			b.op(0x42)
			b.s(int64(bits))
		} else {
			b.i32(int32(bits))
		}
	case optir.OpCopy:
		f.get(b, op.Operands[0])
	case optir.OpBoolNot:
		f.get(b, op.Operands[0])
		b.op(0x45)
	case optir.OpIntNeg:
		if wide {
			b.op(0x42)
			b.s(0)
		} else {
			b.i32(0)
		}
		f.get(b, op.Operands[0])
		if wide {
			b.op(0x7d)
		} else {
			b.op(0x6b)
		}
	case optir.OpIntDiv, optir.OpIntRem:
		f.divrem(b, op)
	case optir.OpCall:
		callee := functions[op.Attributes[0].Value]
		if callee == nil || len(callee.entry.Parameters) != len(op.Operands) || callee.cfg.Results[0] != r.Type {
			return fmt.Errorf("unknown or mismatched callee %q", op.Attributes[0].Value)
		}
		for i, id := range op.Operands {
			if f.types[id] != callee.entry.Parameters[i].Type {
				return fmt.Errorf("callee argument type mismatch")
			}
			f.get(b, id)
		}
		b.op(0x10)
		b.u(uint64(callee.index))
		if r.Type == "()" {
			b.i32(0)
		}
	default:
		if len(op.Operands) != 2 {
			return fmt.Errorf("unsupported operation %s", op.Code)
		}
		t := f.types[op.Operands[0]]
		opcode, ok := binaryOpcode(op.Code, t)
		if !ok {
			return fmt.Errorf("unsupported operation %s in %s", op.Code, Profile)
		}
		f.get(b, op.Operands[0])
		f.get(b, op.Operands[1])
		b.op(opcode)
	}
	b.local(0x21, f.locals[r.ID])
	return nil
}

// divrem preserves Oak's zero-divisor trap and signed overflow behavior. Wasm
// div_s traps on MIN/-1, while Oak wraps. For every dividend, division by -1
// is wrapping negation, so that arm never executes div_s. rem_s already returns
// zero for MIN%-1. Operands are SSA locals: no calls are evaluated again here.
func (f *function) divrem(b *binary, op optir.Operation) {
	t := op.Results[0].Type
	wide := t == "i64" || t == "u64"
	signed := t == "i32" || t == "i64"
	opcode := byte(0x6d) // i32.div_s
	if op.Code == optir.OpIntRem {
		opcode += 2
	}
	if !signed {
		opcode++
	}
	if wide {
		opcode += 0x12
	}
	guard := signed && op.Code == optir.OpIntDiv
	if guard {
		f.get(b, op.Operands[1])
		if wide {
			b.op(0x42)
			b.s(-1)
			b.op(0x51, 0x04, 0x7e) // i64.eq; if (result i64)
			b.op(0x42)
			b.s(0)
		} else {
			b.i32(-1)
			b.op(0x46, 0x04, 0x7f) // i32.eq; if (result i32)
			b.i32(0)
		}
		f.get(b, op.Operands[0])
		if wide {
			b.op(0x7d)
		} else {
			b.op(0x6b)
		}
		b.op(0x05) // else
	}
	f.get(b, op.Operands[0])
	f.get(b, op.Operands[1])
	b.op(opcode)
	if guard {
		b.op(0x0b)
	}
}

func binaryOpcode(code string, t optir.Type) (byte, bool) {
	wide := t == "i64" || t == "u64"
	signed := t == "i32" || t == "i64"
	var opcode byte
	switch code {
	case optir.OpIntAdd:
		opcode = 0x6a
	case optir.OpIntSub:
		opcode = 0x6b
	case optir.OpIntMul:
		opcode = 0x6c
	case optir.OpIntAnd:
		opcode = 0x71
	case optir.OpIntOr:
		opcode = 0x72
	case optir.OpIntXor:
		opcode = 0x73
	case optir.OpEqual:
		if wide {
			return 0x51, true
		}
		return 0x46, true
	case optir.OpNotEqual:
		if wide {
			return 0x52, true
		}
		return 0x47, true
	case optir.OpLess:
		opcode = 0x48
	case optir.OpGreater:
		opcode = 0x4a
	case optir.OpLessEqual:
		opcode = 0x4c
	case optir.OpGreaterEqual:
		opcode = 0x4e
	default:
		return 0, false
	}
	if opcode >= 0x6a {
		if wide {
			opcode += 0x12
		}
		return opcode, true
	}
	if wide {
		// i64 orders the comparison pairs less/greater/less-equal/greater-equal.
		opcode += 0x0b
	}
	if !signed {
		opcode++
	}
	return opcode, true
}

type binary []byte

func (b *binary) op(v ...byte) { *b = append(*b, v...) }
func (b *binary) u(v uint64) {
	for {
		x := byte(v & 127)
		v >>= 7
		if v != 0 {
			x |= 128
		}
		b.op(x)
		if v == 0 {
			return
		}
	}
}
func (b *binary) s(v int64) {
	for {
		x := byte(v & 127)
		v >>= 7
		end := (v == 0 && x&64 == 0) || (v == -1 && x&64 != 0)
		if !end {
			x |= 128
		}
		b.op(x)
		if end {
			return
		}
	}
}
func (b *binary) i32(v int32)                 { b.op(0x41); b.s(int64(v)) }
func (b *binary) local(op byte, index uint32) { b.op(op); b.u(uint64(index)) }
func (b *binary) name(s string)               { b.u(uint64(len(s))); *b = append(*b, []byte(s)...) }
func (b *binary) section(id byte, payload binary) {
	b.op(id)
	b.u(uint64(len(payload)))
	*b = append(*b, payload...)
}
