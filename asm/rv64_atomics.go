package asm

import (
	"fmt"
	"strings"
)

// The A extension in the rv64 unit language (docs/spec/94-assembler.md §9):
// `lr.w`/`lr.d` and `sc.w`/`sc.d` with their ordering suffixes (`.aq`,
// `.rl`, `.aqrl`), and the `amo*.w`/`amo*.d` read-modify-writes, through a
// span element as the plain loads and stores are — the checker holds them
// to the same bounds, the verifier decides them under its sequential model
// (docs/spec/65-machine-memory.md section 7a, asm/atomics.go for the
// AArch64 spellings): `lr` reads the element, `sc` stores and reports
// success (the exclusive store succeeds, so the retry branch is decided),
// an `amo` reads and writes. The ordering bits are the checker's and the
// memory-model chapter's concern (docs/spec/69-riscv-memory-refinement.md);
// the values are these terms. The mnemonic keeps its full spelling in the
// unit, so the C emitter reproduces it; the table entry is the base's.

// rv64AtomicSpelling splits an atomic mnemonic into the table's base name
// and its ordering bits: `sc.w.rl` is `sc.w` with rl.
func rv64AtomicSpelling(mnemonic string) (base string, aq, rl bool, ok bool) {
	base = mnemonic
	switch {
	case strings.HasSuffix(base, ".aqrl"):
		base, aq, rl = strings.TrimSuffix(base, ".aqrl"), true, true
	case strings.HasSuffix(base, ".aq"):
		base, aq = strings.TrimSuffix(base, ".aq"), true
	case strings.HasSuffix(base, ".rl"):
		base, rl = strings.TrimSuffix(base, ".rl"), true
	}
	if !strings.HasPrefix(base, "lr.") && !strings.HasPrefix(base, "sc.") && !strings.HasPrefix(base, "amo") {
		return "", false, false, false
	}
	if _, known := rv64Table[base]; !known {
		return "", false, false, false
	}
	return base, aq, rl, true
}

// rv64Atomic classifies an atomic mnemonic: kind "lr", "sc", or the amo
// operation ("swap", "add", "xor", "and", "or", "min", "max", "minu",
// "maxu"), and the access width in bytes (4 for .w, 8 for .d).
func rv64Atomic(mnemonic string) (kind string, width int, ok bool) {
	base, _, _, isAtomic := rv64AtomicSpelling(mnemonic)
	if !isAtomic {
		return "", 0, false
	}
	dot := strings.LastIndex(base, ".")
	switch base[dot+1:] {
	case "w":
		width = 4
	case "d":
		width = 8
	default:
		return "", 0, false
	}
	switch {
	case strings.HasPrefix(base, "lr."):
		return "lr", width, true
	case strings.HasPrefix(base, "sc."):
		return "sc", width, true
	}
	return strings.TrimPrefix(base[:dot], "amo"), width, true
}

// rv64AtomicShape checks an atomic's operands: `lr rd, 0(rs1)`,
// `sc rd, rs2, 0(rs1)`, `amo* rd, rs2, 0(rs1)` — no offset.
func rv64AtomicShape(instr Instruction) error {
	kind, _, _ := rv64Atomic(instr.Mnemonic)
	want := 3
	if kind == "lr" {
		want = 2
	}
	ops := instr.Operands
	if len(ops) != want {
		return fmt.Errorf("%s takes %d operands, got %d", instr.Mnemonic, want, len(ops))
	}
	for i := 0; i < want-1; i++ {
		if _, isReg := ops[i].(Register); !isReg {
			return fmt.Errorf("%s: operand %d must be a register", instr.Mnemonic, i+1)
		}
	}
	mem, isMem := ops[want-1].(Memory)
	if !isMem {
		return fmt.Errorf("%s: operand %d must be a memory operand 0(base)", instr.Mnemonic, want)
	}
	if mem.Offset != 0 {
		return fmt.Errorf("%s: atomics take a zero offset, got %d", instr.Mnemonic, mem.Offset)
	}
	return nil
}

// atomicAccess checks an atomic through a span element: the bounds are
// the plain access's (spanAccess), a store needs a writable span, `lr`
// and the amos write their destination, `sc` its status register.
func (c *rvChecker) atomicAccess(kind string, width int, ops []Operand, line int) {
	reg := func(i int) Register { return ops[i].(Register) }
	mem := ops[len(ops)-1].(Memory)
	if mem.Base.Class == ClassSP {
		c.errorf(line, "atomics address a span base, not the frame")
		return
	}
	c.read(mem.Base, line)
	if kind != "lr" {
		c.read(reg(1), line)
	}
	c.spanAccess(mem, int64(width), kind != "lr", line)
	c.write(reg(0), line)
}

// atomicRV64 executes an atomic through a span element under the
// sequential model (see the file comment).
func (x *pathExecutor) atomicRV64(kind string, width int, ops []Operand, state *symbolicState) (string, bool) {
	if len(x.loopStack) > 0 {
		return "an atomic in a data-dependent loop body", false
	}
	reg := func(i int) Register { return ops[i].(Register) }
	mem := ops[len(ops)-1].(Memory)
	if mem.Base.Class == ClassSP || mem.Offset != 0 {
		return "an atomic whose address is not a span element", false
	}
	span, index, reason, ok := x.rv64SpanAddress(mem, state)
	if !ok {
		return strings.Replace(reason, "a load", "an atomic", 1), false
	}
	if int64(width) != x.spans[span] {
		return fmt.Sprintf("a %d-byte atomic over %d-byte elements", width, x.spans[span]), false
	}
	w := width * 8
	old := x.elementIn(state, span, index, w)
	// The register value of a loaded word: lr.w and the .w amos sign-extend
	// (the W forms' convention), the .d forms fill the register.
	widened := zeroExtend(old, 64)
	if width == 4 {
		widened = extendTerm(widened, 32, 64, true)
	}
	switch kind {
	case "lr":
		state.write(reg(0), widened)
		return "", true
	case "sc":
		value, okValue := state.read(reg(1))
		if !okValue {
			return "unbound register read", false
		}
		state.writes = appendWrite(state.writes, span, index, truncate(value, w), nil)
		state.write(reg(0), constTerm(0, 64)) // the store succeeds
		return "", true
	}
	source, okSource := state.read(reg(1))
	if !okSource {
		return "unbound register read", false
	}
	source = truncate(source, w)
	var value *term
	switch kind {
	case "swap":
		value = source
	case "add":
		value = binaryTerm("add", old, source)
	case "xor":
		value = binaryTerm("xor", old, source)
	case "and":
		value = binaryTerm("and", old, source)
	case "or":
		value = binaryTerm("or", old, source)
	default:
		return "the atomic amo" + kind + " (a minimum or maximum, not modeled)", false
	}
	state.writes = appendWrite(state.writes, span, index, truncate(value, w), nil)
	state.write(reg(0), widened)
	return "", true
}
