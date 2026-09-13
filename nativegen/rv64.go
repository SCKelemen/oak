package nativegen

// The RV64 lane of the native backend (docs/spec/94-assembler.md §9): the
// AArch64 lowering's discipline restated for the LP64 psABI and an ISA
// without flags. A type-checked Oak function of the fixed-width integer
// subset becomes an asm.Function of the rv64 lane — the object an
// `.rv64.oakasm` unit yields — so the RV64 seam checker holds the
// compiler's own output to its bindings, clobbers, frame, and callee-saved
// disciplines, the RV64 verifier proves it equal to the Oak body where its
// term language reaches, and the RV64 encoder and the ELF writer realize
// it in the companion object. The C backend stays the portable realization
// under the lane's negated guard, and the differential oracle.
//
// First increment — the fixed-width integer subset: parameters, locals,
// and results of u8/u16/u32/u64/i8/i16/i32/i64/Bool (or a unit result);
// literals; wrapping `+ - * & | ^`; `/` and `%` with a zero divisor
// trapping (`ebreak`) and `MIN / -1`, `MIN % -1` as the ISA's total
// division gives them (the C helpers' values); shifts whose count at or
// beyond the width traps (constant counts fold the check away);
// comparisons as `slt`/`sltu` (and `sub` then `sltiu`/`sltu` for equality)
// at the operands' signedness; short-circuit `&&`/`||`; `!`, `-`, `^`; the
// widening constructors and the `trunc`/`bits` conversions; the Bool
// conditional in value and statement position; typed locals and
// assignment; `while`/`break`; `assert` (a trap); calls to program
// functions with scalar signatures through `call`; and a tail self-call as
// a loop. Spans, arrays, records, unions, and floating point are left to
// the C backend with the reason — the later increments of the AArch64
// lane, to be ported in the same order.
//
// Every value is a 64-bit register in the psABI's canonical form, which is
// also what the W-form instructions produce: a 32-bit value sign-extended
// from bit 31 whatever its signedness (so `addw`/`subw`/`mulw`/`sllw`/
// `srlw`/`divw`/`divuw`/`remw`/`remuw` keep it canonical, `and`/`or`/`xor`
// of two canonical values are canonical, and `sltu` orders two canonical
// u32 values as the unsigned 32-bit values order — sign extension is
// monotone on each half of the range and keeps the halves apart), an 8-
// or 16-bit unsigned value zero-extended, a signed one sign-extended, Bool
// as 0 or 1. A narrow parameter arrives canonical: the psABI widens an
// integer scalar by its own sign to 32 bits and sign-extends to XLEN, which
// is what the verifier's binding models (asm/rv64_verify.go) and what the C
// compiler relies on for its own callers.
//
// Registers: expressions evaluate into t0–t6 as a small operand stack,
// spilled to their own frame slots around calls; variables live in the
// callee-saved s1–s11 in declaration order (saved in the prologue,
// restored before `ret`, as the checker's obligation states), with frame
// slots past eleven; parameters bind at a0–a7 and the result leaves in a0;
// `ra` is saved at the frame's base when the body calls. The frame moves
// once at entry (`addi sp, sp, -N`, N a multiple of 16 within addi's
// immediate) and once before `ret`.

import (
	"math"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// rvScratch is the operand stack: t0–t6 (x5–x7, x28–x31), caller-saved.
var rvScratch = []int{5, 6, 7, 28, 29, 30, 31}

// rvCallee are the variable homes: s1–s11 (x9, x18–x27), callee-saved. s0
// is left to the frame-pointer convention.
var rvCallee = []int{9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27}

const (
	rvZero = 0  // x0
	rvRA   = 1  // x1, the return address
	rvArg0 = 10 // a0 (x10); a0–a7 are x10–x17
)

// rvMaxFrame bounds the frame: `addi sp, sp, -N` carries a 12-bit signed
// immediate, and N is a multiple of 16.
const rvMaxFrame = 2032

var rvNames = map[int]string{
	0: "zero", 1: "ra", 5: "t0", 6: "t1", 7: "t2", 8: "s0", 9: "s1",
	10: "a0", 11: "a1", 12: "a2", 13: "a3", 14: "a4", 15: "a5", 16: "a6", 17: "a7",
	18: "s2", 19: "s3", 20: "s4", 21: "s5", 22: "s6", 23: "s7", 24: "s8", 25: "s9", 26: "s10", 27: "s11",
	28: "t3", 29: "t4", 30: "t5", 31: "t6",
}

func rvReg(n int) asm.Register {
	if n >= vecBase {
		return rvFReg(n - vecBase)
	}
	return asm.Register{Text: rvNames[n], Class: asm.ClassRV64X, Num: n, Lane: -1}
}

// The floating-point file (F and D under LP64D): ft0–ft11 are the scratch
// registers (f0–f7, f28–f31, caller-saved), fs0–fs11 the variable homes
// (f8, f9, f18–f27, callee-saved: saved with fsd and restored with fld),
// fa0–fa7 (f10–f17) the argument registers, fa0 the result. In the
// generator's numbering a float register is vecBase + its number.
var rvFScratch = []int{0, 1, 2, 3, 4, 5, 6, 7, 28, 29, 30, 31}
var rvFCallee = []int{8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27}

const rvFArg0 = 10 // fa0

var rvFNames = map[int]string{
	0: "ft0", 1: "ft1", 2: "ft2", 3: "ft3", 4: "ft4", 5: "ft5", 6: "ft6", 7: "ft7",
	8: "fs0", 9: "fs1", 10: "fa0", 11: "fa1", 12: "fa2", 13: "fa3", 14: "fa4", 15: "fa5", 16: "fa6", 17: "fa7",
	18: "fs2", 19: "fs3", 20: "fs4", 21: "fs5", 22: "fs6", 23: "fs7", 24: "fs8", 25: "fs9", 26: "fs10", 27: "fs11",
	28: "ft8", 29: "ft9", 30: "ft10", 31: "ft11",
}

func rvFReg(n int) asm.Register {
	return asm.Register{Text: rvFNames[n], Class: asm.ClassRV64F, Num: n, Lane: -1}
}

// fsuffix is the precision suffix of a floating-point mnemonic.
func fsuffix(s scalar) string {
	if s.wide() {
		return ".d"
	}
	return ".s"
}

func rvSP() asm.Register { return asm.Register{Text: "sp", Class: asm.ClassSP, Num: -1, Lane: -1} }

func rvMem(offset int64) asm.Memory {
	return asm.Memory{Base: rvSP(), Offset: offset, Mode: asm.MemOffset}
}

// rvGenerator lowers one function on the rv64 lane. It embeds the AArch64
// generator for the pieces that are not about the machine — type
// inference over the subset (typeOf, operandType), the scratch pool
// bookkeeping (alloc, release), scopes, and labels — and shadows every
// method that emits an instruction.
type rvGenerator struct {
	generator
	regIndex  int  // integer argument registers the parameters occupy (the hidden result pointer included)
	fregIndex int  // floating-point argument registers the parameters occupy
	softFloat bool // the target has no F/D calling convention
	// twoChunk names the callees whose record result comes back in a0 and
	// a1 (asm.Function.TwoChunkResults: the checker's latitude for a1).
	twoChunk map[string]bool
}

// compileRV64 lowers one Oak function on the rv64 lane; see Compile for
// the arguments.
func compileRV64(fn *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, records map[string]*ast.RecordLiteral, adts map[string]*ast.ADTType, constants map[string]asm.Constant, tc *typechecker.TypeChecker, softFloat bool, tables map[string]GlobalArray, globals map[string]asm.Global) (*asm.Function, error) {
	if fn.Body == nil || fn.ExternSymbol != "" || fn.Receiver != nil || len(fn.TypeParams) > 0 || fn.AsmBacked {
		return nil, unsupported("not an ordinary function body")
	}
	if len(fn.Parameters) > 8 {
		return nil, unsupported("more than eight parameters")
	}
	g := &rvGenerator{generator: generator{fn: fn, tc: tc, functions: functions, slots: map[string]int64{}, types: map[string]scalar{}, spans: map[string]span{}, arrays: map[string]*arrayLocal{}, recordDecls: records, adtDecls: adts, layouts: map[string]*recordLayout{}, records: map[string]*recordLocal{}, recordParams: map[string]*recordParam{}, regs: map[string]int{}, spill: map[int]int64{}, defined: map[int]bool{}, constants: constants, globals: globals, usedGlobals: map[string]asm.Global{}, tables: tables, line: fn.Token.Line}, softFloat: softFloat, twoChunk: map[string]bool{}}
	g.rvLane = true
	usesFloat := mentionsFloat(fn) || g.recordsMentionFloat(fn)
	if usesFloat && softFloat {
		return nil, unsupported("floating point on a soft-float target (freestanding/riscv64 carries no F/D calling convention; build for linux/riscv64)")
	}
	for i := len(rvScratch) - 1; i >= 0; i-- {
		g.free = append(g.free, rvScratch[i])
	}
	for i := len(rvFScratch) - 1; i >= 0; i-- {
		g.freeF = append(g.freeF, vecBase+rvFScratch[i])
	}
	if usesFloat {
		g.saveAreaV = 8 * int64(len(rvFCallee))
	}
	g.hasCalls = mentionsCall(fn.Body)
	// A parked span pair survives a call, and a result: the result leaves
	// in a0 (and a1), where a span parameter's pair is bound, and the
	// checker's span facts flow in text order.
	parkSpans := g.hasCalls || returnsValue(fn)
	nextReg, nextFReg := 0, 0
	if fn.ReturnType != nil && fn.ReturnType.String() != "()" {
		if name, isRecord := g.recordTypeName(fn.ReturnType); isRecord {
			// A record result under the psABI: up to 16 bytes back in a0 (and
			// a1); larger written into the caller's area, whose address
			// arrives as a hidden first argument in a0 — parked in a
			// callee-saved register, since a call clobbers a0.
			layout, err := g.layoutOf(name)
			if err != nil {
				return nil, err
			}
			if layout.hasFloat {
				return nil, unsupported("result of type %s carries floating-point fields (the hardware floating-point calling convention)", name)
			}
			g.resultRecord = layout
			g.resultIndirect = layout.size > 16
			if g.resultIndirect {
				g.resultAreaReg = rvCallee[g.usedCallee]
				g.usedCallee++
				nextReg = 1
			}
		} else {
			s, ok := scalarOf(fn.ReturnType)
			if !ok {
				return nil, unsupported("result of type %s", fn.ReturnType.String())
			}
			g.result = &s
		}
	}
	// Parameters take the LP64 integer registers in order: a scalar one, a
	// span or view two (base, then the raw length), a record of up to 16
	// bytes one chunk per 8 bytes and a larger one its address; a float
	// takes fa0–fa7 by its own count (LP64D).
	for _, p := range fn.Parameters {
		if p.Variadic {
			return nil, unsupported("variadic parameter %s", p.Name.Value)
		}
		if name, isRecord := g.recordTypeName(p.Type); isRecord {
			layout, err := g.layoutOf(name)
			if err != nil {
				return nil, err
			}
			if layout.hasFloat {
				return nil, unsupported("parameter %s: %s carries floating-point fields (the hardware floating-point calling convention)", p.Name.Value, name)
			}
			regs, indirect := 1, layout.size > 16
			if !indirect {
				regs = layout.chunks()
			}
			g.recordParams[p.Name.Value] = &recordParam{layout: layout, reg: rvArg0 + nextReg, regs: regs, indirect: indirect}
			nextReg += regs
			continue
		}
		if sc, ok := scalarOf(p.Type); ok {
			if sc.isFloat {
				nextFReg++
			} else {
				nextReg++
			}
			continue
		}
		if sp, ok := spanOf(p.Type); ok {
			sp.argBase, sp.argLen = rvArg0+nextReg, rvArg0+nextReg+1
			sp.baseReg, sp.lenReg = sp.argBase, sp.argLen
			nextReg += 2
			if parkSpans {
				// A call clobbers a0–a7, where the bound pair lives: park
				// the base, the raw length, and the normalized length in
				// three callee-saved registers (the checker follows the
				// copies: `mv sB, aB` is a base of the same span, `mv sL,
				// aL` a raw length the normalization pair may read).
				if g.usedCallee+3 > len(rvCallee) {
					return nil, unsupported("the span parameters exhaust the callee-saved registers")
				}
				sp.baseReg, sp.lenReg, sp.norm = rvCallee[g.usedCallee], rvCallee[g.usedCallee+1], rvCallee[g.usedCallee+2]
				g.usedCallee += 3
			}
			g.spans[p.Name.Value] = sp
			continue
		}
		return nil, unsupported("parameter %s of type %s", p.Name.Value, p.Type.String())
	}
	if nextReg > 8 || nextFReg > 8 {
		return nil, unsupported("the parameters exhaust the eight argument registers")
	}
	// The save area exists whenever a callee-saved register is written:
	// a variable, a parked span pair (a call, or a result leaving through
	// the pair's registers), or the result area's address.
	if hasVariables(fn) || (parkSpans && len(g.spans) > 0) || g.resultIndirect {
		g.saveArea = 8 * int64(len(rvCallee))
	}
	// In a leaf, each span's normalized length lives in an argument register
	// past the parameters (a leaf writes a0–a7 freely once they are
	// clobbers), written exactly once so the checker carries the fact
	// across labels.
	normNext := rvArg0 + nextReg
	for _, p := range fn.Parameters {
		if sp, isSpan := g.spans[p.Name.Value]; isSpan && !g.hasCalls {
			if normNext > rvArg0+7 {
				return nil, unsupported("the span parameters exhaust the argument registers (no register for a normalized length)")
			}
			sp.norm = normNext
			normNext++
			g.spans[p.Name.Value] = sp
		}
	}
	// Scalar parameters are the first variables, in order; a record
	// parameter becomes a record local.
	g.pushScope()
	for _, p := range fn.Parameters {
		if s, ok := scalarOf(p.Type); ok {
			g.declare(p.Name.Value, s)
		}
		if rp, isRecord := g.recordParams[p.Name.Value]; isRecord {
			rp.local = g.declareRecord(p.Name.Value, rp.layout)
		}
	}
	g.regIndex, g.fregIndex = nextReg, nextFReg
	g.head = g.newLabel("head")
	body, err := g.lowerBody(fn.Body)
	if err != nil {
		return nil, err
	}
	// The frame: ra at the base when the body calls, the callee-saved
	// area, then the slots, rounded to 16 bytes.
	frame := g.frameSize()
	if frame > rvMaxFrame {
		return nil, unsupported("a frame of %d bytes", frame)
	}
	out := &asm.Function{Name: fn.Name.Value, Signature: fn, Line: fn.Token.Line, Arch: asm.ArchRV64, Fallback: true, Records: records, ADTs: adts, Tables: tableSizes(g.tables)}
	if len(g.usedGlobals) > 0 {
		out.Globals = g.usedGlobals
	}
	g.line = fn.Token.Line
	var prologue []asm.Item
	if frame > 0 {
		out.Frame = frame
		prologue = append(prologue, g.ins("addi", rvSP(), rvSP(), imm(-frame)))
	}
	if g.hasCalls {
		prologue = append(prologue, g.ins("sd", rvReg(rvRA), rvMem(0)))
	}
	for i := 0; i < g.usedCallee; i++ {
		prologue = append(prologue, g.ins("sd", rvReg(rvCallee[i]), rvMem(g.saveBase()+int64(8*i))))
	}
	for i := 0; i < g.usedCalleeV; i++ {
		prologue = append(prologue, g.ins("fsd", rvFReg(rvFCallee[i]), rvMem(g.saveBaseV()+int64(8*i))))
	}
	// Bind the parameters at their contract registers and move the scalars
	// to their homes (a narrow one arrives canonical under the psABI); a
	// span's pair stays bound, its length normalized beside it; a record's
	// chunks are stored into its local, or the caller's copy is copied in.
	regIndex, fregIndex := 0, 0
	if g.resultIndirect {
		prologue = append(prologue, g.ins("mv", rvReg(g.resultAreaReg), rvReg(rvArg0)))
		regIndex = 1
	}
	for _, p := range fn.Parameters {
		if rp, isRecord := g.recordParams[p.Name.Value]; isRecord {
			binding := asm.Binding{Register: rvReg(rp.reg), Param: p.Name.Value, Line: fn.Token.Line}
			if rp.regs == 2 {
				second := rvReg(rp.reg + 1)
				binding.Length = &second
			}
			out.Bindings = append(out.Bindings, binding)
			if rp.indirect {
				prologue = append(prologue, g.copyIn(rp.local, rp.reg)...)
			} else {
				for i := 0; i < rp.regs; i++ {
					prologue = append(prologue, g.ins("sd", rvReg(rp.reg+i), g.slotMem(rp.local.offset+int64(8*i))))
				}
			}
			regIndex += rp.regs
			continue
		}
		if sp, isSpan := g.spans[p.Name.Value]; isSpan {
			length := rvReg(sp.argLen)
			out.Bindings = append(out.Bindings, asm.Binding{Register: rvReg(sp.argBase), Length: &length, Param: p.Name.Value, Line: fn.Token.Line})
			if sp.baseReg != sp.argBase {
				// Park the pair in its callee-saved registers (saved above).
				prologue = append(prologue, g.ins("mv", rvReg(sp.baseReg), rvReg(sp.argBase)), g.ins("mv", rvReg(sp.lenReg), rvReg(sp.argLen)))
			}
			prologue = append(prologue, g.ins("slli", rvReg(sp.norm), rvReg(sp.lenReg), imm(32)), g.ins("srli", rvReg(sp.norm), rvReg(sp.norm), imm(32)))
			regIndex += 2
			continue
		}
		if sc, _ := scalarOf(p.Type); sc.isFloat {
			out.Bindings = append(out.Bindings, asm.Binding{Register: rvFReg(rvFArg0 + fregIndex), Param: p.Name.Value, Line: fn.Token.Line})
			prologue = append(prologue, g.storeVar(p.Name.Value, vecBase+rvFArg0+fregIndex))
			fregIndex++
			continue
		}
		out.Bindings = append(out.Bindings, asm.Binding{Register: rvReg(rvArg0 + regIndex), Param: p.Name.Value, Line: fn.Token.Line})
		prologue = append(prologue, g.storeVar(p.Name.Value, rvArg0+regIndex))
		regIndex++
	}
	// The loop header a tail self-call re-enters: after the parameters are
	// in their homes.
	prologue = append(prologue, asm.Label{Name: g.head, Line: fn.Token.Line})
	out.Items = append(prologue, body...)
	// Clobbers: the scratch registers, and the argument registers a call
	// writes beyond the bound parameters (a0 is the result register when
	// there is a result). Callee-saved registers are saved, never clobbered.
	for _, r := range rvScratch {
		out.Clobbers = append(out.Clobbers, rvReg(r))
	}
	resultRegs := 0
	if g.result != nil {
		resultRegs = 1
	} else if g.resultRecord != nil && !g.resultIndirect {
		resultRegs = g.resultRecord.chunks()
	}
	if g.hasCalls {
		for r := g.regIndex; r <= 7; r++ {
			if r >= resultRegs {
				out.Clobbers = append(out.Clobbers, rvReg(rvArg0+r))
			}
		}
	}
	// Every placeable record and union of the program, for the checker's
	// composite binding rules — also under each signature type's own
	// spelling, which is what the checker looks up.
	out.Composites = Composites(records, adts)
	out.Constants = constants
	spell := func(expr ast.Expression) {
		if expr == nil {
			return
		}
		if name, isRecord := g.recordTypeName(expr); isRecord {
			if comp, placed := out.Composites[name]; placed {
				out.Composites[expr.String()] = comp
			}
		}
	}
	for _, p := range fn.Parameters {
		spell(p.Type)
	}
	spell(fn.ReturnType)
	out.TwoChunkResults = g.twoChunk
	for _, p := range fn.Parameters {
		if sp, isSpan := g.spans[p.Name.Value]; isSpan && !g.hasCalls {
			out.Clobbers = append(out.Clobbers, rvReg(sp.norm))
		}
	}
	if g.usedFloat {
		for _, r := range rvFScratch {
			out.Clobbers = append(out.Clobbers, rvFReg(r))
		}
		if g.hasCalls {
			for r := g.fregIndex; r <= 7; r++ {
				if !(g.result != nil && g.result.isFloat && r == 0) {
					out.Clobbers = append(out.Clobbers, rvFReg(rvFArg0+r))
				}
			}
		}
	}
	return out, nil
}

// ---- items ------------------------------------------------------------

func (g *rvGenerator) ins(mnemonic string, operands ...asm.Operand) asm.Instruction {
	g.noteWrite(mnemonic, operands)
	return asm.Instruction{Mnemonic: mnemonic, Operands: operands, Line: g.line}
}

// put appends an instruction unless the path is already terminated (the
// checker refuses unreachable code).
func (g *rvGenerator) put(instr asm.Instruction) {
	if g.terminated {
		return
	}
	g.items = append(g.items, instr)
}

func (g *rvGenerator) emit(mnemonic string, operands ...asm.Operand) {
	g.put(g.ins(mnemonic, operands...))
	if mnemonic == "j" || mnemonic == "ret" || mnemonic == "ebreak" {
		g.terminated = true
	}
}

func (g *rvGenerator) label(name string) {
	g.items = append(g.items, asm.Label{Name: name, Line: g.line})
	g.terminated = false
}

func (g *rvGenerator) jump(label string) { g.emit("j", asm.Symbol{Name: label}) }

// ---- the frame ------------------------------------------------------------

// saveBase is the frame offset of the callee-saved save area: past ra's
// 16-byte slot when the body calls.
func (g *rvGenerator) saveBase() int64 {
	if g.hasCalls {
		return 16
	}
	return 0
}

func (g *rvGenerator) frameSize() int64 {
	return (g.saveBase() + g.saveArea + g.saveAreaV + 8*g.nslots + 15) / 16 * 16
}

// saveBaseV is the frame offset of the fs0–fs11 save area: past the
// general callee-saved area.
func (g *rvGenerator) saveBaseV() int64 { return g.saveBase() + g.saveArea }

// slotMem is the frame address of a slot: past ra and the save areas.
func (g *rvGenerator) slotMem(offset int64) asm.Memory {
	return rvMem(g.saveBase() + g.saveArea + g.saveAreaV + offset)
}

// declare gives a variable a home in the current scope: a callee-saved
// register while they last, then a frame slot.
func (g *rvGenerator) declare(name string, s scalar) {
	offset, r := int64(-1), -1
	switch {
	case s.isFloat && g.usedCalleeV < len(rvFCallee):
		g.usedFloat = true
		r = vecBase + rvFCallee[g.usedCalleeV]
		g.usedCalleeV++
	case s.isFloat:
		g.usedFloat = true
		offset = 8 * g.nslots
		g.nslots++
	case g.usedCallee < len(rvCallee):
		r = rvCallee[g.usedCallee]
		g.usedCallee++
	default:
		offset = 8 * g.nslots
		g.nslots++
	}
	g.slots[name], g.types[name], g.regs[name] = offset, s, r
	g.scopes[len(g.scopes)-1][name] = slotBinding{offset: offset, typ: s, reg: r}
}

// storeVar moves a value held in register r into a variable's home; every
// home holds the full canonical 64-bit form.
func (g *rvGenerator) storeVar(name string, r int) asm.Instruction {
	if v, inReg := g.regs[name]; inReg && v >= 0 {
		return g.moveIns(v, r)
	}
	if r >= vecBase {
		return g.ins("fsd", rvReg(r), g.slotMem(g.slots[name]))
	}
	return g.ins("sd", rvReg(r), g.slotMem(g.slots[name]))
}

// loadVar brings a variable's value into register r.
func (g *rvGenerator) loadVar(name string, r int) asm.Instruction {
	if v, inReg := g.regs[name]; inReg && v >= 0 {
		return g.moveIns(r, v)
	}
	if r >= vecBase {
		return g.ins("fld", rvReg(r), g.slotMem(g.slots[name]))
	}
	return g.ins("ld", rvReg(r), g.slotMem(g.slots[name]))
}

// moveIns is the register move of a register's file: `mv` for the integer
// file, `fsgnj.d` (fmv.d: the whole 64 bits, so a NaN-boxed f32 travels
// intact) for the floating-point file.
func (g *rvGenerator) moveIns(dst, src int) asm.Instruction {
	if dst >= vecBase {
		return g.ins("fsgnj.d", rvReg(dst), rvReg(src), rvReg(src))
	}
	return g.ins("mv", rvReg(dst), rvReg(src))
}

func (g *rvGenerator) move(dst, src int) { g.put(g.moveIns(dst, src)) }

// ---- values -----------------------------------------------------------------

// rvCanonical is a value's canonical 64-bit form at a type, as a signed
// number (what `li` spells).
func rvCanonical(v uint64, s scalar) int64 {
	switch {
	case s.isBool:
		return int64(v & 1)
	case s.bits == 64:
		return int64(v)
	case s.bits == 32:
		return int64(int32(uint32(v)))
	case s.bits == 16 && s.signed:
		return int64(int16(uint16(v)))
	case s.bits == 16:
		return int64(uint16(v))
	case s.signed:
		return int64(int8(uint8(v)))
	default:
		return int64(uint8(v))
	}
}

// constant materializes a value at a type: `li` for what a 32-bit
// immediate reaches (the encoder spends lui and addiw on it), else the two
// halves through a scratch register: `li hi; slli 32; li lo; add`.
func (g *rvGenerator) constant(r int, v uint64, s scalar) error {
	if s.isFloat {
		return unsupported("an integer constant at %s", s.name)
	}
	c := rvCanonical(v, s)
	dst := rvReg(r)
	if c >= -(1<<31) && c < 1<<31 {
		g.emit("li", dst, imm(c))
		return nil
	}
	lo := int64(int32(uint32(uint64(c))))
	hi := int64(int32(uint32((uint64(c) - uint64(lo)) >> 32)))
	t, err := g.alloc(scalars["u64"])
	if err != nil {
		return err
	}
	g.emit("li", dst, imm(hi))
	g.emit("slli", dst, dst, imm(32))
	g.emit("li", rvReg(t), imm(lo))
	g.emit("add", dst, dst, rvReg(t))
	g.release(t)
	return nil
}

// normalize re-establishes a narrow type's canonical form after an
// operation on the whole register. The 32-bit types are kept canonical by
// the W-form instructions; 64-bit values need nothing.
func (g *rvGenerator) normalize(r int, s scalar) {
	for _, it := range g.normalizeInto(r, s) {
		g.put(it)
	}
}

func (g *rvGenerator) normalizeInto(r int, s scalar) []asm.Instruction {
	reg := rvReg(r)
	switch {
	case s.isBool, s.bits >= 32:
		return nil
	case s.bits == 8 && s.signed:
		return []asm.Instruction{g.ins("slli", reg, reg, imm(56)), g.ins("srai", reg, reg, imm(56))}
	case s.bits == 8:
		return []asm.Instruction{g.ins("andi", reg, reg, imm(255))}
	case s.signed:
		return []asm.Instruction{g.ins("slli", reg, reg, imm(48)), g.ins("srai", reg, reg, imm(48))}
	default:
		return []asm.Instruction{g.ins("slli", reg, reg, imm(48)), g.ins("srli", reg, reg, imm(48))}
	}
}

// sameType reports two scalar types with one canonical form.
func sameType(a, b scalar) bool {
	return a.bits == b.bits && a.signed == b.signed && a.isBool == b.isBool && a.isFloat == b.isFloat
}

// adapt moves a register's value from one type's canonical form to
// another's: the bits at the new width, a widening of a signed operand
// sign-extending, everything else truncating or zero-filling — the C
// conversions the constructors and `trunc`/`bits` denote.
func (g *rvGenerator) adapt(r int, from, to scalar) error {
	if sameType(from, to) {
		return nil
	}
	if from.isFloat || to.isFloat {
		return unsupported("an implicit conversion between %s and %s", from.name, to.name)
	}
	reg := rvReg(r)
	switch {
	case to.bits == 64:
		if from.bits == 32 && !from.signed {
			// A canonical u32 is sign-extended: zero-extend it.
			g.emit("slli", reg, reg, imm(32))
			g.emit("srli", reg, reg, imm(32))
		}
		// Narrower unsigned values are zero-extended and signed ones
		// sign-extended already: the 64-bit reading is the C conversion.
	case to.bits == 32:
		if from.bits == 64 {
			g.emit("sext.w", reg, reg)
		}
		// An 8- or 16-bit value is already a canonical 32-bit one.
	default:
		g.normalize(r, to)
	}
	return nil
}

// exprAs evaluates an expression and adapts it to the type the context
// demands (a variable of another width in an arithmetic or comparison
// context promotes as C does).
func (g *rvGenerator) exprAs(expr ast.Expression, typ scalar) (int, error) {
	r, err := g.expr(expr, &typ)
	if err != nil {
		return 0, err
	}
	actual, err := g.typeOf(expr, &typ)
	if err != nil {
		return 0, err
	}
	if err := g.adapt(r, actual, typ); err != nil {
		return 0, err
	}
	return r, nil
}

// ---- the body -------------------------------------------------------------

// lowerBody lowers the function body; the result (if any) ends in a0 and
// control reaches ret with the frame released.
func (g *rvGenerator) lowerBody(body ast.Expression) ([]asm.Item, error) {
	retLabel := g.newLabel("ret")
	trapLabel := g.newLabel("trap")
	g.trap = trapLabel
	switch b := body.(type) {
	case *ast.BlockExpression:
		if b.Block == nil {
			return nil, unsupported("an empty body")
		}
		if err := g.lowerStatements(b.Block.Statements, true); err != nil {
			return nil, err
		}
	default:
		if g.resultRecord != nil {
			if err := g.resultRecordExpr(body); err != nil {
				return nil, err
			}
			break
		}
		if g.result == nil {
			return nil, unsupported("an expression body in a function without a result")
		}
		if err := g.resultExpr(body); err != nil {
			return nil, err
		}
	}
	g.label(retLabel)
	g.epilogue()
	if g.usedTrap {
		g.label(trapLabel)
		g.emit("ebreak")
	}
	return g.items, nil
}

func (g *rvGenerator) epilogue() {
	frame := g.frameSize()
	for i := 0; i < g.usedCalleeV; i++ {
		g.emit("fld", rvFReg(rvFCallee[i]), rvMem(g.saveBaseV()+int64(8*i)))
	}
	for i := 0; i < g.usedCallee; i++ {
		g.emit("ld", rvReg(rvCallee[i]), rvMem(g.saveBase()+int64(8*i)))
	}
	if g.hasCalls {
		g.emit("ld", rvReg(rvRA), rvMem(0))
	}
	if frame > 0 {
		g.emit("addi", rvSP(), rvSP(), imm(frame))
	}
	g.emit("ret")
}

// moveResult places a value in the result register: a0, or fa0 for a float.
func (g *rvGenerator) moveResult(r int) {
	if r >= vecBase {
		g.move(vecBase+rvFArg0, r)
		return
	}
	g.emit("mv", rvReg(rvArg0), rvReg(r))
}

// lowerStatements lowers a block; in a function body the last expression
// statement is the result.
func (g *rvGenerator) lowerStatements(stmts []ast.Statement, functionBody bool) error {
	for i, stmt := range stmts {
		last := functionBody && i == len(stmts)-1
		g.line = statementLine(stmt)
		switch s := stmt.(type) {
		case *ast.VariableDeclaration:
			if elem, length, isArray := arrayOf(s.Type); isArray {
				if err := g.lowerArrayDeclaration(s, elem, length); err != nil {
					return err
				}
				continue
			}
			if typeName, isRecord := g.recordTypeName(s.Type); isRecord {
				if err := g.lowerRecordDeclaration(s, typeName); err != nil {
					return err
				}
				continue
			}
			if s.Value == nil {
				return unsupported("a local without an initializer")
			}
			var typ scalar
			if s.Type != nil {
				t, ok := scalarOf(s.Type)
				if !ok {
					return unsupported("a local of type %s", s.Type.String())
				}
				typ = t
			} else {
				t, err := g.typeOf(s.Value, nil)
				if err != nil {
					return err
				}
				typ = t
			}
			r, err := g.exprAs(s.Value, typ)
			if err != nil {
				return err
			}
			g.declare(s.Name.Value, typ)
			g.put(g.storeVar(s.Name.Value, r))
			g.release(r)
		case *ast.AssignmentStatement:
			if dst, isRecord := g.records[s.Name.Value]; isRecord {
				// `q = p`: a whole-record copy.
				from, err := g.recordValueAs(s.Value, dst.layout)
				if err != nil {
					return err
				}
				if from.layout != dst.layout {
					return unsupported("an assignment of a %s to the %s %s", from.layout.name, dst.layout.name, s.Name.Value)
				}
				if err := g.copyRecord(dst, from); err != nil {
					return err
				}
				g.releaseTemps(from.temps)
				continue
			}
			typ, ok := g.types[s.Name.Value]
			if !ok {
				global, globalType, isGlobal := g.globalOf(s.Name.Value)
				if !isGlobal {
					return unsupported("an assignment to %s", s.Name.Value)
				}
				// `G = e`: the global's cell written through its address.
				r, err := g.exprAs(s.Value, globalType)
				if err != nil {
					return err
				}
				if err := g.rvGlobalStore(s.Name.Value, global, r); err != nil {
					return err
				}
				g.release(r)
				continue
			}
			r, err := g.exprAs(s.Value, typ)
			if err != nil {
				return err
			}
			g.put(g.storeVar(s.Name.Value, r))
			g.release(r)
		case *ast.IndexAssignmentStatement:
			if err := g.elementStore(s); err != nil {
				return err
			}
		case *ast.WhileStatement:
			if err := g.lowerWhile(s); err != nil {
				return err
			}
		case *ast.IfStatement:
			if err := g.lowerIf(s); err != nil {
				return err
			}
		case *ast.BreakStatement:
			if len(g.loops) == 0 {
				return unsupported("break outside a loop")
			}
			g.jump(g.loops[len(g.loops)-1])
		case *ast.BlockStatement:
			g.pushScope()
			err := g.lowerStatements(s.Statements, false)
			g.popScope()
			if err != nil {
				return err
			}
		case *ast.ExpressionStatement:
			if last && !s.Discard {
				if g.resultRecord != nil {
					if err := g.resultRecordExpr(s.Expression); err != nil {
						return err
					}
					continue
				}
				if g.result == nil {
					// A unit function whose last statement is an expression:
					// a call, an assert, or a conditional or match in
					// statement position.
					if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
						if err := g.lowerConditionalStatement(match); err != nil {
							return err
						}
						continue
					}
					if err := g.effect(s.Expression); err != nil {
						return err
					}
					continue
				}
				if err := g.resultExpr(s.Expression); err != nil {
					return err
				}
				continue
			}
			if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
				if err := g.lowerConditionalStatement(match); err != nil {
					return err
				}
				continue
			}
			if err := g.effect(s.Expression); err != nil {
				return err
			}
		default:
			return unsupported("%T", stmt)
		}
	}
	if functionBody && (g.result != nil || g.resultRecord != nil) {
		if len(stmts) == 0 {
			return unsupported("an empty body with a result")
		}
		if es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement); !ok || es.Discard {
			return unsupported("a body whose last statement is not its result")
		}
	}
	return nil
}

// effect evaluates an expression for its effects: a call, or assert.
func (g *rvGenerator) effect(expr ast.Expression) error {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall {
		return unsupported("an expression statement that is not a call")
	}
	ident, isIdent := call.Function.(*ast.Identifier)
	if !isIdent {
		return unsupported("a call through a value")
	}
	if ident.Value == "assert" && len(call.Arguments) == 1 {
		r, err := g.exprAs(call.Arguments[0], scalars["Bool"])
		if err != nil {
			return err
		}
		g.usedTrap = true
		g.emit("beqz", rvReg(r), asm.Symbol{Name: g.trap})
		g.release(r)
		return nil
	}
	r, err := g.call(call)
	if err != nil {
		return err
	}
	if r >= 0 {
		g.release(r)
	}
	return nil
}

func (g *rvGenerator) lowerWhile(loop *ast.WhileStatement) error {
	head, end := g.newLabel("loop"), g.newLabel("done")
	g.label(head)
	if err := g.condition(loop.Condition, end); err != nil {
		return err
	}
	g.loops = append(g.loops, end)
	g.pushScope()
	err := g.lowerStatements(loop.Body.Statements, false)
	g.popScope()
	g.loops = g.loops[:len(g.loops)-1]
	if err != nil {
		return err
	}
	g.jump(head)
	g.label(end)
	return nil
}

func (g *rvGenerator) lowerIf(s *ast.IfStatement) error {
	elseLabel, end := g.newLabel("else"), g.newLabel("endif")
	if err := g.condition(s.Condition, elseLabel); err != nil {
		return err
	}
	if s.Consequence != nil {
		g.pushScope()
		err := g.lowerStatements(s.Consequence.Statements, false)
		g.popScope()
		if err != nil {
			return err
		}
	}
	g.jump(end)
	g.label(elseLabel)
	switch alt := s.Alternative.(type) {
	case nil:
	case *ast.IfStatement:
		if err := g.lowerIf(alt); err != nil {
			return err
		}
	case *ast.BlockStatement:
		g.pushScope()
		err := g.lowerStatements(alt.Statements, false)
		g.popScope()
		if err != nil {
			return err
		}
	default:
		return unsupported("an else of %T", alt)
	}
	g.label(end)
	return nil
}

// lowerConditionalStatement: `c ? { ... } | { ... }` in statement position.
func (g *rvGenerator) lowerConditionalStatement(match *ast.MatchExpression) error {
	whenTrue, whenFalse, ok := statementConditional(match)
	if !ok {
		return g.lowerMatch(match, g.lowerArm)
	}
	elseLabel, end := g.newLabel("else"), g.newLabel("endif")
	if err := g.condition(match.Scrutinee, elseLabel); err != nil {
		return err
	}
	if err := g.lowerArm(whenTrue); err != nil {
		return err
	}
	if whenFalse == nil {
		g.label(elseLabel)
		return nil
	}
	g.jump(end)
	g.label(elseLabel)
	if err := g.lowerArm(whenFalse); err != nil {
		return err
	}
	g.label(end)
	return nil
}

func (g *rvGenerator) lowerArm(arm ast.Expression) error {
	if arm == nil {
		return nil
	}
	if chained, isMatch := arm.(*ast.MatchExpression); isMatch {
		return g.lowerConditionalStatement(chained)
	}
	block, isBlock := arm.(*ast.BlockExpression)
	if !isBlock {
		// An arm that is a call or assert in statement position.
		return g.effect(arm)
	}
	if block.Block == nil {
		return nil
	}
	g.pushScope()
	defer g.popScope()
	return g.lowerStatements(block.Block.Statements, false)
}

// ---- conditions -------------------------------------------------------------

// rvBranchWhenTrue and rvBranchWhenFalse spell the conditional branch that
// jumps when a comparison holds, or when it fails, as {unsigned, signed};
// `<=` and `>` compare the operands in the other order.
var rvBranchWhenTrue = map[string][2]string{
	"==": {"beq", "beq"}, "!=": {"bne", "bne"},
	"<": {"bltu", "blt"}, ">=": {"bgeu", "bge"},
	"<=": {"bgeu", "bge"}, ">": {"bltu", "blt"},
}
var rvBranchWhenFalse = map[string][2]string{
	"==": {"bne", "bne"}, "!=": {"beq", "beq"},
	"<": {"bgeu", "bge"}, ">=": {"bltu", "blt"},
	"<=": {"bltu", "blt"}, ">": {"bgeu", "bge"},
}

// condition evaluates a Bool expression and branches to target when false.
func (g *rvGenerator) condition(expr ast.Expression, target string) error {
	return g.conditionBranch(expr, target, true)
}

// conditionBranch evaluates a Bool expression and branches to target when
// it is false (jumpIfFalse) or true. A comparison branches on its two
// operands directly — the ISA compares in the branch — so a loop's exit
// test is one instruction over the variables' registers.
func (g *rvGenerator) conditionBranch(expr ast.Expression, target string, jumpIfFalse bool) error {
	if infix, ok := expr.(*ast.InfixExpression); ok {
		if _, isComparison := conditionCodes[infix.Operator]; isComparison {
			operand, err := g.operandType(infix)
			if err == nil && !operand.isFloat {
				l, lTemp, err := g.operand(infix.Left, operand)
				if err != nil {
					return err
				}
				r, rTemp, err := g.operand(infix.Right, operand)
				if err != nil {
					return err
				}
				table := rvBranchWhenTrue
				if jumpIfFalse {
					table = rvBranchWhenFalse
				}
				op := table[infix.Operator][0]
				if operand.signed {
					op = table[infix.Operator][1]
				}
				a, b := l, r
				if infix.Operator == "<=" || infix.Operator == ">" {
					a, b = r, l
				}
				g.emit(op, rvReg(a), rvReg(b), asm.Symbol{Name: target})
				if lTemp {
					g.release(l)
				}
				if rTemp {
					g.release(r)
				}
				return nil
			}
		}
	}
	r, err := g.exprAs(expr, scalars["Bool"])
	if err != nil {
		return err
	}
	if jumpIfFalse {
		g.emit("beqz", rvReg(r), asm.Symbol{Name: target})
	} else {
		g.emit("bnez", rvReg(r), asm.Symbol{Name: target})
	}
	g.release(r)
	return nil
}

// operand yields a register holding an expression at a type: a variable's
// own register when its type has the same canonical form (temp false),
// else a fresh scratch register (temp true).
func (g *rvGenerator) operand(expr ast.Expression, typ scalar) (reg int, temp bool, err error) {
	if ident, isIdent := expr.(*ast.Identifier); isIdent {
		if v, inReg := g.regs[ident.Value]; inReg && v >= 0 {
			if t, ok := g.types[ident.Value]; ok && sameType(t, typ) {
				return v, false, nil
			}
		}
	}
	r, err := g.exprAs(expr, typ)
	return r, true, err
}

// ---- expressions ------------------------------------------------------------

// expr evaluates an expression into a fresh scratch register in the
// canonical form of its own type; hint types literals.
func (g *rvGenerator) expr(expr ast.Expression, hint *scalar) (int, error) {
	typ, err := g.typeOf(expr, hint)
	if err != nil {
		return 0, err
	}
	if typ.isFloat && g.softFloat {
		return 0, unsupported("floating point on a soft-float target")
	}
	switch e := expr.(type) {
	case *ast.FloatLiteral:
		value, ok := typechecker.FloatLiteralValue(e.Text, typ.name)
		if !ok {
			return 0, unsupported("the float literal %s at %s", e.Text, typ.name)
		}
		r, err := g.alloc(typ)
		if err != nil {
			return 0, err
		}
		if err := g.floatConstant(r, value, typ); err != nil {
			return 0, err
		}
		return r, nil
	case *ast.IntegerLiteral:
		r, err := g.alloc(typ)
		if err != nil {
			return 0, err
		}
		if err := g.constant(r, uint64(e.Value), typ); err != nil {
			return 0, err
		}
		return r, nil
	case *ast.Boolean:
		r, err := g.alloc(typ)
		if err != nil {
			return 0, err
		}
		v := uint64(0)
		if e.Value {
			v = 1
		}
		if err := g.constant(r, v, typ); err != nil {
			return 0, err
		}
		return r, nil
	case *ast.Identifier:
		r, err := g.alloc(typ)
		if err != nil {
			return 0, err
		}
		if c, isConst := g.constantOf(e.Value); isConst {
			if err := g.constant(r, c.Value, typ); err != nil {
				return 0, err
			}
			return r, nil
		}
		if global, globalType, isGlobal := g.globalOf(e.Value); isGlobal {
			if globalType != typ {
				return 0, unsupported("the global %s (%s) read as %s", e.Value, globalType.name, typ.name)
			}
			if err := g.rvGlobalLoad(e.Value, global, r); err != nil {
				return 0, err
			}
			return r, nil
		}
		g.put(g.loadVar(e.Value, r))
		return r, nil
	case *ast.InfixExpression:
		return g.infix(e, typ)
	case *ast.PrefixExpression:
		return g.prefix(e, typ)
	case *ast.IndexExpression:
		return g.element(e)
	case *ast.InvocationExpression:
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return 0, unsupported("a call through a value")
		}
		if ident.Value == "len" && len(e.Arguments) == 1 {
			if _, _, length, isArray := g.staticArrayOf(e.Arguments[0]); isArray {
				r, err := g.alloc(scalars["u32"])
				if err != nil {
					return 0, err
				}
				if err := g.constant(r, uint64(length), scalars["u32"]); err != nil {
					return 0, err
				}
				return r, nil
			}
			sp, err := g.spanOperand(e.Arguments[0])
			if err != nil {
				return 0, err
			}
			r, err := g.alloc(scalars["u32"])
			if err != nil {
				return 0, err
			}
			// The normalized length is zero-extended; a canonical u32 is
			// sign-extended from bit 31.
			g.emit("sext.w", rvReg(r), rvReg(sp.norm))
			return r, nil
		}
		if target, isConv := scalars[ident.Value]; isConv && len(e.Arguments) == 1 && ident.Value != "byte" {
			return g.convert(e.Arguments[0], target)
		}
		if targetName, op, _, isConv := typechecker.ConversionParts(ident.Value); isConv && len(e.Arguments) == 1 {
			return g.convertOp(e.Arguments[0], scalars[targetName], op)
		}
		if typechecker.FloatIntrinsicName(ident.Value) {
			if _, shadowed := g.functions[ident.Value]; !shadowed {
				return g.intrinsic(e, typ)
			}
		}
		return g.call(e)
	case *ast.MatchExpression:
		whenTrue, whenFalse, isBool := boolConditional(e)
		if !isBool {
			out, err := g.alloc(typ)
			if err != nil {
				return 0, err
			}
			err = g.lowerMatch(e, func(body ast.Expression) error {
				r, err := g.exprAs(body, typ)
				if err != nil {
					return err
				}
				g.move(out, r)
				g.release(r)
				return nil
			})
			if err != nil {
				return 0, err
			}
			return out, nil
		}
		elseLabel, end := g.newLabel("else"), g.newLabel("endif")
		if err := g.condition(e.Scrutinee, elseLabel); err != nil {
			return 0, err
		}
		out, err := g.alloc(typ)
		if err != nil {
			return 0, err
		}
		t, err := g.exprAs(whenTrue, typ)
		if err != nil {
			return 0, err
		}
		g.move(out, t)
		g.release(t)
		g.jump(end)
		g.label(elseLabel)
		f, err := g.exprAs(whenFalse, typ)
		if err != nil {
			return 0, err
		}
		g.move(out, f)
		g.release(f)
		g.label(end)
		return out, nil
	case *ast.BlockExpression:
		if e.Block == nil || len(e.Block.Statements) == 0 {
			return 0, unsupported("an empty block in value position")
		}
		g.pushScope()
		defer g.popScope()
		stmts := e.Block.Statements
		if err := g.lowerStatements(stmts[:len(stmts)-1], false); err != nil {
			return 0, err
		}
		es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement)
		if !ok {
			return 0, unsupported("a block whose last statement is not an expression")
		}
		return g.exprAs(es.Expression, typ)
	}
	return 0, unsupported("%T", expr)
}

// rvALU spells the register-register operation of an operator at a width:
// the W forms for 32-bit types (they keep the canonical form), the full
// forms otherwise (the narrow types re-normalize after).
func rvALU(op string, typ scalar) string {
	wide := typ.bits != 32
	switch op {
	case "+":
		return pick(wide, "add", "addw")
	case "-":
		return pick(wide, "sub", "subw")
	case "*":
		return pick(wide, "mul", "mulw")
	case "&":
		return "and"
	case "|":
		return "or"
	case "^":
		return "xor"
	case "<<":
		return pick(wide, "sll", "sllw")
	case ">>":
		return pick(wide, "srl", "srlw")
	case "/":
		if typ.signed {
			return pick(wide, "div", "divw")
		}
		return pick(wide, "divu", "divuw")
	case "%":
		if typ.signed {
			return pick(wide, "rem", "remw")
		}
		return pick(wide, "remu", "remuw")
	}
	return ""
}

func pick(wide bool, full, w string) string {
	if wide {
		return full
	}
	return w
}

func (g *rvGenerator) infix(e *ast.InfixExpression, typ scalar) (int, error) {
	switch e.Operator {
	case "&&", "||":
		b := scalars["Bool"]
		out, err := g.alloc(b)
		if err != nil {
			return 0, err
		}
		end := g.newLabel("short")
		l, err := g.exprAs(e.Left, b)
		if err != nil {
			return 0, err
		}
		g.emit("mv", rvReg(out), rvReg(l))
		g.release(l)
		if e.Operator == "&&" {
			g.emit("beqz", rvReg(out), asm.Symbol{Name: end})
		} else {
			g.emit("bnez", rvReg(out), asm.Symbol{Name: end})
		}
		rr, err := g.exprAs(e.Right, b)
		if err != nil {
			return 0, err
		}
		g.emit("mv", rvReg(out), rvReg(rr))
		g.release(rr)
		g.label(end)
		return out, nil
	case "==", "!=", "<", "<=", ">", ">=":
		operand, err := g.operandType(e)
		if err != nil {
			return 0, err
		}
		l, err := g.exprAs(e.Left, operand)
		if err != nil {
			return 0, err
		}
		r, err := g.exprAs(e.Right, operand)
		if err != nil {
			return 0, err
		}
		if operand.isFloat {
			return g.floatCompare(e.Operator, l, r, operand)
		}
		L, R, Z := rvReg(l), rvReg(r), rvReg(rvZero)
		slt := "sltu"
		if operand.signed {
			slt = "slt"
		}
		switch e.Operator {
		case "==":
			g.emit("sub", L, L, R)
			g.emit("sltiu", L, L, imm(1))
		case "!=":
			g.emit("sub", L, L, R)
			g.emit("sltu", L, Z, L)
		case "<":
			g.emit(slt, L, L, R)
		case ">":
			g.emit(slt, L, R, L)
		case "<=":
			g.emit(slt, L, R, L)
			g.emit("xori", L, L, imm(1))
		case ">=":
			g.emit(slt, L, L, R)
			g.emit("xori", L, L, imm(1))
		}
		g.release(r)
		return l, nil
	}
	l, err := g.exprAs(e.Left, typ)
	if err != nil {
		return 0, err
	}
	L := rvReg(l)
	if typ.isFloat {
		r, err := g.exprAs(e.Right, typ)
		if err != nil {
			return 0, err
		}
		op, ok := map[string]string{"+": "fadd", "-": "fsub", "*": "fmul", "/": "fdiv"}[e.Operator]
		if !ok {
			return 0, unsupported("operator %s on %s", e.Operator, typ.name)
		}
		// Nothing is contracted: the C backend's FP_CONTRACT OFF.
		g.emit(op+fsuffix(typ), L, L, rvReg(r))
		g.release(r)
		return l, nil
	}
	switch e.Operator {
	case "<<", ">>":
		if typ.signed {
			return 0, unsupported("a shift of a signed operand")
		}
		count, isConst := constantValue(e.Right)
		if isConst {
			if count < 0 || count >= int64(typ.bits) {
				return 0, unsupported("a constant shift count of %d", count)
			}
			op := pick(typ.bits != 32, "slli", "slliw")
			if e.Operator == ">>" {
				op = pick(typ.bits != 32, "srli", "srliw")
			}
			g.emit(op, L, L, imm(count))
			g.normalize(l, typ)
			return l, nil
		}
		r, err := g.exprAs(e.Right, typ)
		if err != nil {
			return 0, err
		}
		// A count at or beyond the width traps (10-syntax.md §3b).
		g.usedTrap = true
		bound, err := g.alloc(scalars["u64"])
		if err != nil {
			return 0, err
		}
		g.emit("li", rvReg(bound), imm(int64(typ.bits)))
		g.emit("bgeu", rvReg(r), rvReg(bound), asm.Symbol{Name: g.trap})
		g.release(bound)
		g.emit(rvALU(e.Operator, typ), L, L, rvReg(r))
		g.release(r)
		g.normalize(l, typ)
		return l, nil
	}
	r, err := g.exprAs(e.Right, typ)
	if err != nil {
		return 0, err
	}
	R := rvReg(r)
	switch e.Operator {
	case "+", "-", "*", "&", "|", "^":
		g.emit(rvALU(e.Operator, typ), L, L, R)
	case "/", "%":
		// Division by zero traps; MIN / -1 and MIN % -1 are the ISA's total
		// results, which are the C helpers' (the quotient MIN, remainder 0).
		g.usedTrap = true
		g.emit("beqz", R, asm.Symbol{Name: g.trap})
		g.emit(rvALU(e.Operator, typ), L, L, R)
	default:
		return 0, unsupported("operator %s", e.Operator)
	}
	g.release(r)
	g.normalize(l, typ)
	return l, nil
}

func (g *rvGenerator) prefix(e *ast.PrefixExpression, typ scalar) (int, error) {
	switch e.Operator {
	case "!":
		r, err := g.exprAs(e.Right, scalars["Bool"])
		if err != nil {
			return 0, err
		}
		g.emit("xori", rvReg(r), rvReg(r), imm(1))
		return r, nil
	case "-":
		r, err := g.exprAs(e.Right, typ)
		if err != nil {
			return 0, err
		}
		if typ.isFloat {
			// The sign bit flips, NaN and zero included (fneg).
			g.emit("fsgnjn"+fsuffix(typ), rvReg(r), rvReg(r), rvReg(r))
			return r, nil
		}
		g.emit(pick(typ.bits != 32, "neg", "negw"), rvReg(r), rvReg(r))
		g.normalize(r, typ)
		return r, nil
	case "^":
		r, err := g.exprAs(e.Right, typ)
		if err != nil {
			return 0, err
		}
		g.emit("not", rvReg(r), rvReg(r))
		g.normalize(r, typ)
		return r, nil
	}
	return 0, unsupported("prefix operator %s", e.Operator)
}

// convert lowers `T(x)`, `T_trunc_S(x)`, `T_bits_S(x)`: the operand in its
// own form, adapted to the target's.
func (g *rvGenerator) convert(operand ast.Expression, target scalar) (int, error) {
	return g.convertOp(operand, target, "")
}

// convertOp lowers a conversion with its operation name ("" for a
// constructor, else trunc/bits/round/saturating).
func (g *rvGenerator) convertOp(operand ast.Expression, target scalar, op string) (int, error) {
	source, err := g.typeOf(operand, &target)
	if err != nil {
		return 0, err
	}
	r, err := g.expr(operand, &source)
	if err != nil {
		return 0, err
	}
	if source.isFloat || target.isFloat {
		return g.convertFloat(r, source, target, op)
	}
	if op != "" && op != "trunc" && op != "bits" {
		return 0, unsupported("a %s conversion", op)
	}
	if err := g.adapt(r, source, target); err != nil {
		return 0, err
	}
	return r, nil
}

// call lowers a call to a program function with a scalar signature: the
// arguments evaluate into scratch registers first (an argument may itself
// call), then move to a0–a7; the live scratch registers are spilled around
// `call` (the callee owns t0–t6 and a0–a7); the result comes back in a0.
func (g *rvGenerator) call(e *ast.InvocationExpression) (int, error) {
	return g.callWith(e, nil)
}

// callWith lowers a call; recordResult, when the callee returns a record,
// is the temp that receives it: chunks stored from a0/a1, or written by
// the callee through the area address passed as the hidden first
// argument.
func (g *rvGenerator) callWith(e *ast.InvocationExpression, recordResult *recordLocal) (int, error) {
	ident, isIdent := e.Function.(*ast.Identifier)
	if !isIdent {
		return 0, unsupported("a call through a value")
	}
	callee, ok := g.functions[g.calleeName(ident)]
	if !ok {
		return 0, unsupported("a call to %s", ident.Value)
	}
	if len(e.Arguments) != len(callee.Parameters) || len(e.Arguments) > 8 {
		return 0, unsupported("a call to %s with %d arguments", ident.Value, len(e.Arguments))
	}
	var resultType *scalar
	var regs []int
	fixed := map[int]bool{} // a parked span's registers, passed on: never released
	if callee.ReturnType != nil && callee.ReturnType.String() != "()" {
		if name, isRecord := g.recordTypeName(callee.ReturnType); isRecord {
			if recordResult == nil {
				return 0, unsupported("a call to %s (returning a record) in scalar position", ident.Value)
			}
			layout, err := g.layoutOf(name)
			if err != nil {
				return 0, err
			}
			if layout.hasFloat {
				return 0, unsupported("a call to %s returning %s (floating-point fields)", ident.Value, name)
			}
			if layout.size > 16 {
				// The callee writes its result into the temp: its address
				// is the hidden first argument.
				area, err := g.alloc(scalars["u64"])
				if err != nil {
					return 0, err
				}
				g.emit("addi", rvReg(area), rvSP(), imm(g.slotMem(recordResult.offset).Offset))
				regs = append(regs, area)
			} else if layout.chunks() == 2 {
				g.twoChunk[ident.Value] = true
			}
		} else {
			s, ok := scalarOf(callee.ReturnType)
			if !ok {
				return 0, unsupported("a call to %s returning %s", ident.Value, callee.ReturnType.String())
			}
			resultType = &s
		}
	}
	for i, arg := range e.Arguments {
		p := callee.Parameters[i]
		if p.Variadic {
			return 0, unsupported("a call to %s (parameter %s is variadic)", ident.Value, p.Name.Value)
		}
		if name, isRecord := g.recordTypeName(p.Type); isRecord {
			layout, err := g.layoutOf(name)
			if err != nil {
				return 0, err
			}
			if layout.hasFloat {
				return 0, unsupported("a call to %s passing %s (floating-point fields)", ident.Value, name)
			}
			rec, err := g.recordValueAs(arg, layout)
			if err != nil {
				return 0, err
			}
			if rec.layout != layout {
				return 0, unsupported("a call to %s: a %s where %s is expected", ident.Value, rec.layout.name, name)
			}
			if layout.size > 16 {
				// By reference to a copy the callee may read.
				copied := g.tempRecord(layout)
				if err := g.copyRecord(copied, rec); err != nil {
					return 0, err
				}
				g.releaseTemps(rec.temps)
				address, err := g.alloc(scalars["u64"])
				if err != nil {
					return 0, err
				}
				g.emit("addi", rvReg(address), rvSP(), imm(g.slotMem(copied.offset).Offset))
				regs = append(regs, address)
				continue
			}
			for c := 0; c < layout.chunks(); c++ {
				r, err := g.alloc(scalars["u64"])
				if err != nil {
					return 0, err
				}
				g.emit("ld", rvReg(r), g.slotMem(rec.offset+int64(8*c)))
				regs = append(regs, r)
			}
			g.releaseTemps(rec.temps)
			continue
		}
		if target, isSpan := spanOf(p.Type); isSpan {
			if name, isIdent := arg.(*ast.Identifier); isIdent {
				// A span parameter passed on: its parked pair.
				sp, isNamed := g.spans[name.Value]
				if !isNamed {
					return 0, unsupported("a call to %s: %s is not a span", ident.Value, name.Value)
				}
				if !sameElements(sp, target) || (target.writable && !sp.writable) {
					return 0, unsupported("a call to %s: %s does not fit the span type", ident.Value, name.Value)
				}
				regs = append(regs, sp.baseReg, sp.lenReg)
				fixed[sp.baseReg], fixed[sp.lenReg] = true, true
				continue
			}
			// `view(&buf)` / `span(&buf)` over an owned array local: the
			// callee receives the {frame address, N} pair.
			base, length, err := g.arraySpanArgument(ident.Value, arg, target)
			if err != nil {
				return 0, err
			}
			regs = append(regs, base, length)
			continue
		}
		s, ok := scalarOf(p.Type)
		if !ok {
			return 0, unsupported("a call to %s (parameter %s: %s)", ident.Value, p.Name.Value, p.Type.String())
		}
		r, err := g.exprAs(arg, s)
		if err != nil {
			return 0, err
		}
		regs = append(regs, r)
	}

	general, floating := 0, 0
	for _, r := range regs {
		if r >= vecBase {
			g.move(vecBase+rvFArg0+floating, r)
			floating++
		} else {
			g.emit("mv", rvReg(rvArg0+general), rvReg(r))
			general++
		}
		if !fixed[r] {
			g.release(r)
		}
	}
	if general > 8 || floating > 8 {
		return 0, unsupported("a call to %s: the arguments exhaust the argument registers", ident.Value)
	}
	var spilled []int
	for _, r := range g.live {
		if !g.defined[r] {
			continue // allocated for an enclosing result, not yet written
		}
		if _, ok := g.spill[r]; !ok {
			g.spill[r] = 8 * g.nslots
			g.nslots++
		}
		g.emit(pick(r < vecBase, "sd", "fsd"), rvReg(r), g.slotMem(g.spill[r]))
		spilled = append(spilled, r)
	}
	g.emit("call", asm.Symbol{Name: g.calleeName(ident)})
	for _, r := range spilled {
		g.emit(pick(r < vecBase, "ld", "fld"), rvReg(r), g.slotMem(g.spill[r]))
	}
	if recordResult != nil {
		if recordResult.layout.size <= 16 {
			for c := 0; c < recordResult.layout.chunks(); c++ {
				g.emit("sd", rvReg(rvArg0+c), g.slotMem(recordResult.offset+int64(8*c)))
			}
		}
		return -1, nil
	}
	if resultType == nil {
		return -1, nil
	}
	out, err := g.alloc(*resultType)
	if err != nil {
		return 0, err
	}
	if resultType.isFloat {
		g.move(out, vecBase+rvFArg0)
	} else {
		g.emit("mv", rvReg(out), rvReg(rvArg0))
	}
	return out, nil
}

// ---- results and tail calls -------------------------------------------------

func (g *rvGenerator) resultExpr(expr ast.Expression) error {
	switch e := expr.(type) {
	case *ast.InvocationExpression:
		if g.isTailCall(e) {
			return g.tailCall(e)
		}
	case *ast.MatchExpression:
		if g.result != nil && !g.result.isFloat && g.valueOnly(e) {
			// Every arm yields a value: they meet in one scratch register
			// and a0 is written once, at the join — a result written inside
			// an arm would forget the parameters' span and record facts for
			// the arms after it in the linear checker.
			out, err := g.alloc(*g.result)
			if err != nil {
				return err
			}
			g.emit("mv", rvReg(out), rvReg(0)) // defined before the arms (generator.resultExpr)
			if err := g.resultInto(e, out); err != nil {
				return err
			}
			g.moveResult(out)
			g.release(out)
			return nil
		}
		whenTrue, whenFalse, isBool := boolConditional(e)
		if !isBool {
			return g.lowerMatch(e, g.resultExpr)
		}
		// With one arm a tail self-call, the loop shape the verifier
		// recognizes: the exit branch leaves for the value arm, the tail
		// arm falls through to the back edge.
		if g.isTailCall(whenFalse) != g.isTailCall(whenTrue) {
			tail, value, jumpIfFalse := whenTrue, whenFalse, true
			if g.isTailCall(whenFalse) {
				tail, value, jumpIfFalse = whenFalse, whenTrue, false
			}
			exit := g.newLabel("exit")
			if err := g.conditionBranch(e.Scrutinee, exit, jumpIfFalse); err != nil {
				return err
			}
			if err := g.resultExpr(tail); err != nil {
				return err
			}
			g.label(exit)
			return g.resultExpr(value)
		}
		elseLabel, end := g.newLabel("else"), g.newLabel("endif")
		if err := g.condition(e.Scrutinee, elseLabel); err != nil {
			return err
		}
		if err := g.resultExpr(whenTrue); err != nil {
			return err
		}
		g.jump(end)
		g.label(elseLabel)
		if err := g.resultExpr(whenFalse); err != nil {
			return err
		}
		g.label(end)
		return nil
	case *ast.BlockExpression:
		if e.Block != nil && len(e.Block.Statements) > 0 {
			g.pushScope()
			defer g.popScope()
			stmts := e.Block.Statements
			if err := g.lowerStatements(stmts[:len(stmts)-1], false); err != nil {
				return err
			}
			if es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement); ok && !es.Discard {
				return g.resultExpr(es.Expression)
			}
		}
	}
	r, err := g.exprAs(expr, *g.result)
	if err != nil {
		return err
	}
	g.moveResult(r)
	g.release(r)
	return nil
}

// tailCall lowers a self-call in result position as a loop: every argument
// is evaluated before any parameter home changes.
func (g *rvGenerator) tailCall(e *ast.InvocationExpression) error {
	if len(e.Arguments) != len(g.fn.Parameters) {
		return unsupported("a self-call with %d arguments", len(e.Arguments))
	}
	var values []int
	for i, arg := range e.Arguments {
		typ, _ := scalarOf(g.fn.Parameters[i].Type)
		r, err := g.exprAs(arg, typ)
		if err != nil {
			return err
		}
		values = append(values, r)
	}
	for i, r := range values {
		g.put(g.storeVar(g.fn.Parameters[i].Name.Value, r))
		g.release(r)
	}
	g.jump(g.head)
	return nil
}

// isTailCall recognizes a self-call the loop lowering handles.
// valueOnly is the AArch64 lane's rule (generator.valueOnly) with this
// lane's tail-call test.
func (g *rvGenerator) valueOnly(expr ast.Expression) bool {
	switch e := expr.(type) {
	case *ast.MatchExpression:
		for _, arm := range e.Arms {
			if arm == nil || arm.Body == nil || !g.valueOnly(arm.Body) {
				return false
			}
		}
		return true
	case *ast.BlockExpression:
		if e.Block == nil || len(e.Block.Statements) == 0 {
			return false
		}
		last, ok := e.Block.Statements[len(e.Block.Statements)-1].(*ast.ExpressionStatement)
		return ok && !last.Discard && g.valueOnly(last.Expression)
	case *ast.InvocationExpression:
		if g.isTailCall(e) {
			return false
		}
		if ident, ok := e.Function.(*ast.Identifier); ok {
			if callee := g.functions[ident.Value]; callee != nil && callee.ReturnType != nil && callee.ReturnType.String() == "never" {
				return false
			}
		}
	}
	return true
}

// resultInto lowers a value-only result expression into the register out
// (generator.resultInto for this lane).
func (g *rvGenerator) resultInto(expr ast.Expression, out int) error {
	switch e := expr.(type) {
	case *ast.MatchExpression:
		if whenTrue, whenFalse, ok := boolConditional(e); ok {
			elseLabel, end := g.newLabel("else"), g.newLabel("endif")
			if err := g.condition(e.Scrutinee, elseLabel); err != nil {
				return err
			}
			if err := g.resultInto(whenTrue, out); err != nil {
				return err
			}
			g.jump(end)
			g.label(elseLabel)
			if err := g.resultInto(whenFalse, out); err != nil {
				return err
			}
			g.label(end)
			return nil
		}
		return g.lowerMatch(e, func(body ast.Expression) error { return g.resultInto(body, out) })
	case *ast.BlockExpression:
		if e.Block != nil && len(e.Block.Statements) > 0 {
			g.pushScope()
			defer g.popScope()
			stmts := e.Block.Statements
			if err := g.lowerStatements(stmts[:len(stmts)-1], false); err != nil {
				return err
			}
			if es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement); ok && !es.Discard {
				return g.resultInto(es.Expression, out)
			}
		}
	}
	r, err := g.exprAs(expr, *g.result)
	if err != nil {
		return err
	}
	if r != out {
		g.move(out, r)
		g.release(r)
	}
	return nil
}

func (g *rvGenerator) isTailCall(expr ast.Expression) bool {
	call, ok := expr.(*ast.InvocationExpression)
	if !ok || len(g.spans) != 0 {
		return false
	}
	ident, ok := call.Function.(*ast.Identifier)
	return ok && ident.Value == g.fn.Name.Value
}

// ---- spans ------------------------------------------------------------------

// rvLoadOf is the whole-element load of a type, extending as the element
// reads in C: the signed and 32-bit loads sign-extend (a canonical i32 or
// u32), lhu/lbu zero-extend.
func rvLoadOf(s scalar) string {
	switch {
	case s.isFloat && s.bits == 64:
		return "fld"
	case s.isFloat:
		return "flw"
	case s.bits == 64:
		return "ld"
	case s.bits == 32:
		return "lw"
	case s.bits == 16 && s.signed:
		return "lh"
	case s.bits == 16:
		return "lhu"
	case s.signed:
		return "lb"
	default:
		return "lbu"
	}
}

// rvGlobalAddress materializes a global's address with `la` (auipc then
// addi, the pc-relative pair the linker fills) in a fresh scratch register
// and records the global as one the body addresses
// (docs/spec/94-assembler.md §9).
func (g *rvGenerator) rvGlobalAddress(name string, global asm.Global) (int, error) {
	addr, err := g.alloc(scalars["u64"])
	if err != nil {
		return 0, err
	}
	g.emit("la", rvReg(addr), asm.Symbol{Name: name})
	g.usedGlobals[name] = global
	return addr, nil
}

// rvGlobalLoad reads a global's cell into r at its storage width: a Bool
// is the C backend's 4-byte cell.
func (g *rvGenerator) rvGlobalLoad(name string, global asm.Global, r int) error {
	addr, err := g.rvGlobalAddress(name, global)
	if err != nil {
		return err
	}
	load := rvLoadOf(scalars[global.Type])
	if global.Type == "Bool" {
		load = "lw"
	}
	g.emit(load, rvReg(r), asm.Memory{Base: rvReg(addr)})
	g.release(addr)
	return nil
}

// rvGlobalStore writes r into a global's cell at its storage width.
func (g *rvGenerator) rvGlobalStore(name string, global asm.Global, r int) error {
	addr, err := g.rvGlobalAddress(name, global)
	if err != nil {
		return err
	}
	store := rvStoreOf(scalars[global.Type])
	if global.Type == "Bool" {
		store = "sw"
	}
	g.emit(store, rvReg(r), asm.Memory{Base: rvReg(addr)})
	g.release(addr)
	return nil
}

// rvStoreOf is the whole-element store of a type.
func rvStoreOf(s scalar) string {
	if s.isFloat {
		return pick(s.bits == 64, "fsd", "fsw")
	}
	switch s.bits {
	case 64:
		return "sd"
	case 32:
		return "sw"
	case 16:
		return "sh"
	default:
		return "sb"
	}
}

// guardedAddress evaluates an element index and emits the checker's idiom
// (docs/spec/94-assembler.md §9), returning the register that holds the
// element's address: the index zero-extended (a canonical u32 is
// sign-extended; the guard compares 64-bit values), `bgeu idx, norm, trap`
// so an index at or past the length traps as the C backend's oak_index
// does, `slli` by the element size's log, then `add` to the bound base —
// the fall-through path carries the facts the checker admits the access
// under.
func (g *rvGenerator) guardedAddress(sp span, index ast.Expression) (int, error) {
	idxType, err := g.typeOf(index, nil)
	if err != nil {
		return 0, err
	}
	if idxType.isBool || idxType.isFloat || (idxType.signed && idxType.bits != 32) {
		return 0, unsupported("an element index of type %s (indices are unsigned or i32)", idxType.name)
	}
	r, err := g.expr(index, &idxType)
	if err != nil {
		return 0, err
	}
	R := rvReg(r)
	if idxType.bits < 64 && !idxType.signed {
		g.emit("slli", R, R, imm(32))
		g.emit("srli", R, R, imm(32))
	}
	// An i32 index stays in its canonical sign-extended form: a negative
	// index is a huge unsigned value the guard traps, as the C backend's
	// `(u64)(i)` cast does; a non-negative one is its own zero-extension.
	g.usedTrap = true
	g.emit("bgeu", R, rvReg(sp.norm), asm.Symbol{Name: g.trap})
	if shift := log2Bytes(sp.elem.bits / 8); shift > 0 {
		g.emit("slli", R, R, imm(int64(shift)))
	}
	g.emit("add", R, rvReg(sp.baseReg), R)
	return r, nil
}

// element lowers `v[i]`: a guarded, whole-element load through the bound
// base. The element lands in the address register: the index is spent.
func (g *rvGenerator) element(e *ast.IndexExpression) (int, error) {
	if e.Dot {
		p, err := g.placeOf(e)
		if err != nil {
			return 0, err
		}
		if p.sc == nil {
			return 0, unsupported("%s is not a scalar field", e.String())
		}
		return g.fieldLoad(p.sc)
	}
	arr, err := g.arrayOperand(e.Left)
	if err != nil {
		return 0, err
	}
	if arr == nil {
		// A local view of an owned array: the array's own element idiom.
		if sp, err := g.spanOperand(e.Left); err == nil && sp.array != nil && sp.elemLayout == nil {
			arr = sp.array
		}
	}
	if arr != nil {
		address, tmp, err := g.arrayAddress(arr, e.Index)
		if err != nil {
			return 0, err
		}
		dst := tmp
		if dst < 0 || arr.elem.isFloat {
			if dst, err = g.alloc(arr.elem); err != nil {
				return 0, err
			}
		}
		g.emit(rvLoadOf(arr.elem), rvReg(dst), address)
		if tmp >= 0 && tmp != dst {
			g.release(tmp)
		}
		return dst, nil
	}
	sp, err := g.spanOperand(e.Left)
	if err != nil {
		return 0, err
	}
	r, err := g.guardedAddress(sp, e.Index)
	if err != nil {
		return 0, err
	}
	address := asm.Memory{Base: rvReg(r), Offset: 0, Mode: asm.MemOffset}
	if sp.elem.isFloat {
		f, err := g.alloc(sp.elem)
		if err != nil {
			return 0, err
		}
		g.emit(rvLoadOf(sp.elem), rvReg(f), address)
		g.release(r)
		return f, nil
	}
	g.emit(rvLoadOf(sp.elem), rvReg(r), address)
	return r, nil
}

// elementStore lowers `v[i] = e` through a writable span: the value first,
// placeStore lowers `p.f = e` and `pool[i].f = e`. When the value calls,
// it is evaluated before the place: an element address computed first
// would be held across the call, spilled and reloaded, and the checker
// cannot carry a region through a spill (docs/spec/94-assembler.md §9).
// The place is computed once to learn its type — that computation is
// rolled back — then again after the value.
func (g *rvGenerator) placeStore(s *ast.IndexAssignmentStatement) error {
	if !mentionsCall(s.Value) {
		target, err := g.placeOf(s.Target)
		if err != nil {
			return err
		}
		return g.storeToPlace(target, s)
	}
	mark := len(g.items)
	probe, err := g.placeOf(s.Target)
	if err != nil {
		return err
	}
	g.items = g.items[:mark]
	switch {
	case probe.sc != nil:
		g.releaseTemps(probe.sc.temps)
		if probe.sc.readOnly {
			return unsupported("a store into %s through a read-only view", s.Target.String())
		}
		typ := probe.sc.typ
		value, err := g.exprAs(s.Value, typ)
		if err != nil {
			return err
		}
		target, err := g.placeOf(s.Target)
		if err != nil {
			return err
		}
		if target.sc == nil {
			return unsupported("the place %s changed shape", s.Target.String())
		}
		if err := g.fieldStore(target.sc, value); err != nil {
			return err
		}
		g.release(value)
		g.releaseTemps(target.sc.temps)
		return nil
	case probe.rec != nil:
		g.releaseTemps(probe.rec.temps)
		if probe.rec.readOnly {
			return unsupported("a store into %s through a read-only view", s.Target.String())
		}
		layout := probe.rec.layout
		src, err := g.recordValueAs(s.Value, layout)
		if err != nil {
			return err
		}
		if src.layout != layout {
			return unsupported("a %s stored into %s (a %s)", src.layout.name, s.Target.String(), layout.name)
		}
		target, err := g.placeOf(s.Target)
		if err != nil {
			return err
		}
		if target.rec == nil {
			return unsupported("the place %s changed shape", s.Target.String())
		}
		err = g.copyBytes(target.rec.loc(), src.loc(), layout.size)
		g.releaseTemps(src.temps)
		g.releaseTemps(target.rec.temps)
		return err
	}
	target, err := g.placeOf(s.Target)
	if err != nil {
		return err
	}
	return g.storeToPlace(target, s)
}

// then the guarded address, then the store at the element's width.
func (g *rvGenerator) elementStore(s *ast.IndexAssignmentStatement) error {
	if s.Target.Dot {
		return g.placeStore(s)
	}
	arr, err := g.arrayOperand(s.Target.Left)
	if err != nil {
		return err
	}
	if arr == nil {
		if sp, err := g.spanOperand(s.Target.Left); err == nil && sp.array != nil && sp.elemLayout == nil && sp.writable {
			arr = sp.array
		}
	}
	if arr != nil {
		if arr.readOnly {
			return unsupported("a store into %s through a view", s.Target.Left.String())
		}
		value, err := g.exprAs(s.Value, arr.elem)
		if err != nil {
			return err
		}
		address, tmp, err := g.arrayAddress(arr, s.Target.Index)
		if err != nil {
			return err
		}
		g.emit(rvStoreOf(arr.elem), rvReg(value), address)
		if tmp >= 0 {
			g.release(tmp)
		}
		g.release(value)
		return nil
	}
	sp, err := g.spanOperand(s.Target.Left)
	if err != nil {
		return err
	}
	if !sp.writable {
		return unsupported("a store through the view %s", s.Target.Left.String())
	}
	value, err := g.exprAs(s.Value, sp.elem)
	if err != nil {
		return err
	}
	r, err := g.guardedAddress(sp, s.Target.Index)
	if err != nil {
		return err
	}
	g.emit(rvStoreOf(sp.elem), rvReg(value), asm.Memory{Base: rvReg(r), Offset: 0, Mode: asm.MemOffset})
	g.release(r)
	g.release(value)
	return nil
}

// ---- owned arrays in the frame ----------------------------------------------

// lowerArrayDeclaration lowers `buf: [N]T` (zero-filled through the zero
// register, as the C backend leaves no storage uninitialized) or
// `buf: [N]T = [e0, …]` (each element stored at its slot, the name bound
// after every element is evaluated).
func (g *rvGenerator) lowerArrayDeclaration(s *ast.VariableDeclaration, elem scalar, length int64) error {
	if elem.isFloat {
		g.usedFloat = true
	}
	size := int64(elem.bits / 8)
	if s.Value == nil {
		arr := g.declareArray(s.Name.Value, elem, length)
		words := (length*size + 7) / 8
		for w := int64(0); w < words; w++ {
			g.emit("sd", rvReg(rvZero), g.slotMem(arr.offset+8*w))
		}
		return nil
	}
	literal, isLiteral := s.Value.(*ast.ArrayLiteral)
	if !isLiteral {
		return unsupported("an array local initialized from %s", s.Value.String())
	}
	if int64(len(literal.Elements)) != length {
		return unsupported("an array literal of %d elements for [%d]%s", len(literal.Elements), length, elem.name)
	}
	arr := g.allocArray(elem, length)
	for k, e := range literal.Elements {
		r, err := g.exprAs(e, elem)
		if err != nil {
			return err
		}
		g.emit(rvStoreOf(elem), rvReg(r), g.slotMem(arr.offset+int64(k)*size))
		g.release(r)
	}
	g.bindArray(s.Name.Value, arr)
	return nil
}

// arrayAddress lowers `buf[i]` to a memory operand: a literal index inside
// the array addresses its slot through sp directly; any other index goes
// through the array's frame address under the constant guard the checker
// admits (docs/spec/94-assembler.md §9) — `addi b, sp, off; li k, N; bgeu
// idx, k, trap; slli idx, idx, s; add idx, b, idx` — so an index at or past
// N traps as the C backend's guard does. The returned register (or -1)
// holds the address and is the caller's to spend or release.
func (g *rvGenerator) arrayAddress(arr *arrayLocal, index ast.Expression) (asm.Memory, int, error) {
	size := arr.elemSize()
	if k, isConst := constantValue(index); isConst && k >= 0 && k < arr.length {
		if arr.inReg {
			return asm.Memory{Base: rvReg(arr.reg), Offset: arr.offset + k*size, Mode: asm.MemOffset}, -1, nil
		}
		return g.slotMem(arr.offset + k*size), -1, nil
	}
	idxType, err := g.typeOf(index, nil)
	if err != nil {
		return asm.Memory{}, 0, err
	}
	if idxType.isBool || idxType.isFloat || (idxType.signed && idxType.bits != 32) {
		return asm.Memory{}, 0, unsupported("an element index of type %s (indices are unsigned or i32)", idxType.name)
	}
	r, err := g.expr(index, &idxType)
	if err != nil {
		return asm.Memory{}, 0, err
	}
	R := rvReg(r)
	if idxType.bits < 64 && !idxType.signed {
		g.emit("slli", R, R, imm(32))
		g.emit("srli", R, R, imm(32))
	}
	base := arr.reg
	if !arr.inReg {
		if base, err = g.alloc(scalars["u64"]); err != nil {
			return asm.Memory{}, 0, err
		}
		g.emit("addi", rvReg(base), rvSP(), imm(g.slotMem(arr.offset).Offset))
	} else if arr.offset != 0 {
		return asm.Memory{}, 0, unsupported("an array at offset %d inside a register-addressed place", arr.offset)
	}
	bound, err := g.alloc(scalars["u64"])
	if err != nil {
		return asm.Memory{}, 0, err
	}
	g.usedTrap = true
	g.emit("li", rvReg(bound), imm(arr.length))
	g.emit("bgeu", R, rvReg(bound), asm.Symbol{Name: g.trap})
	g.release(bound)
	if shift := log2Bytes(int(size)); shift > 0 {
		g.emit("slli", R, R, imm(int64(shift)))
	}
	g.emit("add", R, rvReg(base), R)
	if !arr.inReg {
		g.release(base)
	}
	return asm.Memory{Base: R, Offset: 0, Mode: asm.MemOffset}, r, nil
}

// arraySpanArgument lowers `view(&buf)` / `span(&buf)` as a call argument
// for a span-typed parameter: the array's frame address and its constant
// length in two scratch registers (a `[*]T` parameter takes only `span`).
func (g *rvGenerator) arraySpanArgument(callee string, arg ast.Expression, target span) (int, int, error) {
	call, isCall := arg.(*ast.InvocationExpression)
	if !isCall {
		return 0, 0, unsupported("a call to %s: a span argument %s (only view(&buf) or span(&buf) over an owned array)", callee, arg.String())
	}
	fn, isIdent := call.Function.(*ast.Identifier)
	if !isIdent || (fn.Value != "view" && fn.Value != "span") || len(call.Arguments) != 1 {
		return 0, 0, unsupported("a call to %s: a span argument %s (only view(&buf) or span(&buf) over an owned array)", callee, arg.String())
	}
	if target.writable && fn.Value != "span" {
		return 0, 0, unsupported("a call to %s: a view where a span is expected", callee)
	}
	borrow, isBorrow := call.Arguments[0].(*ast.PrefixExpression)
	if !isBorrow || borrow.Operator != "&" {
		return 0, 0, unsupported("a call to %s: %s of %s (only &buf over an owned array)", callee, fn.Value, call.Arguments[0].String())
	}
	arr, err := g.arrayOperand(borrow.Right)
	if err != nil {
		return 0, 0, err
	}
	if arr == nil {
		return 0, 0, unsupported("a call to %s: %s of %s (only an owned array)", callee, fn.Value, borrow.Right.String())
	}
	if arr.elemLayout != nil || arr.elem != target.elem {
		return 0, 0, unsupported("a call to %s: %s over %s where the span type's elements are expected", callee, fn.Value, borrow.Right.String())
	}
	base, err := g.alloc(scalars["u64"])
	if err != nil {
		return 0, 0, err
	}
	if arr.inReg {
		if target.writable {
			return 0, 0, unsupported("a call to %s: span of the constant table %s (read-only)", callee, borrow.Right.String())
		}
		g.emit("mv", rvReg(base), rvReg(arr.reg))
		g.releaseTemps(arr.temps)
	} else {
		g.emit("addi", rvReg(base), rvSP(), imm(g.slotMem(arr.offset).Offset))
	}
	length, err := g.alloc(scalars["u32"])
	if err != nil {
		return 0, 0, err
	}
	if err := g.constant(length, uint64(arr.length), scalars["u32"]); err != nil {
		return 0, 0, err
	}
	return base, length, nil
}

// ---- floating point -----------------------------------------------------------

// floatConstant materializes a float: its IEEE bit pattern through an
// integer scratch register and fmv (exact for every value; an f32 pattern
// travels as the sign-extended low word, which fmv.w.x NaN-boxes).
func (g *rvGenerator) floatConstant(r int, value float64, s scalar) error {
	g.usedFloat = true
	bits := scalars["u64"]
	pattern := math.Float64bits(value)
	if !s.wide() {
		bits = scalars["u32"]
		pattern = uint64(math.Float32bits(float32(value)))
	}
	t, err := g.alloc(bits)
	if err != nil {
		return err
	}
	if err := g.constant(t, pattern, bits); err != nil {
		return err
	}
	g.emit(pick(s.wide(), "fmv.d.x", "fmv.w.x"), rvReg(r), rvReg(t))
	g.release(t)
	return nil
}

// floatCompare lowers an IEEE comparison to a Bool in an integer register:
// feq/flt/fle are quiet comparisons yielding 0 on unordered operands, so
// `!=` is the complement of feq and `>`/`>=` swap the operands — exactly
// how C reads the comparison (NaN is unequal, neither below nor above).
func (g *rvGenerator) floatCompare(operator string, l, r int, typ scalar) (int, error) {
	out, err := g.alloc(scalars["Bool"])
	if err != nil {
		return 0, err
	}
	O, L, R := rvReg(out), rvReg(l), rvReg(r)
	suffix := fsuffix(typ)
	switch operator {
	case "==":
		g.emit("feq"+suffix, O, L, R)
	case "!=":
		g.emit("feq"+suffix, O, L, R)
		g.emit("xori", O, O, imm(1))
	case "<":
		g.emit("flt"+suffix, O, L, R)
	case "<=":
		g.emit("fle"+suffix, O, L, R)
	case ">":
		g.emit("flt"+suffix, O, R, L)
	case ">=":
		g.emit("fle"+suffix, O, R, L)
	}
	g.release(l)
	g.release(r)
	return out, nil
}

// rvFloatIntrinsics are the correctly rounded intrinsics that are one F/D
// instruction each: fmin/fmax are the number-selecting minimum and maximum
// (a NaN operand yields the other, IEEE 754-2008 minNum/maxNum), fma is
// fmadd (nothing else is ever contracted). floor/ceil/trunc/round and the
// NaN-propagating min/max have no single instruction and stay with C.
var rvFloatIntrinsics = map[string]string{"sqrt": "fsqrt", "abs": "fsgnjx", "min_num": "fmin", "max_num": "fmax", "fma": "fmadd"}

// intrinsic lowers a float intrinsic at the call's recorded width
// (narrower operands widen exactly first).
func (g *rvGenerator) intrinsic(e *ast.InvocationExpression, typ scalar) (int, error) {
	ident, isIdent := e.Function.(*ast.Identifier)
	if !isIdent {
		return 0, unsupported("a call through a value")
	}
	op, ok := rvFloatIntrinsics[ident.Value]
	if !ok {
		return 0, unsupported("the intrinsic %s (no single F/D instruction)", ident.Value)
	}
	g.usedFloat = true
	var regs []int
	for _, arg := range e.Arguments {
		argType, err := g.typeOf(arg, &typ)
		if err != nil {
			return 0, err
		}
		r, err := g.expr(arg, &argType)
		if err != nil {
			return 0, err
		}
		if !argType.isFloat {
			return 0, unsupported("a non-float operand of %s", ident.Value)
		}
		if argType.bits != typ.bits {
			g.emit("fcvt"+fsuffix(typ)+fsuffix(argType), rvReg(r), rvReg(r))
		}
		regs = append(regs, r)
	}
	suffix := fsuffix(typ)
	R := func(i int) asm.Register { return rvReg(regs[i]) }
	switch {
	case len(regs) == 1 && op == "fsgnjx":
		g.emit(op+suffix, R(0), R(0), R(0))
	case len(regs) == 1:
		g.emit(op+suffix, R(0), R(0))
	case len(regs) == 2:
		g.emit(op+suffix, R(0), R(0), R(1))
		g.release(regs[1])
	case len(regs) == 3:
		// fma(a, b, c) = a*b + c: fmadd d, a, b, c.
		g.emit(op+suffix, R(0), R(0), R(1), R(2))
		g.release(regs[1])
		g.release(regs[2])
	default:
		return 0, unsupported("the intrinsic %s with %d operands", ident.Value, len(regs))
	}
	return regs[0], nil
}

// rvCvtInt spells an integer type as fcvt's integer operand: w/wu for the
// 32-bit and narrower types (a narrow value is canonical: fits), l/lu for
// the 64-bit ones.
func rvCvtInt(s scalar) string {
	switch {
	case s.bits == 64 && s.signed:
		return "l"
	case s.bits == 64:
		return "lu"
	case s.signed:
		return "w"
	default:
		return "wu"
	}
}

// convertFloat lowers the conversions with a float on either side
// (docs/spec/20-types.md §11.3.4): widening and `round` between the
// precisions through fcvt; integer to float through fcvt.d.w and its kin;
// `bits` through fmv; `saturating` float to integer through fcvt with rtz
// (which saturates at the register's range) with NaN sent to 0 as the C
// helper does — the ISA converts NaN to the largest positive value, so the
// result is multiplied by the `feq x, x` bit — and a narrower target
// clamped to its own range; `trunc` float to integer with the C backend's
// range check first: NaN or a value outside the target's open interval
// traps.
func (g *rvGenerator) convertFloat(r int, source, target scalar, op string) (int, error) {
	g.usedFloat = true
	switch {
	case source.isFloat && target.isFloat:
		if source.bits == target.bits {
			return r, nil
		}
		g.emit("fcvt"+fsuffix(target)+fsuffix(source), rvReg(r), rvReg(r))
		return r, nil
	case !source.isFloat && target.isFloat:
		f, err := g.alloc(target)
		if err != nil {
			return 0, err
		}
		if op == "bits" {
			g.emit(pick(target.wide(), "fmv.d.x", "fmv.w.x"), rvReg(f), rvReg(r))
		} else {
			g.emit("fcvt"+fsuffix(target)+"."+rvCvtInt(source), rvReg(f), rvReg(r))
		}
		g.release(r)
		return f, nil
	}
	// Float to integer.
	out, err := g.alloc(target)
	if err != nil {
		return 0, err
	}
	rtz := asm.Option{Name: "rtz"}
	switch op {
	case "bits":
		// fmv.x.w sign-extends the 32-bit pattern: a canonical u32.
		g.emit(pick(source.wide(), "fmv.x.d", "fmv.x.w"), rvReg(out), rvReg(r))
	case "saturating":
		g.emit("fcvt."+rvCvtInt(target)+fsuffix(source), rvReg(out), rvReg(r), rtz)
		ordered, err := g.alloc(scalars["Bool"])
		if err != nil {
			return 0, err
		}
		g.emit("feq"+fsuffix(source), rvReg(ordered), rvReg(r), rvReg(r))
		g.emit("mul", rvReg(out), rvReg(out), rvReg(ordered))
		g.release(ordered)
		if target.bits < 32 {
			if err := g.clampNarrow(out, target); err != nil {
				return 0, err
			}
		}
		g.normalize(out, target)
	case "trunc":
		low, lowInclusive, high := floatIntegerBounds(target)
		bound, err := g.alloc(source)
		if err != nil {
			return 0, err
		}
		test, err := g.alloc(scalars["Bool"])
		if err != nil {
			return 0, err
		}
		g.usedTrap = true
		// NaN traps: it is unordered with itself.
		g.emit("feq"+fsuffix(source), rvReg(test), rvReg(r), rvReg(r))
		g.emit("beqz", rvReg(test), asm.Symbol{Name: g.trap})
		if err := g.floatConstant(bound, low, source); err != nil {
			return 0, err
		}
		if lowInclusive {
			g.emit("flt"+fsuffix(source), rvReg(test), rvReg(r), rvReg(bound)) // x < low
		} else {
			g.emit("fle"+fsuffix(source), rvReg(test), rvReg(r), rvReg(bound)) // x <= low
		}
		g.emit("bnez", rvReg(test), asm.Symbol{Name: g.trap})
		if err := g.floatConstant(bound, high, source); err != nil {
			return 0, err
		}
		g.emit("fle"+fsuffix(source), rvReg(test), rvReg(bound), rvReg(r)) // x >= high
		g.emit("bnez", rvReg(test), asm.Symbol{Name: g.trap})
		g.release(test)
		g.release(bound)
		g.emit("fcvt."+rvCvtInt(target)+fsuffix(source), rvReg(out), rvReg(r), rtz)
		g.normalize(out, target)
	default:
		return 0, unsupported("a %s conversion from %s to %s", op, source.name, target.name)
	}
	g.release(r)
	return out, nil
}

// clampNarrow clamps a saturated 32-bit conversion result into a narrow
// integer type's range with compare-and-branch selects, what fcvt.w/wu
// cannot do for u8/u16 and i8/i16.
func (g *rvGenerator) clampNarrow(r int, target scalar) error {
	word := scalars["u32"]
	if target.signed {
		word = scalars["i32"]
	}
	t, err := g.alloc(word)
	if err != nil {
		return err
	}
	var max, min int64
	if target.signed {
		max, min = int64(1)<<uint(target.bits-1)-1, -(int64(1) << uint(target.bits-1))
	} else {
		max = int64(1)<<uint(target.bits) - 1
	}
	R, T := rvReg(r), rvReg(t)
	// r = r > max ? max | r
	high := g.newLabel("clamp")
	if err := g.constant(t, uint64(max), word); err != nil {
		return err
	}
	g.emit(pick(target.signed, "bge", "bgeu"), T, R, asm.Symbol{Name: high})
	g.emit("mv", R, T)
	g.label(high)
	if target.signed {
		low := g.newLabel("clamp")
		if err := g.constant(t, uint64(min), word); err != nil {
			return err
		}
		g.emit("bge", R, T, asm.Symbol{Name: low})
		g.emit("mv", R, T)
		g.label(low)
	}
	g.release(t)
	return nil
}

// ---- record locals ------------------------------------------------------------

// placeOf resolves an access chain to its place in the frame (the shared
// resolver, docs/spec/94-assembler.md §9); a chain through a call's result
// is outside this lane's subset (records do not cross calls here yet).
// arrayOperand resolves the array an expression names through the RV64
// lane's placeOf (a constant table's address is taken with `la`).
func (g *rvGenerator) arrayOperand(expr ast.Expression) (*arrayLocal, error) {
	p, err := g.placeOf(expr)
	if err != nil {
		return nil, err
	}
	return p.arr, nil
}

func (g *rvGenerator) placeOf(expr ast.Expression) (place, error) {
	switch e := expr.(type) {
	case *ast.Identifier:
		if rec, isRecord := g.records[e.Value]; isRecord {
			return place{rec: rec}, nil
		}
		if arr, isArray := g.arrays[e.Value]; isArray {
			return place{arr: arr}, nil
		}
		if gl, isTable := g.tables[e.Value]; isTable {
			// A constant table: its address in a scratch register (la), a
			// read-only array at offset 0 from it.
			r, err := g.alloc(scalars["u64"])
			if err != nil {
				return place{}, err
			}
			g.emit("la", rvReg(r), asm.Symbol{Name: gl.Symbol})
			return place{arr: &arrayLocal{elem: scalars[gl.Elem], length: gl.Length, inReg: true, reg: r, temps: []int{r}, readOnly: true}}, nil
		}
	case *ast.IndexExpression:
		if !e.Dot {
			base, err := g.placeOf(e.Left)
			if err != nil {
				return place{}, err
			}
			if base.arr == nil || base.arr.elemLayout == nil {
				return place{}, nil
			}
			return place{}, unsupported("an element of an array of records (%s)", e.String())
		}
		base, err := g.placeOf(e.Left)
		if err != nil {
			return place{}, err
		}
		if base.rec == nil {
			call, isCall := e.Left.(*ast.InvocationExpression)
			if !isCall {
				return place{}, unsupported("a field access on %s (not a record)", e.Left.String())
			}
			// A field of a call's record result: the call lands in a temp.
			rec, err := g.callRecord(call)
			if err != nil {
				return place{}, err
			}
			base = place{rec: rec}
		}
		name, isName := e.Index.(*ast.Identifier)
		if !isName {
			return place{}, unsupported("a field access %s", e.String())
		}
		field, has := base.rec.layout.fields[name.Value]
		if !has {
			return place{}, unsupported("the field %s of %s", name.Value, base.rec.layout.name)
		}
		at := base.rec.loc().plus(field.offset)
		switch field.kind {
		case fieldScalar:
			return place{sc: &scalarPlace{offset: at.offset, typ: field.typ, inReg: at.inReg, reg: at.reg, temps: base.rec.temps}}, nil
		case fieldRecord:
			return place{rec: &recordLocal{offset: at.offset, layout: field.layout, inReg: at.inReg, reg: at.reg, temps: base.rec.temps}}, nil
		default:
			return place{arr: &arrayLocal{offset: at.offset, elem: field.typ, elemLayout: field.layout, length: field.length, inReg: at.inReg, reg: at.reg, temps: base.rec.temps}}, nil
		}
	}
	return place{}, nil
}

// fieldLoad reads a scalar field into a fresh register at its type: a Bool
// field is the 4-byte C enum holding 0 or 1, so its load is `lw`.
func (g *rvGenerator) fieldLoad(sc *scalarPlace) (int, error) {
	if sc.inReg {
		return 0, unsupported("a field through a register-addressed place")
	}
	r, err := g.alloc(sc.typ)
	if err != nil {
		return 0, err
	}
	load := rvLoadOf(sc.typ)
	if sc.typ.isBool {
		load = "lw"
	}
	g.emit(load, rvReg(r), g.memOf(sc.loc()))
	return r, nil
}

// fieldStore writes a canonical value of the field's type at its width.
func (g *rvGenerator) fieldStore(sc *scalarPlace, r int) error {
	if sc.inReg {
		return unsupported("a field through a register-addressed place")
	}
	store := rvStoreOf(sc.typ)
	if sc.typ.isBool {
		store = "sw"
	}
	g.emit(store, rvReg(r), g.memOf(sc.loc()))
	return nil
}

// copyBytes copies size bytes between two frame locations through a
// scratch register, in the widest aligned units then a narrowing tail —
// exactly the bytes of the value, never a neighbor's (the checker requires
// each frame access naturally aligned).
func (g *rvGenerator) copyBytes(dst, src loc, size int64) error {
	if dst.inReg || src.inReg {
		return unsupported("a copy through a register-addressed place")
	}
	tmp, err := g.alloc(scalars["u64"])
	if err != nil {
		return err
	}
	unit := copyUnit(g.alignmentOf(dst), g.alignmentOf(src))
	off := int64(0)
	for bytes := unit; bytes >= 1; bytes /= 2 {
		load, store := map[int64]string{8: "ld", 4: "lw", 2: "lh", 1: "lb"}[bytes], map[int64]string{8: "sd", 4: "sw", 2: "sh", 1: "sb"}[bytes]
		for off+bytes <= size {
			g.emit(load, rvReg(tmp), g.memOf(src.plus(off)))
			g.emit(store, rvReg(tmp), g.memOf(dst.plus(off)))
			off += bytes
		}
	}
	g.release(tmp)
	return nil
}

// copyRecord copies a record slot-wise (the padding travels too, as the C
// struct assignment copies it).
func (g *rvGenerator) copyRecord(dst, src *recordLocal) error {
	return g.copyBytes(dst.loc(), src.loc(), dst.layout.size)
}

// lowerRecordDeclaration lowers `p: Point = Point { x: e, … }` (every field
// stored at its offset) or `p: Point = q` (a slot-wise copy). A record
// without an initializer is left to the C backend, which leaves it
// uninitialized — no semantics are invented here.
func (g *rvGenerator) lowerRecordDeclaration(s *ast.VariableDeclaration, typeName string) error {
	layout, err := g.layoutOf(typeName)
	if err != nil {
		return err
	}
	if s.Value == nil {
		return unsupported("the record local %s without an initializer", s.Name.Value)
	}
	if literal, isLiteral := s.Value.(*ast.RecordLiteral); isLiteral {
		if literal.TypeName != nil && literal.TypeName.Value != typeName {
			return unsupported("a %s literal for the %s local %s", literal.TypeName.Value, typeName, s.Name.Value)
		}
		_, err := g.fillRecord(layout, literal, s.Name.Value)
		return err
	}
	src, err := g.recordValueAs(s.Value, layout)
	if err != nil {
		return err
	}
	if src.layout != layout {
		return unsupported("the %s local %s initialized from a %s", typeName, s.Name.Value, src.layout.name)
	}
	rec := g.declareRecord(s.Name.Value, layout)
	err = g.copyRecord(rec, src)
	g.releaseTemps(src.temps)
	return err
}

// recordValueAs lowers a record-typed expression to a record local: a
// named local (or a nested record field), or a typed literal into a fresh
// temp. Variants, record-valued matches, and calls returning records are
// the lane's later increments.
func (g *rvGenerator) recordValueAs(expr ast.Expression, expected *recordLayout) (*recordLocal, error) {
	switch e := expr.(type) {
	case *ast.VariantExpression:
		name, err := g.variantTypeName(e, expected)
		if err != nil {
			return nil, err
		}
		layout, err := g.layoutOf(name)
		if err != nil {
			return nil, err
		}
		return g.buildVariant(layout, e)
	case *ast.MatchExpression:
		// A record-valued match: every arm lands in one temp.
		layout := expected
		if layout == nil {
			var err error
			if layout, err = g.recordLayoutOfExpr(e.Arms[0].Body); err != nil {
				return nil, err
			}
		}
		out := g.tempRecord(layout)
		err := g.lowerMatch(e, func(body ast.Expression) error {
			src, err := g.recordValueAs(body, layout)
			if err != nil {
				return err
			}
			if src.layout != layout {
				return unsupported("a %s arm where %s is expected", src.layout.name, layout.name)
			}
			err = g.copyBytes(out.loc(), src.loc(), layout.size)
			g.releaseTemps(src.temps)
			return err
		})
		if err != nil {
			return nil, err
		}
		return out, nil
	case *ast.Identifier, *ast.IndexExpression:
		p, err := g.placeOf(e)
		if err != nil {
			return nil, err
		}
		if p.rec == nil {
			return nil, unsupported("%s is not a record", expr.String())
		}
		return p.rec, nil
	case *ast.RecordLiteral:
		layout := expected
		if e.TypeName != nil {
			var err error
			if layout, err = g.layoutOf(e.TypeName.Value); err != nil {
				return nil, err
			}
		}
		if layout == nil {
			return nil, unsupported("an untyped record literal")
		}
		return g.fillRecord(layout, e, "")
	case *ast.InvocationExpression:
		return g.callRecord(e)
	}
	return nil, unsupported("a record value %s", expr.String())
}

// callRecord lowers a call returning a record into a fresh temp.
func (g *rvGenerator) callRecord(e *ast.InvocationExpression) (*recordLocal, error) {
	ident, isIdent := e.Function.(*ast.Identifier)
	if !isIdent {
		return nil, unsupported("a call through a value")
	}
	callee, known := g.functions[ident.Value]
	if !known || callee.ReturnType == nil {
		return nil, unsupported("a call to %s", ident.Value)
	}
	name, isRecord := g.recordTypeName(callee.ReturnType)
	if !isRecord {
		return nil, unsupported("a call to %s in record position", ident.Value)
	}
	layout, err := g.layoutOf(name)
	if err != nil {
		return nil, err
	}
	dst := g.tempRecord(layout)
	if _, err := g.callWith(e, dst); err != nil {
		return nil, err
	}
	return dst, nil
}

// copyIn copies a record from the memory a register addresses (the
// caller's copy of a by-reference parameter) into a record local: whole
// words, then a 4/2/1-byte tail, through t0.
func (g *rvGenerator) copyIn(dst *recordLocal, base int) []asm.Item {
	var items []asm.Item
	size := dst.layout.size
	tmp := rvReg(rvScratch[0])
	off := int64(0)
	for ; off+8 <= size; off += 8 {
		items = append(items, g.ins("ld", tmp, asm.Memory{Base: rvReg(base), Offset: off, Mode: asm.MemOffset}), g.ins("sd", tmp, g.slotMem(dst.offset+off)))
	}
	for _, piece := range []struct {
		bytes       int64
		load, store string
	}{{4, "lw", "sw"}, {2, "lh", "sh"}, {1, "lb", "sb"}} {
		if off+piece.bytes <= size {
			items = append(items, g.ins(piece.load, tmp, asm.Memory{Base: rvReg(base), Offset: off, Mode: asm.MemOffset}), g.ins(piece.store, tmp, g.slotMem(dst.offset+off)))
			off += piece.bytes
		}
	}
	return items
}

// copyOut copies a record local into the memory a register addresses (the
// caller's result area), the same way.
func (g *rvGenerator) copyOut(base int, src *recordLocal) error {
	tmp, err := g.alloc(scalars["u64"])
	if err != nil {
		return err
	}
	size := src.layout.size
	unit := copyUnit(g.alignmentOf(src.loc()))
	off := int64(0)
	for bytes := unit; bytes >= 1; bytes /= 2 {
		load, store := map[int64]string{8: "ld", 4: "lw", 2: "lh", 1: "lb"}[bytes], map[int64]string{8: "sd", 4: "sw", 2: "sh", 1: "sb"}[bytes]
		for off+bytes <= size {
			g.emit(load, rvReg(tmp), g.memOf(src.loc().plus(off)))
			g.emit(store, rvReg(tmp), asm.Memory{Base: rvReg(base), Offset: off, Mode: asm.MemOffset})
			off += bytes
		}
	}
	g.release(tmp)
	return nil
}

// resultRecordExpr places a record-typed result: chunks in a0/a1, or a
// copy into the caller's result area through its parked address.
func (g *rvGenerator) resultRecordExpr(expr ast.Expression) error {
	switch e := expr.(type) {
	case *ast.MatchExpression:
		if !g.resultIndirect && g.valueOnly(e) {
			// The arms meet in one frame temporary and the chunks load into
			// a0 (and a1) once, at the join (generator.resultRecordExpr).
			var outs []int
			for c := 0; c < g.resultRecord.chunks(); c++ {
				out, err := g.alloc(scalars["u64"])
				if err != nil {
					return err
				}
				g.emit("mv", rvReg(out), rvReg(0)) // defined before the arms
				outs = append(outs, out)
			}
			if err := g.resultRecordInto(e, outs); err != nil {
				return err
			}
			for c, out := range outs {
				g.emit("mv", rvReg(rvArg0+c), rvReg(out))
				g.release(out)
			}
			return nil
		}
		whenTrue, whenFalse, isBool := boolConditional(e)
		if !isBool {
			return g.lowerMatch(e, g.resultRecordExpr)
		}
		elseLabel, end := g.newLabel("else"), g.newLabel("endif")
		if err := g.condition(e.Scrutinee, elseLabel); err != nil {
			return err
		}
		if err := g.resultRecordExpr(whenTrue); err != nil {
			return err
		}
		g.jump(end)
		g.label(elseLabel)
		if err := g.resultRecordExpr(whenFalse); err != nil {
			return err
		}
		g.label(end)
		return nil
	case *ast.BlockExpression:
		if e.Block != nil && len(e.Block.Statements) > 0 {
			g.pushScope()
			defer g.popScope()
			stmts := e.Block.Statements
			if err := g.lowerStatements(stmts[:len(stmts)-1], false); err != nil {
				return err
			}
			if es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement); ok && !es.Discard {
				return g.resultRecordExpr(es.Expression)
			}
			return unsupported("a block whose last statement is not its record result")
		}
	}
	rec, err := g.recordValueAs(expr, g.resultRecord)
	if err != nil {
		return err
	}
	if rec.layout != g.resultRecord {
		return unsupported("a %s result where %s is declared", rec.layout.name, g.resultRecord.name)
	}
	if g.resultIndirect {
		err := g.copyOut(g.resultAreaReg, rec)
		g.releaseTemps(rec.temps)
		return err
	}
	for c := 0; c < g.resultRecord.chunks(); c++ {
		g.emit("ld", rvReg(rvArg0+c), g.slotMem(rec.offset+int64(8*c)))
	}
	g.releaseTemps(rec.temps)
	return nil
}

// resultRecordInto lowers a value-only record result into the scratch
// registers outs, one per chunk (generator.resultRecordInto for this lane).
func (g *rvGenerator) resultRecordInto(expr ast.Expression, outs []int) error {
	switch e := expr.(type) {
	case *ast.MatchExpression:
		if whenTrue, whenFalse, ok := boolConditional(e); ok {
			elseLabel, end := g.newLabel("else"), g.newLabel("endif")
			if err := g.condition(e.Scrutinee, elseLabel); err != nil {
				return err
			}
			if err := g.resultRecordInto(whenTrue, outs); err != nil {
				return err
			}
			g.jump(end)
			g.label(elseLabel)
			if err := g.resultRecordInto(whenFalse, outs); err != nil {
				return err
			}
			g.label(end)
			return nil
		}
		return g.lowerMatch(e, func(body ast.Expression) error { return g.resultRecordInto(body, outs) })
	case *ast.BlockExpression:
		if e.Block != nil && len(e.Block.Statements) > 0 {
			g.pushScope()
			defer g.popScope()
			stmts := e.Block.Statements
			if err := g.lowerStatements(stmts[:len(stmts)-1], false); err != nil {
				return err
			}
			if es, ok := stmts[len(stmts)-1].(*ast.ExpressionStatement); ok && !es.Discard {
				return g.resultRecordInto(es.Expression, outs)
			}
			return unsupported("a block whose last statement is not its record result")
		}
	}
	rec, err := g.recordValueAs(expr, g.resultRecord)
	if err != nil {
		return err
	}
	if rec.layout != g.resultRecord {
		return unsupported("a %s result where %s is declared", rec.layout.name, g.resultRecord.name)
	}
	for c, out := range outs {
		g.emit("ld", rvReg(out), g.slotMem(rec.offset+int64(8*c)))
	}
	g.releaseTemps(rec.temps)
	return nil
}

// fillRecord evaluates a literal's fields (in layout order, before the
// record is bound) into a new record local named name (a temp when empty):
// scalar fields into registers, nested records and scalar arrays from
// their places or literals.
func (g *rvGenerator) fillRecord(layout *recordLayout, literal *ast.RecordLiteral, name string) (*recordLocal, error) {
	if layout.isADT() {
		return nil, unsupported("a %s literal (a tagged union)", layout.name)
	}
	if len(literal.Fields) != len(layout.order) {
		return nil, unsupported("a partial %s literal", layout.name)
	}
	type pending struct {
		reg      int
		src      *recordLocal
		arraySrc *arrayLocal
		elements *ast.ArrayLiteral
	}
	var values []pending
	for _, fieldName := range layout.order {
		expr, given := literal.Fields[fieldName]
		if !given {
			return nil, unsupported("a %s literal without the field %s", layout.name, fieldName)
		}
		field := layout.fields[fieldName]
		switch field.kind {
		case fieldScalar:
			r, err := g.exprAs(expr, field.typ)
			if err != nil {
				return nil, err
			}
			values = append(values, pending{reg: r})
		case fieldRecord:
			src, err := g.recordValueAs(expr, field.layout)
			if err != nil {
				return nil, err
			}
			if src.layout != field.layout {
				return nil, unsupported("a %s where the field %s is a %s", src.layout.name, fieldName, field.layout.name)
			}
			values = append(values, pending{src: src})
		default:
			if field.layout != nil {
				return nil, unsupported("the array-of-records field %s", fieldName)
			}
			switch value := expr.(type) {
			case *ast.ArrayLiteral:
				if int64(len(value.Elements)) != field.length {
					return nil, unsupported("an array literal of %d elements for the field %s ([%d]%s)", len(value.Elements), fieldName, field.length, field.typ.name)
				}
				values = append(values, pending{elements: value})
			default:
				p, err := g.placeOf(expr)
				if err != nil {
					return nil, err
				}
				if p.arr == nil || p.arr.elem != field.typ || p.arr.elemLayout != nil || p.arr.length != field.length {
					return nil, unsupported("the array field %s initialized from %s", fieldName, expr.String())
				}
				values = append(values, pending{arraySrc: p.arr})
			}
		}
	}
	var rec *recordLocal
	if name == "" {
		rec = g.tempRecord(layout)
	} else {
		rec = g.declareRecord(name, layout)
	}
	for i, fieldName := range layout.order {
		field := layout.fields[fieldName]
		at := rec.offset + field.offset
		switch {
		case field.kind == fieldScalar:
			if err := g.fieldStore(&scalarPlace{offset: at, typ: field.typ}, values[i].reg); err != nil {
				return nil, err
			}
			g.release(values[i].reg)
		case values[i].src != nil:
			if err := g.copyBytes(slotLoc(at), values[i].src.loc(), field.size); err != nil {
				return nil, err
			}
			g.releaseTemps(values[i].src.temps)
		case values[i].arraySrc != nil:
			if err := g.copyBytes(slotLoc(at), values[i].arraySrc.loc(), field.size); err != nil {
				return nil, err
			}
		default:
			size := int64(field.typ.bits / 8)
			for j, element := range values[i].elements.Elements {
				r, err := g.exprAs(element, field.typ)
				if err != nil {
					return nil, err
				}
				g.emit(rvStoreOf(field.typ), rvReg(r), g.slotMem(at+int64(j)*size))
				g.release(r)
			}
		}
	}
	return rec, nil
}

// storeToPlace stores into a resolved place: a scalar field at its width,
// a record (a nested field) by its exact size.
func (g *rvGenerator) storeToPlace(target place, s *ast.IndexAssignmentStatement) error {
	switch {
	case target.sc != nil:
		if target.sc.readOnly {
			return unsupported("a store into %s through a read-only view", s.Target.String())
		}
		value, err := g.exprAs(s.Value, target.sc.typ)
		if err != nil {
			return err
		}
		if err := g.fieldStore(target.sc, value); err != nil {
			return err
		}
		g.release(value)
		return nil
	case target.rec != nil:
		src, err := g.recordValueAs(s.Value, target.rec.layout)
		if err != nil {
			return err
		}
		if src.layout != target.rec.layout {
			return unsupported("a %s stored into %s (a %s)", src.layout.name, s.Target.String(), target.rec.layout.name)
		}
		err = g.copyBytes(target.rec.loc(), src.loc(), target.rec.layout.size)
		g.releaseTemps(src.temps)
		return err
	}
	return unsupported("a store to %s", s.Target.String())
}

// ---- tagged unions and match --------------------------------------------------

// buildVariant constructs `.Variant(payload)` in a fresh temp: every byte
// zero first (inactive payloads and padding are one defined value both
// realizations' readers never observe), the tag as a 32-bit store, the
// payload at its field. The payload evaluates first (it may call).
func (g *rvGenerator) buildVariant(layout *recordLayout, e *ast.VariantExpression) (*recordLocal, error) {
	if !layout.isADT() {
		return nil, unsupported("the variant %s of the record %s", e.Variant.Value, layout.name)
	}
	info, known := layout.variants[e.Variant.Value]
	if !known {
		return nil, unsupported("the variant %s of %s", e.Variant.Value, layout.name)
	}
	if (e.Payload == nil) != (info.payload == "") {
		return nil, unsupported("the variant %s.%s with the wrong payload shape", layout.name, e.Variant.Value)
	}
	payloadReg := -1
	var payloadSrc *recordLocal
	var field recordField
	if e.Payload != nil {
		field = layout.fields[info.payload]
		switch field.kind {
		case fieldScalar:
			r, err := g.exprAs(e.Payload, field.typ)
			if err != nil {
				return nil, err
			}
			payloadReg = r
		case fieldRecord:
			src, err := g.recordValueAs(e.Payload, field.layout)
			if err != nil {
				return nil, err
			}
			if src.layout != field.layout {
				return nil, unsupported("a %s payload where %s is expected", src.layout.name, field.layout.name)
			}
			payloadSrc = src
		default:
			return nil, unsupported("an array payload for %s.%s", layout.name, e.Variant.Value)
		}
	}
	rec := g.tempRecord(layout)
	for w := int64(0); w < (layout.size+7)/8; w++ {
		g.emit("sd", rvReg(rvZero), g.slotMem(rec.offset+8*w))
	}
	tag, err := g.alloc(scalars["u32"])
	if err != nil {
		return nil, err
	}
	if err := g.constant(tag, uint64(info.tag), scalars["u32"]); err != nil {
		return nil, err
	}
	g.emit("sw", rvReg(tag), g.slotMem(rec.offset))
	g.release(tag)
	switch {
	case payloadReg >= 0:
		if err := g.fieldStore(&scalarPlace{offset: rec.offset + field.offset, typ: field.typ}, payloadReg); err != nil {
			return nil, err
		}
		g.release(payloadReg)
	case payloadSrc != nil:
		if err := g.copyBytes(slotLoc(rec.offset+field.offset), payloadSrc.loc(), field.size); err != nil {
			return nil, err
		}
		g.releaseTemps(payloadSrc.temps)
	}
	return rec, nil
}

// lowerMatch lowers a general match: over a tagged union (the tag loaded
// once and compared per arm with `bne` against the variant's tag, a
// payload binding declared as a local from the payload field — a record
// payload copied, as the C backend binds a copy), or over a scalar with
// literal patterns. arm lowers one arm's body in the caller's position
// (statement, value, or result). A wildcard or bare binding ends the
// chain; without one, falling off every arm reaches the trap block (the
// checker proved exhaustiveness, so it never runs).
func (g *rvGenerator) lowerMatch(match *ast.MatchExpression, arm func(body ast.Expression) error) error {
	end := g.newLabel("match_end")
	if layout, err := g.recordLayoutOfExpr(match.Scrutinee); err == nil {
		if !layout.isADT() {
			return unsupported("a match over the record %s", layout.name)
		}
		rec, err := g.recordValueAs(match.Scrutinee, layout)
		if err != nil {
			return err
		}
		tag, err := g.alloc(scalars["u32"])
		if err != nil {
			return err
		}
		g.emit("lw", rvReg(tag), g.memOf(rec.loc()))
		closed := false
		for _, matchArm := range match.Arms {
			next := g.newLabel("arm")
			g.pushScope()
			if isWildcard(matchArm.Pattern) {
				closed = true
			}
			switch pattern := matchArm.Pattern.(type) {
			case *ast.VariantPattern:
				info, known := layout.variants[pattern.Variant.Value]
				if !known {
					g.popScope()
					return unsupported("the variant %s of %s in a pattern", pattern.Variant.Value, layout.name)
				}
				want, err := g.alloc(scalars["u32"])
				if err != nil {
					g.popScope()
					return err
				}
				if err := g.constant(want, uint64(info.tag), scalars["u32"]); err != nil {
					g.popScope()
					return err
				}
				g.emit("bne", rvReg(tag), rvReg(want), asm.Symbol{Name: next})
				g.release(want)
				if binding, isBinding := pattern.Payload.(*ast.BindingPattern); isBinding && binding.Name != nil && !isWildcard(pattern.Payload) {
					if info.payload == "" {
						g.popScope()
						return unsupported("a binding on the bare variant %s", pattern.Variant.Value)
					}
					if err := g.bindPayload(binding.Name.Value, rec, layout.fields[info.payload]); err != nil {
						g.popScope()
						return err
					}
				} else if pattern.Payload != nil && !isWildcard(pattern.Payload) {
					g.popScope()
					return unsupported("the payload pattern %s", pattern.Payload.String())
				}
			case *ast.WildcardPattern:
			case *ast.BindingPattern:
				if !closed {
					if err := g.bindWhole(pattern.Name.Value, rec); err != nil {
						g.popScope()
						return err
					}
					closed = true
				}
			default:
				g.popScope()
				return unsupported("the pattern %s over %s", matchArm.Pattern.String(), layout.name)
			}
			err := arm(matchArm.Body)
			g.popScope()
			if err != nil {
				return err
			}
			g.jump(end)
			if closed {
				break
			}
			g.label(next)
		}
		if !closed {
			g.usedTrap = true
			g.jump(g.trap)
		}
		g.label(end)
		g.release(tag)
		g.releaseTemps(rec.temps)
		return nil
	}
	// A scalar scrutinee with literal patterns.
	typ, err := g.typeOf(match.Scrutinee, nil)
	if err != nil {
		return err
	}
	if typ.isFloat {
		return unsupported("a match over a float")
	}
	value, err := g.exprAs(match.Scrutinee, typ)
	if err != nil {
		return err
	}
	closed := false
	for _, matchArm := range match.Arms {
		next := g.newLabel("arm")
		switch pattern := matchArm.Pattern.(type) {
		case *ast.LiteralPattern:
			lit, err := g.exprAs(pattern.Value, typ)
			if err != nil {
				return err
			}
			g.emit("bne", rvReg(value), rvReg(lit), asm.Symbol{Name: next})
			g.release(lit)
		default:
			if !isWildcard(matchArm.Pattern) {
				return unsupported("the pattern %s over %s", matchArm.Pattern.String(), typ.name)
			}
			closed = true
		}
		g.pushScope()
		err := arm(matchArm.Body)
		g.popScope()
		if err != nil {
			return err
		}
		g.jump(end)
		if closed {
			break
		}
		g.label(next)
	}
	if !closed {
		g.usedTrap = true
		g.jump(g.trap)
	}
	g.label(end)
	g.release(value)
	return nil
}

// bindPayload declares a match arm's payload binding: a scalar loaded into
// a variable, a record copied into a fresh local.
func (g *rvGenerator) bindPayload(name string, rec *recordLocal, field recordField) error {
	switch field.kind {
	case fieldScalar:
		at := rec.loc().plus(field.offset)
		r, err := g.fieldLoad(&scalarPlace{offset: at.offset, typ: field.typ, inReg: at.inReg, reg: at.reg})
		if err != nil {
			return err
		}
		g.declare(name, field.typ)
		g.put(g.storeVar(name, r))
		g.release(r)
		return nil
	case fieldRecord:
		local := g.declareRecord(name, field.layout)
		return g.copyBytes(local.loc(), rec.loc().plus(field.offset), field.size)
	}
	return unsupported("a binding of an array payload")
}

// bindWhole binds a match arm's name to a copy of the whole value.
func (g *rvGenerator) bindWhole(name string, rec *recordLocal) error {
	local := g.declareRecord(name, rec.layout)
	return g.copyRecord(local, rec)
}
