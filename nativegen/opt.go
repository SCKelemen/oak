package nativegen

import (
	"fmt"
	"reflect"
	"sort"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/typechecker"
)

// The native lane's side of the candidate-search optimizer
// (docs/notes/optimizer-search-2026-09.md §11, §16 Phase A item 7): the
// transforms the lane already performs, each as an opt.Transform over a
// Lane configuration with the facts it consumes; the facts of a function
// body read from the typechecker; and the structural metrics of a lowered
// body. The compiler (compiler/native_bodies.go) runs the search with a
// Driver that lowers, checks, and verifies each candidate; this file
// decides nothing about admissibility.

// Fact kinds the lane's transforms consume.
const (
	// FactIndexInExtent: an element access the typechecker proved under
	// its extent (typechecker.IndexProven; docs/spec/90-backend.md §8).
	FactIndexInExtent = "index-in-extent"
	// FactAssociative: an operator with a declared or language-given
	// associativity law (docs/spec/55-parallelism.md §4).
	FactAssociative = "associative"
)

// Transform names, as the optimization report spells them.
const (
	TransformStrength    = "strength-reduce"
	TransformElide       = "elide-guards"
	TransformReuseFlags  = "reuse-flags"
	TransformHoist       = "hoist-invariants"
	TransformUnroll      = "unroll-reductions"
	TransformVectorHomes = "vector-homes"
	TransformReallocate  = "reallocate"
)

// laneTransform is one of the lane's transforms as a toggle of the Lane
// configuration.
type laneTransform struct {
	name  string
	phase opt.Phase
	proof opt.ProofKind
	reqs  []opt.Requirement
	// arches are the lanes the transform runs on.
	arches map[string]bool
	// applied reports whether the configuration already has the transform.
	applied func(Lane) bool
	// apply turns the transform on.
	apply func(Lane) Lane
	// fired counts the sites the transform changed in a lowered body.
	fired func(*asm.Function) int
}

func (t *laneTransform) Name() string                    { return t.name }
func (t *laneTransform) Phase() opt.Phase                { return t.phase }
func (t *laneTransform) Proof() opt.ProofKind            { return t.proof }
func (t *laneTransform) Requirements() []opt.Requirement { return t.reqs }

// Apply proposes the configuration with the transform on, or nil off its
// lane or when already applied.
func (t *laneTransform) Apply(c *opt.Candidate) *opt.Candidate {
	lane, ok := c.Config.(Lane)
	if !ok || !t.arches[laneArch(lane)] || t.applied(lane) {
		return nil
	}
	return c.With(t.name, t.apply(lane))
}

// Fired counts the sites the transform changed in the candidate's body.
func (t *laneTransform) Fired(c *opt.Candidate) int {
	fn, ok := c.Body.(*asm.Function)
	if !ok || fn == nil {
		return 0
	}
	return t.fired(fn)
}

func laneArch(lane Lane) string {
	if lane.Arch == "" {
		return asm.ArchArm64
	}
	return lane.Arch
}

// elideTransform is the guard elision, refinable by source line: the
// checker's finding names the line of the access it could not admit, that
// line's accesses keep their guards, and the accesses the checker admits
// stay elided (docs/spec/94-assembler.md §9 "Check elision").
type elideTransform struct{ laneTransform }

// Refine keeps the guards of the line the finding names.
func (t *elideTransform) Refine(c *opt.Candidate, finding string) (*opt.Candidate, bool) {
	lane, ok := c.Config.(Lane)
	if !ok || !lane.ElideProven {
		return nil, false
	}
	line, hasLine := FindingLine(finding)
	if !hasLine || lane.GuardLines[line] {
		return nil, false
	}
	kept := make(map[int]bool, len(lane.GuardLines)+1)
	for l := range lane.GuardLines {
		kept[l] = true
	}
	kept[line] = true
	lane.GuardLines = kept
	return c.Reconfigured(lane), true
}

// FindingLine reads the source line a seam-checker finding names: the
// checker prefixes every finding with `function:line:` (asm/check.go
// errorf).
func FindingLine(finding string) (int, bool) {
	_, rest, hasPrefix := strings.Cut(finding, ":")
	if !hasPrefix {
		return 0, false
	}
	digits, _, hasColon := strings.Cut(rest, ":")
	if !hasColon {
		return 0, false
	}
	line, err := strconv.Atoi(strings.TrimSpace(digits))
	if err != nil || line <= 0 {
		return 0, false
	}
	return line, true
}

// GuardLinesKept lists the source lines whose guards a configuration
// keeps under elision, sorted.
func GuardLinesKept(lane Lane) []int {
	lines := make([]int, 0, len(lane.GuardLines))
	for line := range lane.GuardLines {
		lines = append(lines, line)
	}
	sort.Ints(lines)
	return lines
}

var arm64Only = map[string]bool{asm.ArchArm64: true}
var bothLanes = map[string]bool{asm.ArchArm64: true, asm.ArchRV64: true}

// Transforms are the lane's transforms in the order they compose within
// their phases.
func Transforms() []opt.Transform {
	return []opt.Transform{
		&laneTransform{
			// Strength reduction (docs/spec/90-backend.md §16, §9.ac, §9.ag):
			// in layer A, on every lane, a multiplication by a power of two
			// as a shift and an unsigned division or remainder by one as a
			// shift or a mask, each site decided at the bit level before it
			// applies (Oak.StrengthReduction states the laws); on the
			// AArch64 lane also a division by a nonzero constant without
			// its zero test, the verifier judging the body.
			name: TransformStrength, phase: opt.PhaseCanonical, proof: opt.Canonical,
			arches:  bothLanes,
			applied: func(l Lane) bool { return l.Strength },
			apply:   func(l Lane) Lane { l.Strength = true; return l },
			// Layer A's decided sites (nativegen/rewrite.go, both lanes) and
			// the AArch64 emitter's zero tests dropped.
			fired: func(fn *asm.Function) int { return StrengthReduced(fn) + Reduced(fn) },
		},
		&elideTransform{laneTransform{
			// Guard elision: an element access the typechecker proved in
			// range is lowered without its guard, and the checker admits
			// the body only from facts it reads at the seam
			// (docs/spec/94-assembler.md §9 "Check elision").
			name: TransformElide, phase: opt.PhaseMemory, proof: opt.Mechanical,
			reqs:    []opt.Requirement{opt.Require(opt.Prop(FactIndexInExtent), opt.Checked)},
			arches:  bothLanes,
			applied: func(l Lane) bool { return l.ElideProven },
			apply:   func(l Lane) Lane { l.ElideProven = true; return l },
			fired:   ElidedGuards,
		}},
		&laneTransform{
			// Compare reuse across a conditional chain (docs/spec/94-assembler.md
			// §9 "Condition selection"): the else arm reads its guard's
			// flags; the checker carries flag validity across the label.
			name: TransformReuseFlags, phase: opt.PhaseControl, proof: opt.Mechanical,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.ReuseFlags },
			apply:   func(l Lane) Lane { l.ReuseFlags = true; return l },
			fired:   ReusedCompares,
		},
		&laneTransform{
			// Loop-invariant code motion with copy propagation and guard
			// peeling (nativegen/licm.go; §9 "Loop invariants"): machine
			// shape only, judged by the checker and the verifier.
			name: TransformHoist, phase: opt.PhaseLoop, proof: opt.Mechanical,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.HoistInvariants },
			apply:   func(l Lane) Lane { l.HoistInvariants = true; return l },
			fired:   Hoisted,
		},
		&laneTransform{
			// Vector homes across calls (docs/spec/94-assembler.md §9.ad): a
			// calling function's vector locals in v16–v31, saved around a
			// call only when live after it, instead of sixteen-byte slots;
			// the checker and the verifier decide.
			name: TransformVectorHomes, phase: opt.PhaseMachine, proof: opt.Mechanical,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.VectorHomes },
			apply:   func(l Lane) Lane { l.VectorHomes = true; return l },
			fired:   func(fn *asm.Function) int { return VectorHomes(fn) + LeafVectorHomes(fn) },
		},
		&laneTransform{
			// Global register reallocation (package machine, Phase B): the
			// body's def-use webs recolored by a linear scan and its copies
			// coalesced, within the registers the lowering wrote; machine
			// shape only, judged by the checker and the verifier.
			name: TransformReallocate, phase: opt.PhaseMachine, proof: opt.Mechanical,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.Reallocate },
			apply:   func(l Lane) Lane { l.Reallocate = true; return l },
			fired:   Reallocated,
		},
		&laneTransform{
			// Reduction unrolling over four independent accumulators
			// (nativegen/reduction.go): a source rewrite licensed by the
			// operator's associativity (Oak.Reduction.unrolled4_eq); the
			// verifier judges the lowering against the rewritten body.
			name: TransformUnroll, phase: opt.PhaseLoop, proof: opt.LawLicensed,
			reqs:    []opt.Requirement{opt.Require(opt.Prop(FactAssociative), opt.ProvedKernel)},
			arches:  bothLanes,
			applied: func(l Lane) bool { return !l.NoReductions },
			apply:   func(l Lane) Lane { l.NoReductions = false; return l },
			fired:   Unrolled,
		},
	}
}

// Registry is the lane's transform registry.
func Registry() *opt.Registry {
	return opt.NewRegistry(Transforms()...)
}

// PlainLane is the identity configuration of a lane: the given lane with
// every transform off. The search turns them on one by one.
func PlainLane(lane Lane) Lane {
	lane.Strength = false
	lane.ElideProven = false
	lane.GuardLines = nil
	lane.ReuseFlags = false
	lane.HoistInvariants = false
	lane.VectorHomes = false
	lane.Reallocate = false
	lane.NoReductions = true
	return lane
}

// FunctionFacts reads the facts of a function body the lane's transforms
// consume: every bracket index the typechecker proved under its extent
// (typechecker.IndexProven, provenance checked), and the associativity of
// the integer operators the language gives the law to
// (docs/spec/55-parallelism.md §4; the reduction theorem is
// Oak.Reduction.unrolled4_eq), provenance proved-kernel. The floats have
// no such law and get no such fact.
func FunctionFacts(fn *ast.FunctionStatement, tc *typechecker.TypeChecker) *opt.Facts {
	facts := opt.NewFacts()
	if fn == nil || fn.Body == nil {
		return facts
	}
	walkNodes(fn.Body, func(node ast.Node) {
		index, ok := node.(*ast.IndexExpression)
		if !ok || index.Dot || tc == nil || !tc.IndexProven(index.Token) {
			return
		}
		facts.Add(opt.Fact{
			Proposition: opt.Prop(FactIndexInExtent, index.String()),
			Provenance:  opt.Checked,
			Source:      "typechecker/extents.go IndexProven",
			Scope:       fmt.Sprintf("line %d", index.Token.Line),
		})
	})
	for _, op := range []string{"+", "|", "&", "^", "min", "max"} {
		facts.Add(opt.Fact{
			Proposition: opt.Prop(FactAssociative, op, "integer"),
			Provenance:  opt.ProvedKernel,
			Source:      "spec/lean/Oak/Reduction.lean unrolled4_eq (docs/spec/55-parallelism.md §4)",
		})
	}
	return facts
}

// walkNodes visits every ast.Node reachable from node through exported
// fields and slices, in field order, node first.
func walkNodes(node ast.Node, visit func(ast.Node)) {
	seen := map[uintptr]bool{}
	var walk func(v reflect.Value)
	walk = func(v reflect.Value) {
		switch v.Kind() {
		case reflect.Interface:
			if v.IsNil() {
				return
			}
			walk(v.Elem())
		case reflect.Ptr:
			if v.IsNil() || seen[v.Pointer()] {
				return
			}
			seen[v.Pointer()] = true
			if n, ok := v.Interface().(ast.Node); ok {
				visit(n)
			}
			walk(v.Elem())
		case reflect.Struct:
			for i := 0; i < v.NumField(); i++ {
				if v.Type().Field(i).IsExported() {
					walk(v.Field(i))
				}
			}
		case reflect.Slice, reflect.Array:
			for i := 0; i < v.Len(); i++ {
				walk(v.Index(i))
			}
		}
	}
	walk(reflect.ValueOf(node))
}

// Metrics measures a lowered body: instruction classes over the whole
// body and per loop, a loop being the items from a label to a branch back
// to it (docs/notes/optimizer-search-2026-09.md §9). Each loop's stride is
// read from the increment of the register its exit compares (an `add
// wN, wN, #k`), and a stride-one loop right after a strided loop over the
// same register — the remainder loop of an unrolling — is bounded by the
// stride's trips. Both are the cost model's hints.
func Metrics(fn *asm.Function) opt.Metrics {
	var m opt.Metrics
	if fn == nil {
		return m
	}
	labelAt := map[string]int{}
	for i, item := range fn.Items {
		if label, ok := item.(asm.Label); ok {
			labelAt[label.Name] = i
		}
	}
	type loopRange struct{ from, to int }
	var loops []loopRange
	inLoop := make([]bool, len(fn.Items))
	for i, item := range fn.Items {
		ins, ok := item.(asm.Instruction)
		if !ok || !isBranch(fn.Arch, ins) {
			continue
		}
		if at, isLabel := labelAt[branchTarget(ins)]; isLabel && at < i {
			loops = append(loops, loopRange{at, i})
			for j := at; j <= i; j++ {
				inLoop[j] = true
			}
		}
	}
	sort.Slice(loops, func(i, j int) bool { return loops[i].from < loops[j].from })
	m.Loops = len(loops)
	classify := func(i int, ins asm.Instruction, count *opt.LoopMetrics) {
		count.Instructions++
		switch {
		case isCall(fn.Arch, ins):
		case isBranch(fn.Arch, ins):
			count.Branches++
			if isConditionalBranch(fn.Arch, ins) && strings.HasPrefix(branchTarget(ins), "trap") {
				count.Guards++
			}
		case isLoad(fn.Arch, ins):
			count.Loads++
		case isStore(fn.Arch, ins):
			count.Stores++
		}
	}
	var whole, inLoops opt.LoopMetrics
	for i, item := range fn.Items {
		ins, ok := item.(asm.Instruction)
		if !ok {
			continue
		}
		classify(i, ins, &whole)
		if inLoop[i] {
			classify(i, ins, &inLoops)
		}
		switch {
		case isCall(fn.Arch, ins):
			m.Calls++
		case isMultiply(fn.Arch, ins):
			m.Multiplies++
		case isDivide(fn.Arch, ins):
			m.Divides++
		}
	}
	m.Instructions, m.Branches, m.Loads, m.Stores, m.Guards = whole.Instructions, whole.Branches, whole.Loads, whole.Stores, whole.Guards
	m.LoopInstructions, m.LoopBranches, m.LoopLoads, m.LoopStores, m.LoopGuards = inLoops.Instructions, inLoops.Branches, inLoops.Loads, inLoops.Stores, inLoops.Guards
	indices := make([]int, len(loops)) // each loop's index register, -1 when unknown
	for k, loop := range loops {
		var body opt.LoopMetrics
		compared := map[int]bool{}
		for i := loop.from; i <= loop.to; i++ {
			ins, ok := fn.Items[i].(asm.Instruction)
			if !ok {
				continue
			}
			classify(i, ins, &body)
			if isCompare(fn.Arch, ins) {
				for _, r := range generalRegisters(ins) {
					compared[r] = true
				}
			}
		}
		// The index register: compared in the loop, written exactly once
		// in it, by `add r, r, #k` — its stride. A register the loop
		// rounds or rebuilds (an `add r, r, #7` before a shift) is not one.
		defs := map[int]int{}
		for i := loop.from; i <= loop.to; i++ {
			if ins, ok := fn.Items[i].(asm.Instruction); ok {
				for _, r := range writtenGeneral(ins) {
					defs[r]++
				}
			}
		}
		body.Stride, indices[k] = 1, -1
		for i := loop.from; i <= loop.to; i++ {
			if reg, step, ok := increment(fn.Arch, fn.Items[i]); ok && compared[reg] && defs[reg] == 1 {
				body.Stride, indices[k] = step, reg
				break
			}
		}
		if k > 0 && body.Stride == 1 && indices[k-1] == indices[k] && indices[k] >= 0 && loops[k-1].to < loop.from {
			if prev := m.LoopBodies[k-1]; prev.Stride > 1 {
				body.MaxTrips = prev.Stride - 1
			}
		}
		m.LoopBodies = append(m.LoopBodies, body)
	}
	return m
}

// isCompare reports an instruction that compares registers for a branch:
// a compare on the AArch64 lane, a conditional branch on the RV64 lane.
func isCompare(arch string, ins asm.Instruction) bool {
	if arch == asm.ArchRV64 {
		return isConditionalBranch(arch, ins)
	}
	switch ins.Mnemonic {
	case "cmp", "cmn", "subs", "cbz", "cbnz", "tst":
		return true
	}
	return false
}

// increment reads `add rN, rN, #k` (`addi rN, rN, k` on RV64): the
// register and its step.
func increment(arch string, item asm.Item) (int, int, bool) {
	ins, ok := item.(asm.Instruction)
	if !ok || len(ins.Operands) != 3 {
		return 0, 0, false
	}
	if (arch == asm.ArchRV64 && ins.Mnemonic != "addi") || (arch != asm.ArchRV64 && ins.Mnemonic != "add") {
		return 0, 0, false
	}
	dest, isReg := ins.Operands[0].(asm.Register)
	src, isSrc := ins.Operands[1].(asm.Register)
	imm, isImm := ins.Operands[2].(asm.Immediate)
	if !isReg || !isSrc || !isImm || dest.Num != src.Num || dest.Class != src.Class || imm.Value <= 0 {
		return 0, 0, false
	}
	return dest.Num, int(imm.Value), true
}

func isCall(arch string, ins asm.Instruction) bool {
	if arch == asm.ArchRV64 {
		return ins.Mnemonic == "call" || ins.Mnemonic == "jal" || ins.Mnemonic == "jalr"
	}
	return ins.Mnemonic == "bl" || ins.Mnemonic == "blr"
}

func isConditionalBranch(arch string, ins asm.Instruction) bool {
	if arch == asm.ArchRV64 {
		switch ins.Mnemonic {
		case "beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "blez", "bgez", "bltz", "bgtz":
			return true
		}
		return false
	}
	switch ins.Mnemonic {
	case "b.", "cbz", "cbnz", "tbz", "tbnz":
		return true
	case "b":
		return ins.Cond != ""
	}
	return false
}

func isBranch(arch string, ins asm.Instruction) bool {
	if isConditionalBranch(arch, ins) {
		return true
	}
	if arch == asm.ArchRV64 {
		return ins.Mnemonic == "j" || ins.Mnemonic == "jr"
	}
	return ins.Mnemonic == "b" || ins.Mnemonic == "br"
}

func isLoad(arch string, ins asm.Instruction) bool {
	if arch == asm.ArchRV64 {
		switch ins.Mnemonic {
		case "lb", "lh", "lw", "ld", "lbu", "lhu", "lwu", "flw", "fld", "lr.w", "lr.d":
			return true
		}
		return strings.HasPrefix(ins.Mnemonic, "vle") || strings.HasPrefix(ins.Mnemonic, "vl")
	}
	if isPlainLoadMnemonic(ins.Mnemonic) {
		return true
	}
	switch ins.Mnemonic {
	case "ldar", "ldarb", "ldarh", "ldxr", "ldaxr", "ld1", "ld1r", "ldp", "ldnp":
		return true
	}
	return false
}

func isStore(arch string, ins asm.Instruction) bool {
	if arch == asm.ArchRV64 {
		switch ins.Mnemonic {
		case "sb", "sh", "sw", "sd", "fsw", "fsd", "sc.w", "sc.d":
			return true
		}
		return strings.HasPrefix(ins.Mnemonic, "vse") || strings.HasPrefix(ins.Mnemonic, "vs")
	}
	switch ins.Mnemonic {
	case "str", "strb", "strh", "stp", "stur", "stlr", "stlrb", "stlrh", "stxr", "stlxr", "st1", "stnp":
		return true
	}
	return false
}

func isMultiply(arch string, ins asm.Instruction) bool {
	if arch == asm.ArchRV64 {
		switch ins.Mnemonic {
		case "mul", "mulh", "mulhu", "mulhsu", "mulw":
			return true
		}
		return false
	}
	switch ins.Mnemonic {
	case "mul", "madd", "msub", "mneg", "smull", "umull", "smulh", "umulh", "smaddl", "umaddl":
		return true
	}
	return false
}

func isDivide(arch string, ins asm.Instruction) bool {
	if arch == asm.ArchRV64 {
		switch ins.Mnemonic {
		case "div", "divu", "rem", "remu", "divw", "divuw", "remw", "remuw":
			return true
		}
		return false
	}
	return ins.Mnemonic == "udiv" || ins.Mnemonic == "sdiv"
}
