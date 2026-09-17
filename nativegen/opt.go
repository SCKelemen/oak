package nativegen

import (
	"fmt"
	"reflect"
	"sort"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/machine"
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
	TransformStrength        = "strength-reduce"
	TransformOptIR           = "optir-emit"
	TransformElide           = "elide-guards"
	TransformReuseFlags      = "reuse-flags"
	TransformHoist           = "hoist-invariants"
	TransformUnroll          = "unroll-reductions"
	TransformUnrollFills     = "unroll-fills"
	TransformVectorHomes     = "vector-homes"
	TransformLoopArrayHomes  = "loop-array-homes"
	TransformLoopResultHomes = "loop-result-homes"
	TransformCleanup         = "late-cleanup"
	TransformVectorize       = "vectorize-reductions"
	TransformVectorMaps      = "vectorize-maps"
	TransformUnrollMaps      = "unroll-vector-maps"
	TransformVectorFolds     = "vectorize-folds"
	TransformUnrollConst     = "unroll-constant"
	TransformUnrollSmall     = "unroll-small"
	TransformVecBlocks       = "vector-blocks"
	TransformVectorAddresses = "share-vector-addresses"
	TransformMultiplyAdd     = "multiply-add"
	TransformValueSelect     = "value-select"
	TransformReallocate      = "reallocate"
	TransformSchedule        = "schedule"
	TransformFuse            = "fuse"
	TransformFuseExits       = "fuse-exits"
	TransformRotate          = "rotate-loops"
	TransformCarryIndex      = "carry-loop-index"
	TransformRedundantGuards = "elide-redundant-guards"
	TransformRecordBases     = "share-record-bases"
	TransformGlobalAddresses = "share-global-addresses"
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
	// eligible cheaply rejects a transform before candidate materialization.
	// Nil means every configuration on the transform's lane is eligible.
	eligible func(Lane) bool
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
	if !ok || !t.arches[laneArch(lane)] || t.applied(lane) || (t.eligible != nil && !t.eligible(lane)) {
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

// gatedTransform ships only on a verifier's verdict (opt.Gated): a body
// the verifier cannot judge keeps a form without it.
type gatedTransform struct {
	laneTransform
	// neutral marks a transform that moves and renames but changes no
	// evaluation shape the verifier reads (a register assignment, an
	// instruction order): its candidate shares its parent's shape in the
	// search's validation order (opt.Neutral).
	neutral bool
}

// NeedsVerdict marks the transform as gated.
func (t *gatedTransform) NeedsVerdict() bool { return true }

// ShapeNeutral reports a gated transform that changes no evaluation shape.
func (t *gatedTransform) ShapeNeutral() bool { return t.neutral }

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
		&gatedTransform{laneTransform: laneTransform{
			// The generic SSA middle end's optimized CFG becomes a native
			// implementation candidate. The closed AArch64 and RV64 selectors
			// also admit exact whole-region scalar-global stores after verified
			// MemorySSA, DSE, and region-load forwarding. Unsupported effects
			// and types refuse, and every
			// emitted body remains translation-validator gated.
			name: TransformOptIR, phase: opt.PhaseCanonical, proof: opt.Mechanical,
			arches:  bothLanes,
			applied: func(l Lane) bool { return l.UseOptIR || l.OptIR == nil || l.OptIRChanges <= 0 },
			apply:   func(l Lane) Lane { l.UseOptIR = true; return l },
			fired:   OptIRLowered,
		}},
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
		&gatedTransform{laneTransform: laneTransform{
			// Peephole fusion (machine.Fuse): a shift folded into an add's
			// shifted operand, an increment folded into a csinc; machine
			// shape only, shipping only on the verifier's verdict.
			name: TransformFuse, phase: opt.PhaseMachine, proof: opt.Mechanical,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.Fuse },
			apply:   func(l Lane) Lane { l.Fuse = true; return l },
			fired:   Fused,
		}},
		&gatedTransform{laneTransform: laneTransform{
			// Exit-test fusion (machine.FuseExits): a loop's `b.cond exit;
			// cbz back` as `ccmp; b.eq back`, one branch for two, the entry
			// test fused alike; gated like Fuse. The checker reads the
			// compare's fact through the ccmp, the verifier's loop shapes
			// read the ccmp in a tail run.
			name: TransformFuseExits, phase: opt.PhaseMachine, proof: opt.Mechanical,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.FuseExits },
			apply:   func(l Lane) Lane { l.FuseExits = true; return l },
			fired:   FusedExits,
		}},
		&gatedTransform{laneTransform: laneTransform{
			// Instruction scheduling (package machine, Phase B): each block's
			// instructions reordered between barriers so a consumer follows
			// its producer by the producer's latency; machine shape only,
			// shipping only on the verifier's verdict.
			name: TransformSchedule, phase: opt.PhaseMachine, proof: opt.Mechanical,
			arches:  bothLanes,
			applied: func(l Lane) bool { return l.Schedule },
			apply:   func(l Lane) Lane { l.Schedule = true; return l },
			fired:   Scheduled,
		}, neutral: true},
		&laneTransform{
			// Reduction unrolling over four independent accumulators
			// (nativegen/reduction.go): a source rewrite licensed by the
			// operator's associativity (Oak.Reduction.unrolled4_eq); the
			// verifier judges the lowering against the rewritten body.
			// First of the loop phase: the machine passes after it (the
			// invariant pass, the rotation) see the unrolled shape — its
			// slack test is theirs to peel and rotate — where a candidate
			// they fire on nothing would never meet the unrolling.
			name: TransformUnroll, phase: opt.PhaseLoop, proof: opt.LawLicensed,
			reqs:    []opt.Requirement{opt.Require(opt.Prop(FactAssociative), opt.ProvedKernel)},
			arches:  bothLanes,
			applied: func(l Lane) bool { return !l.NoReductions },
			apply:   func(l Lane) Lane { l.NoReductions = false; return l },
			fired:   Unrolled,
		},
		&laneTransform{
			// Scalar blocked zero fills (nativegen/fill_unroll.go): four
			// ordered u64 stores per main trip and the original remainder,
			// licensed by Oak.BlockedFill.blocked_fill_eq. The stores remain
			// scalar; pair-store custody is a separate, unmet obligation.
			name: TransformUnrollFills, phase: opt.PhaseLoop, proof: opt.LawLicensed,
			arches:   bothLanes,
			applied:  func(l Lane) bool { return l.UnrollFills },
			eligible: func(l Lane) bool { return l.UnrollFillsEligible },
			apply:    func(l Lane) Lane { l.UnrollFills = true; return l },
			fired:    UnrolledFills,
		},
		&laneTransform{
			// Reduction vectorization (nativegen/vector_reduction.go): the
			// four accumulators as the lanes of fixed vectors — two
			// simd.U64x2 or one simd.U32x4 — under the same license
			// (Oak.Reduction.vector4_eq). It takes the loop the unrolling
			// would, so the search prices the two forms against each
			// other; beside the unrolling at the head of the loop phase,
			// so the invariant pass and the rotation see its shape too.
			name: TransformVectorize, phase: opt.PhaseLoop, proof: opt.LawLicensed,
			reqs:    []opt.Requirement{opt.Require(opt.Prop(FactAssociative), opt.ProvedKernel)},
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.VectorReductions },
			apply:   func(l Lane) Lane { l.VectorReductions = true; return l },
			fired:   Vectorized,
		},
		&laneTransform{
			// Map vectorization (nativegen/vector_map.go): an element-wise
			// map over span parameters as one vector a trip under the slack
			// guard, the remainder as written, licensed by Oak.Map.blocked_eq
			// — lane-wise semantics alone, no law of the element type, so no
			// fact of the body is required.
			// AArch64 only for now. The RV64 lane lowers the rewritten shape
			// to RVV under its fixed configurations, the machine lift reads it
			// (stride 4, the remainder bounded) and prices it at half the
			// scalar loop, but the verifier does not yet model a vector store
			// in a data-dependent loop body on that lane, so the form can
			// only be trusted and never ships over the proven scalar loop
			// (2026-09-16; the plumbing through compileRV64 is in place).
			name: TransformVectorMaps, phase: opt.PhaseLoop, proof: opt.LawLicensed,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.VectorMaps },
			apply:   func(l Lane) Lane { l.VectorMaps = true; return l },
			fired:   VectorizedMaps,
		},
		&laneTransform{
			// Two consecutive blocks under one slack guard. This only changes
			// a body with VectorMaps enabled; lane-wise semantics license it,
			// without associativity or numerical relaxation.
			name: TransformUnrollMaps, phase: opt.PhaseLoop, proof: opt.LawLicensed,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.UnrollVectorMaps },
			apply:   func(l Lane) Lane { l.UnrollVectorMaps = true; return l },
			fired:   UnrolledMaps,
		},
		&laneTransform{
			// Constant-trip unrolling (nativegen/unroll_constant.go): a loop
			// from zero to a literal bound becomes its trips, the index a
			// literal in each, licensed by Oak.ConstantUnroll.loop_eq_unrolled
			// — nothing of the body is assumed, so no fact is required. What
			// it buys is downstream: constant indices where the loop's
			// variable indexed a frame array, so the slot promotion can keep
			// the array's words in registers. At the head of the loop phase,
			// so the other loop rewrites see the trips.
			name: TransformUnrollConst, phase: opt.PhaseLoop, proof: opt.LawLicensed,
			arches:   arm64Only,
			applied:  func(l Lane) bool { return l.UnrollConstant },
			eligible: func(l Lane) bool { return !l.UnrollSmall },
			apply:    func(l Lane) Lane { l.UnrollConstant = true; return l },
			fired:    UnrolledConstant,
		},
		&gatedTransform{laneTransform: laneTransform{
			// The same exact loop law with a bounded copy policy and a
			// placement-only veto. Keep the full strategy as an alternative,
			// never combine their rewrite or cache identities.
			name: TransformUnrollSmall, phase: opt.PhaseLoop, proof: opt.LawLicensed,
			arches:   arm64Only,
			applied:  func(l Lane) bool { return l.UnrollSmall },
			eligible: func(l Lane) bool { return !l.UnrollConstant },
			apply:    func(l Lane) Lane { l.UnrollSmall = true; return l },
			fired:    UnrolledSmall,
		}},
		&laneTransform{
			// Fold vectorization (nativegen/vector_fold.go): a float
			// reduction whose element expression is lane-wise over span
			// parameters — the dot product — computes one vector of element
			// values a trip and adds its lanes in element order, licensed by
			// Oak.Fold.blocked_eq: lane-wise semantics and the kept order, no
			// law of the element type, so no fact of the body is required and
			// the float accumulator rounds as the scalar loop's did.
			name: TransformVectorFolds, phase: opt.PhaseLoop, proof: opt.LawLicensed,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.VectorFolds },
			apply:   func(l Lane) Lane { l.VectorFolds = true; return l },
			fired:   VectorizedFolds,
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
		&gatedTransform{laneTransform: laneTransform{
			// Bottom-tested loops (nativegen/rotate.go; §9 "Bottom-tested
			// loops"): a loop over a conjunction of simple tests runs its
			// test at the tail as a conditional back edge, one branch an
			// iteration; machine shape only, the verifier recognizing the
			// shape. After the invariant pass, whose loop finder reads the
			// top-tested shape.
			name: TransformRotate, phase: opt.PhaseLoop, proof: opt.Mechanical,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.RotateLoops },
			apply:   func(l Lane) Lane { l.RotateLoops = true; return l },
			fired:   RotatedLoops,
		}},
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
		&gatedTransform{laneTransform: laneTransform{
			// Selected literal-index u32/u64 array elements live in
			// callee-saved registers for one loop (loop_array_homes.go).
			// The full verifier compares the machine candidate with the
			// unchanged Oak reference; unsupported shapes remain memory-backed.
			name: TransformLoopArrayHomes, phase: opt.PhaseMachine, proof: opt.Mechanical,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.LoopArrayHomes },
			apply:   func(l Lane) Lane { l.LoopArrayHomes = true; return l },
			fired:   LoopArrayHomes,
		}},
		&gatedTransform{laneTransform: laneTransform{
			// Selected literal-index elements of an eligible result-buffer
			// array live in callee-saved registers for one loop. This remains
			// a separate machine candidate judged against the Oak reference.
			name: TransformLoopResultHomes, phase: opt.PhaseMachine, proof: opt.Mechanical,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.LoopResultHomes },
			apply:   func(l Lane) Lane { l.LoopResultHomes = true; return l },
			fired:   LoopResultHomes,
		}},
		&gatedTransform{laneTransform: laneTransform{
			// Global register reallocation and frame-slot promotion (package
			// machine, Phase B): the body's def-use webs recolored by a
			// linear scan, its slots moved into registers, its copies
			// coalesced, within the registers the lowering wrote; machine
			// shape only, judged by the checker and the verifier — and, new,
			// shipping only on the verifier's verdict.
			name: TransformReallocate, phase: opt.PhaseMachine, proof: opt.Mechanical,
			arches:  bothLanes,
			applied: func(l Lane) bool { return l.Reallocate },
			apply:   func(l Lane) Lane { l.Reallocate = true; return l },
			fired:   Reallocated,
		}, neutral: true},
		&gatedTransform{laneTransform: laneTransform{
			name: TransformCarryIndex, phase: opt.PhaseMachine, proof: opt.Mechanical,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.CarryLoopIndices },
			apply:   func(l Lane) Lane { l.CarryLoopIndices = true; return l },
			fired:   CarriedLoopIndices,
		}},
		&gatedTransform{laneTransform: laneTransform{
			name: TransformRedundantGuards, phase: opt.PhaseMachine, proof: opt.Mechanical,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.ElideRedundantGuards },
			apply:   func(l Lane) Lane { l.ElideRedundantGuards = true; return l },
			fired:   ElidedRedundantGuards,
		}},
		&gatedTransform{laneTransform: laneTransform{
			name: TransformRecordBases, phase: opt.PhaseMachine, proof: opt.Mechanical,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.ShareRecordBases },
			apply:   func(l Lane) Lane { l.ShareRecordBases = true; return l },
			fired:   SharedRecordBases,
		}},
		&gatedTransform{laneTransform: laneTransform{
			name: TransformGlobalAddresses, phase: opt.PhaseMachine, proof: opt.Mechanical,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.ShareGlobalAddresses },
			apply:   func(l Lane) Lane { l.ShareGlobalAddresses = true; return l },
			fired:   SharedGlobalAddresses,
		}},
		multiplyAddTransform,
		valueSelectTransform,
		vecBlocksTransform,
		cleanupTransform,
		&gatedTransform{laneTransform: laneTransform{
			// Copy cleanup exposes private address temporaries. Retry load
			// sharing and include stores, in place: no memory reordering.
			// This is a new gated candidate, not more authority for the
			// earlier load-only vecBlocksTransform.
			name: TransformVectorAddresses, phase: opt.PhaseMachine, proof: opt.Mechanical,
			arches:  arm64Only,
			applied: func(l Lane) bool { return l.ShareVectorAddresses },
			apply:   func(l Lane) Lane { l.ShareVectorAddresses = true; return l },
			fired:   SharedVectorAddresses,
		}},
	}
}

// cleanupTransform is the late copy and branch cleanup (nativegen/cleanup.go).
var cleanupTransform = &laneTransform{
	// Late cleanup (docs/spec/94-assembler.md §9 "Late cleanup"): a copy
	// read once by the next instruction is forwarded, a definition copied
	// once writes its destination, and narrowly proved branch/store materialized
	// temporaries disappear. Machine shape only: always seam-checked, and judged
	// by the verifier only where that verifier's subset applies.
	name: TransformCleanup, phase: opt.PhaseMachine, proof: opt.Mechanical,
	arches:  arm64Only,
	applied: func(l Lane) bool { return l.Cleanup },
	apply:   func(l Lane) Lane { l.Cleanup = true; return l },
	fired:   CleanedCopies,
}

// multiplyAddTransform lowers a product and its addend in one instruction
// (nativegen/multiply_add.go).
var multiplyAddTransform = &laneTransform{
	// Multiply-add forms (docs/spec/94-assembler.md §9 "Multiply-add
	// forms"): `a + b * c` as madd, `a - b * c` as msub, `0 - b * c` as
	// mneg — the machine's own arithmetic, judged by the verifier, which
	// reads all three as the product and its term.
	name: TransformMultiplyAdd, phase: opt.PhaseCanonical, proof: opt.Canonical,
	arches:  arm64Only,
	applied: func(l Lane) bool { return l.MultiplyAdd },
	apply:   func(l Lane) Lane { l.MultiplyAdd = true; return l },
	fired:   FusedMultiplies,
}

// valueSelectTransform lowers a value-position conditional as one
// conditional select (nativegen/value_select.go).
var valueSelectTransform = &laneTransform{
	// Select forms (docs/spec/94-assembler.md §9 "Select forms"): a
	// compare and one csel — or csinc, csneg, csinv where the arms share
	// an operand — where the lowering branched over two moves. The
	// verifier models all four already.
	name: TransformValueSelect, phase: opt.PhaseMachine, proof: opt.Mechanical,
	arches:  arm64Only,
	applied: func(l Lane) bool { return l.ValueSelect },
	apply:   func(l Lane) Lane { l.ValueSelect = true; return l },
	fired:   ValueSelects,
}

// vecBlocksTransform reads a block's vector loads off one element address
// (nativegen/vector_blocks.go).
var vecBlocksTransform = &laneTransform{
	// Vector block loads (docs/spec/94-assembler.md §9 "Vector block
	// loads"): the vector loads of one basic block at immediate offsets
	// off a single element address, where the lowering formed an address
	// register for each — machine shape only, judged by the checker and
	// the verifier.
	name: TransformVecBlocks, phase: opt.PhaseMachine, proof: opt.Mechanical,
	arches:  arm64Only,
	applied: func(l Lane) bool { return l.VectorBlocks },
	apply:   func(l Lane) Lane { l.VectorBlocks = true; return l },
	fired:   FusedVectorBlocks,
}

// Registry is the lane's transform registry.
func Registry() *opt.Registry {
	return opt.NewRegistry(Transforms()...)
}

// PlainLane is the identity configuration of a lane: the given lane with
// every transform off. The search turns them on one by one.
func PlainLane(lane Lane) Lane {
	lane.Strength = false
	lane.UseOptIR = false
	lane.ElideProven = false
	lane.GuardLines = nil
	lane.ReuseFlags = false
	lane.HoistInvariants = false
	lane.RotateLoops = false
	lane.CarryLoopIndices = false
	lane.ElideRedundantGuards = false
	lane.ShareRecordBases = false
	lane.ShareGlobalAddresses = false
	lane.VectorHomes = false
	lane.LoopArrayHomes = false
	lane.LoopResultHomes = false
	lane.Cleanup = false
	lane.VectorBlocks = false
	lane.ShareVectorAddresses = false
	lane.MultiplyAdd = false
	lane.ValueSelect = false
	lane.Reallocate = false
	lane.Schedule = false
	lane.Fuse = false
	lane.FuseExits = false
	lane.VectorReductions = false
	lane.VectorMaps = false
	lane.UnrollVectorMaps = false
	lane.VectorFolds = false
	lane.UnrollConstant = false
	lane.UnrollSmall = false
	lane.UnrollFills = false
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
		proof, hasProof := tc.IndexProof(index.Token)
		fact := opt.Fact{
			Proposition: opt.Prop(FactIndexInExtent, index.String()),
			Provenance:  opt.Checked,
			Source:      "typechecker/extents.go IndexProven",
			Scope:       fmt.Sprintf("line %d", index.Token.Line),
		}
		if hasProof {
			fact.ID = proof.ID
			fact.Proposition = opt.Prop(proof.Proposition, index.Index.String(), proof.Container)
			fact.Source = proof.Witness
			fact.Scope = proof.Scope
			for _, dependency := range proof.Dependencies {
				fact.Dependencies = append(fact.Dependencies, opt.Prop(dependency))
			}
		}
		facts.Add(fact)
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
// wN, wN, #k`), and a smaller-stride loop right after a strided loop over the
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
	// Nesting: a loop's outer loop is the innermost range enclosing it;
	// the items of a nested loop are that loop's own, not its outer
	// loops' — the cost model charges them by the trips of every loop
	// around them (opt.LoopMetrics.Outer).
	encloses := func(j, k int) bool {
		return j != k && loops[j].from <= loops[k].from && loops[k].to <= loops[j].to && (loops[j].from < loops[k].from || loops[k].to < loops[j].to)
	}
	outer := make([]int, len(loops))
	depth := make([]int, len(loops))
	for k := range loops {
		outer[k] = -1
		for j := range loops {
			if encloses(j, k) {
				depth[k]++
				if outer[k] < 0 || loops[j].from > loops[outer[k]].from || (loops[j].from == loops[outer[k]].from && loops[j].to < loops[outer[k]].to) {
					outer[k] = j
				}
			}
		}
	}
	nested := func(k, i int) bool {
		for j := range loops {
			if encloses(k, j) && loops[j].from <= i && i <= loops[j].to {
				return true
			}
		}
		return false
	}
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
	// The stall estimate (machine.StallEstimate): the total, and per loop
	// the blocks the loop spans, by label.
	stalls, stallsByLabel := machine.StallEstimate(fn)
	m.Stalls = stalls
	// The recurrence analysis (machine.LoopShapes) reads each loop's
	// index, stride, and trip bound off the lifted body; a body the lift
	// refuses keeps the register-increment heuristic below.
	shapes := map[string]*machine.LoopShape{}
	if analyzed, err := machine.LoopShapes(fn); err == nil {
		for _, sh := range analyzed {
			if sh.Header != "" {
				shapes[sh.Header] = sh
			}
		}
	}
	indices := make([]int, len(loops)) // each loop's index register, -1 when unknown
	for k, loop := range loops {
		body := opt.LoopMetrics{Depth: depth[k], Outer: outer[k] + 1}
		compared := map[int]bool{}
		for i := loop.from; i <= loop.to; i++ {
			ins, ok := fn.Items[i].(asm.Instruction)
			if !ok || nested(k, i) {
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
			if ins, ok := fn.Items[i].(asm.Instruction); ok && !nested(k, i) {
				for _, r := range writtenGeneral(ins) {
					defs[r]++
				}
			}
		}
		body.Stride, indices[k] = 1, -1
		for i := loop.from; i <= loop.to; i++ {
			if nested(k, i) {
				continue
			}
			if reg, step, ok := increment(fn.Arch, fn.Items[i]); ok && compared[reg] && defs[reg] == 1 {
				body.Stride, indices[k] = step, reg
				break
			}
		}
		if k > 0 && body.Stride > 0 && indices[k-1] == indices[k] && indices[k] >= 0 && loops[k-1].to < loop.from && outer[k-1] == outer[k] {
			if prev := m.LoopBodies[k-1]; prev.Stride > body.Stride {
				body.MaxTrips = (prev.Stride - 1) / body.Stride
			}
		}
		for i := loop.from; i <= loop.to; i++ {
			if label, ok := fn.Items[i].(asm.Label); ok {
				body.Stalls += stallsByLabel[label.Name]
			}
		}
		m.LoopStalls += body.Stalls
		if label, ok := fn.Items[loop.from].(asm.Label); ok {
			if sh := shapes[label.Name]; sh != nil && sh.Index != nil {
				// The recurrence web is also the best identity for the
				// cost-only constant-bound fallback below.
				indices[k] = sh.Index.Reg.Num
				// The analysis found the index: its stride and bound
				// replace the heuristic's; a loop it could not read keeps
				// the heuristic's reading.
				body.Stride = sh.Stride
				if sh.MaxTrips > 0 {
					body.MaxTrips = sh.MaxTrips
				}
			}
		}
		if body.MaxTrips == 0 && body.Stride > 0 && indices[k] >= 0 {
			body.MaxTrips = constantLoopTrips(fn.Items, loop.from, loop.to, indices[k], body.Stride, labelAt)
		}
		m.LoopBodies = append(m.LoopBodies, body)
	}
	return m
}

// constantLoopTrips recovers a cost-only bound from the generator's closed
// unsigned exit shapes when recurrence analysis leaves a computed constant
// in a temporary. It grants no checker or verifier authority.
func constantLoopTrips(items []asm.Item, from, to, index, stride int, labels map[string]int) int {
	start, known := constantRegisterBefore(items, from, index, 0)
	if !known || start < 0 || stride <= 0 {
		return 0
	}
	for i := from + 1; i < to; i++ {
		cmp, isInstruction := items[i].(asm.Instruction)
		if !isInstruction || cmp.Mnemonic != "cmp" || len(cmp.Operands) != 2 {
			continue
		}
		left, isRegister := cmp.Operands[0].(asm.Register)
		if !isRegister || left.Num != index || (left.Class != asm.ClassW && left.Class != asm.ClassX) {
			continue
		}
		branch, isBranch := items[i+1].(asm.Instruction)
		if !isBranch || (branch.Mnemonic != "b" && branch.Mnemonic != "b.") || (branch.Cond != "hs" && branch.Cond != "hi") {
			continue
		}
		target, exists := labels[branchTarget(branch)]
		if !exists || (target >= from && target <= to) {
			continue
		}
		bound, known := constantLoopBound(items, from, to, i, cmp.Operands[1], left.Class)
		if !known || bound < start {
			continue
		}
		delta := bound - start
		step := int64(stride)
		var trips int64
		if branch.Cond == "hi" {
			trips = delta/step + 1
		} else if delta > 0 {
			trips = (delta + step - 1) / step
		}
		if trips > 0 && trips <= 1<<31 {
			return int(trips)
		}
	}
	return 0
}

// constantLoopBound resolves a compare operand at the branch, then permits
// one cost-only look through the loop header for an invariant register. The
// latter is fail closed: a definition anywhere in the loop, or a call that
// may clobber an implicit caller-saved register, leaves the trip count unknown.
func constantLoopBound(items []asm.Item, from, to, at int, operand asm.Operand, class asm.RegClass) (int64, bool) {
	if value, known := constantOperandBefore(items, at, operand, class, 0); known {
		return value, true
	}
	reg, isRegister := operand.(asm.Register)
	if !isRegister || reg.Class != class {
		return 0, false
	}
	for i := from; i <= to && i < len(items); i++ {
		ins, isInstruction := items[i].(asm.Instruction)
		if !isInstruction {
			continue
		}
		if isCall(asm.ArchArm64, ins) || writesGeneral(ins, reg.Num) {
			return 0, false
		}
	}
	return constantRegisterBefore(items, from, reg.Num, 0)
}

func constantOperandBefore(items []asm.Item, at int, operand asm.Operand, class asm.RegClass, depth int) (int64, bool) {
	switch value := operand.(type) {
	case asm.Immediate:
		if value.Shift != 0 {
			return 0, false
		}
		return value.Value, value.Value >= 0
	case asm.Register:
		if value.Class != class {
			return 0, false
		}
		return constantRegisterBefore(items, at, value.Num, depth)
	default:
		return 0, false
	}
}

// constantRegisterBefore follows only a nearest straight-line W/X
// definition. Labels and control or memory instructions terminate the walk;
// arithmetic that would wrap is refused rather than modeled.
func constantRegisterBefore(items []asm.Item, at, register, depth int) (int64, bool) {
	if depth > 4 {
		return 0, false
	}
	for i := at - 1; i >= 0; i-- {
		if _, isLabel := items[i].(asm.Label); isLabel {
			return 0, false
		}
		ins, isInstruction := items[i].(asm.Instruction)
		if !isInstruction {
			return 0, false
		}
		if isCall("arm64", ins) || isLoad("arm64", ins) || isStore("arm64", ins) {
			return 0, false
		}
		if isBranch("arm64", ins) {
			// A conditional branch before this point either exits or falls
			// through without changing a register. Along the only path that
			// reaches `at`, its value is preserved. An unconditional edge can
			// introduce a join the linear scan cannot model.
			if ins.Cond == "" {
				return 0, false
			}
			continue
		}
		if !writesGeneral(ins, register) {
			continue
		}
		if len(ins.Operands) < 2 {
			return 0, false
		}
		destination, ok := ins.Operands[0].(asm.Register)
		if !ok || destination.Num != register || (destination.Class != asm.ClassW && destination.Class != asm.ClassX) {
			return 0, false
		}
		limit := int64(^uint32(0))
		if destination.Class == asm.ClassX {
			limit = int64(^uint64(0) >> 1)
		}
		switch ins.Mnemonic {
		case "mov":
			source, ok := ins.Operands[1].(asm.Register)
			if !ok || source.Class != destination.Class {
				return 0, false
			}
			if source.ZeroRegister() {
				return 0, true
			}
			return constantRegisterBefore(items, i, source.Num, depth+1)
		case "movz":
			immediate, ok := ins.Operands[1].(asm.Immediate)
			if !ok || immediate.Value < 0 || immediate.Shift < 0 || immediate.Shift > 48 {
				return 0, false
			}
			value := immediate.Value << immediate.Shift
			return value, value >= 0 && value <= limit
		case "add", "sub":
			if len(ins.Operands) != 3 {
				return 0, false
			}
			source, ok := ins.Operands[1].(asm.Register)
			if !ok || source.Class != destination.Class {
				return 0, false
			}
			base, known := constantRegisterBefore(items, i, source.Num, depth+1)
			immediate, isImmediate := ins.Operands[2].(asm.Immediate)
			if !known || !isImmediate || immediate.Value < 0 || immediate.Shift != 0 {
				return 0, false
			}
			value := base + immediate.Value
			if ins.Mnemonic == "sub" {
				value = base - immediate.Value
			}
			return value, value >= 0 && value <= limit
		default:
			return 0, false
		}
	}
	return 0, false
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
