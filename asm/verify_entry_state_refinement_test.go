package asm

import (
	"fmt"
	"testing"
)

// A deliberately independent two-bit abstraction of the symbolic executor:
// bound records a currently materialized register value, invalid records
// that the original entry value is no longer available for lazy reads.
type entryProvenanceOracle struct {
	bound   bool
	invalid bool
}

func oracleEntryReadable(arch string, reg int) bool {
	switch arch {
	case ArchArm64:
		return reg >= 19 && reg <= 30
	case ArchRV64:
		return reg == 1 || reg == 8 || reg == 9 || (reg >= 18 && reg <= 27)
	default:
		return false
	}
}

func oracleCallerClobbered(arch string, reg int) bool {
	switch arch {
	case ArchArm64:
		return reg <= 17 || reg == 30
	case ArchRV64:
		return reg == 1 || (reg >= 5 && reg <= 7) || (reg >= 10 && reg <= 17) || reg >= 28
	default:
		return false
	}
}

func (o *entryProvenanceOracle) step(arch string, reg, op int) {
	switch op {
	case 0: // read: a valid incoming value is materialized
		if !o.bound && !o.invalid && oracleEntryReadable(arch, reg) {
			o.bound = true
		}
	case 1: // a real instruction writes a register
		o.bound = true
	case 2: // explicitly invalidate a register
		o.bound = false
		o.invalid = o.invalid || oracleEntryReadable(arch, reg)
	case 3: // a native function call invalidates the caller-saved subset
		if oracleCallerClobbered(arch, reg) {
			o.bound = false
			o.invalid = o.invalid || oracleEntryReadable(arch, reg)
		}
	}
}

func applyEntryProvenanceOperation(s *symbolicState, arch string, reg Register, op, serial int) {
	switch op {
	case 0:
		s.read(reg)
	case 1:
		s.write(reg, constTerm(uint64(101+serial), 64))
	case 2:
		s.clobberGPR(reg.Num)
	case 3:
		(&pathExecutor{arch: arch}).forgetCallerSaved(s)
	}
}

func checkEntryProvenanceAbstraction(t *testing.T, s *symbolicState, expected entryProvenanceOracle, arch string, reg Register, history string) {
	t.Helper()
	if got := s.invalidEntryGPR[reg.Num]; got != expected.invalid {
		t.Fatalf("%s register %d history %s: invalid=%v, want %v", arch, reg.Num, history, got, expected.invalid)
	}
	if _, bound := s.regs[reg.Num]; bound != expected.bound {
		t.Fatalf("%s register %d history %s: bound=%v, want %v", arch, reg.Num, history, bound, expected.bound)
	}
	// Reading a clone tests availability without mutating the state under
	// comparison: lazy reads must not change the oracle's next transition.
	copy := s.clone()
	value, ok := copy.read(reg)
	want := expected.bound || (!expected.invalid && oracleEntryReadable(arch, reg.Num))
	if ok != want || (value != nil) != want {
		t.Fatalf("%s register %d history %s: readable=%v, want %v", arch, reg.Num, history, ok, want)
	}
}

// Exhaustively compare short fork/join traces against the actual verifier.
// The independent oracle never invokes the production ISA policy for expected
// entry/clobber masks or its implementation of read/write/clone/merge.
func TestNativeVerifierRegisterStateRefinement(t *testing.T) {
	for _, lane := range []struct {
		arch   string
		class  RegClass
		maxReg int
		link   int
	}{
		{ArchArm64, ClassX, 30, 30},
		{ArchRV64, ClassRV64X, 31, 1},
	} {
		for regNum := 1; regNum <= lane.maxReg; regNum++ {
			reg := Register{Class: lane.class, Num: regNum}
			length := 2
			if regNum == lane.link {
				length = 3
			}
			options := 1
			for i := 0; i < length; i++ {
				options *= 4
			}
			for leftCode := 0; leftCode < options; leftCode++ {
				for rightCode := 0; rightCode < options; rightCode++ {
					initial := &symbolicState{arch: lane.arch, regs: map[int]*term{}}
					left, right := initial.clone(), initial.clone()
					var leftOracle, rightOracle entryProvenanceOracle
					run := func(s *symbolicState, model *entryProvenanceOracle, code int, path string) {
						for step := 0; step < length; step++ {
							op := (code >> (2 * step)) & 3
							model.step(lane.arch, regNum, op)
							applyEntryProvenanceOperation(s, lane.arch, reg, op, step+code)
							checkEntryProvenanceAbstraction(t, s, *model, lane.arch, reg, fmt.Sprintf("%s:%d/%d", path, code, step))
						}
					}
					run(left, &leftOracle, leftCode, "left")
					run(right, &rightOracle, rightCode, "right")
					joined, ok := (&pathExecutor{arch: lane.arch}).mergeTwo(constTerm(1, 1), left, right)
					if !ok {
						t.Fatalf("%s register %d: refused equal-architecture empty-frame join", lane.arch, regNum)
					}
					joinedOracle := entryProvenanceOracle{
						bound:   leftOracle.bound && rightOracle.bound,
						invalid: leftOracle.invalid || rightOracle.invalid,
					}
					checkEntryProvenanceAbstraction(t, joined, joinedOracle, lane.arch, reg,
						fmt.Sprintf("join(%d,%d)", leftCode, rightCode))
					// A subsequent call cannot release the invalidated
					// entry value, even after the join selected real values.
					joinedOracle.step(lane.arch, regNum, 3)
					applyEntryProvenanceOperation(joined, lane.arch, reg, 3, 0)
					checkEntryProvenanceAbstraction(t, joined, joinedOracle, lane.arch, reg,
						fmt.Sprintf("join-call(%d,%d)", leftCode, rightCode))
				}
			}
		}
	}
}
