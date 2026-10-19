package asm

import "testing"

func TestMergeWritesPreservesGuardedZeroMemory(t *testing.T) {
	p := paramTerm("p", 1)
	fs := frameSpan{name: "v", size: 2, elem: 1, entry: true}
	filled := &symbolicState{}
	for i := uint64(0); i < 2; i++ {
		filled.writes = appendWrite(filled.writes, fs.name, constTerm(i, 32), constTerm(0, 8), nil)
	}
	collapseZeroFill(filled, fs)
	if log := filled.writes[fs.name]; len(log) != 1 || log[0].memory != zeroMemory || log[0].guard != nil {
		t.Fatal("complete unconditional fill must produce one unconditional zero marker")
	}
	stored := appendWrite(nil, fs.name, constTerm(0, 32), constTerm(1, 8), nil)
	for _, zeroTaken := range []bool{false, true} {
		name := "zero_fallthrough"
		taken, fallthroughLog := stored, filled.writes
		if zeroTaken {
			name = "zero_taken"
			taken, fallthroughLog = filled.writes, stored
		}
		t.Run(name, func(t *testing.T) {
			merged := mergeWrites(p, taken, fallthroughLog)
			zeroGuarded := false
			for _, w := range merged[fs.name] {
				if w.memory == zeroMemory {
					zeroGuarded = w.guard != nil
				}
			}
			if !zeroGuarded || filled.writes[fs.name][0].guard != nil || stored[fs.name][0].guard != nil {
				t.Fatal("merge must guard branch-only markers without mutating either input")
			}
			for guard := uint64(0); guard < 2; guard++ {
				for index := uint64(0); index < 2; index++ {
					for _, entry := range []uint64{0, 7} {
						at, base := constTerm(index, 32), constTerm(entry, 8)
						env := map[string]uint64{"p": guard}
						branch := fallthroughLog[fs.name]
						if guard != 0 {
							branch = taken[fs.name]
						}
						want := memoryAt(branch, at, base).eval(env)
						if got := memoryAt(merged[fs.name], at, base).eval(env); got != want {
							t.Fatalf("merged memory p=%d index=%d entry=%d = %d, selected branch = %d", guard, index, entry, got, want)
						}
					}
				}
			}
		})
	}
}

func TestMemoryAtGuardedZeroPreservesHistoryAndPruning(t *testing.T) {
	p, q := paramTerm("p", 1), paramTerm("q", 1)
	log := []*spanWrite{
		{index: constTerm(0, 32), value: constTerm(3, 8)},
		{memory: zeroMemory, guard: p},
		{index: constTerm(1, 32), value: constTerm(5, 8), guard: q},
	}
	widthOf := func(name string) int {
		if name == "p" || name == "q" {
			return 1
		}
		return 32
	}
	for _, premise := range []*term{constTerm(1, 1), p, notTerm(p)} {
		pruned := pruneWritesUnder(premise, log, widthOf)
		for bits := uint64(0); bits < 4; bits++ {
			env := map[string]uint64{"p": bits & 1, "q": (bits >> 1) & 1}
			if premise.eval(env)&1 == 0 {
				continue
			}
			for index := uint64(0); index < 3; index++ {
				env["i"] = index
				for _, entry := range []uint64{0, 7} {
					want := entry
					if index == 0 {
						want = 3
					}
					if env["p"] != 0 {
						want = 0
					}
					if index == 1 && env["q"] != 0 {
						want = 5
					}
					for _, at := range []*term{constTerm(index, 32), paramTerm("i", 32)} {
						for _, writes := range [][]*spanWrite{log, pruned} {
							if got := memoryAt(writes, at, constTerm(entry, 8)).eval(env); got != want {
								t.Fatalf("memory p=%d q=%d index=%d entry=%d = %d, want %d", env["p"], env["q"], index, entry, got, want)
							}
						}
					}
				}
			}
		}
	}
	if log[1].guard != p || log[2].guard != q || len(log) != 3 {
		t.Fatal("reading or pruning mutated the original write log")
	}
}

func TestFrameSpanAccessRetainsFillAfterGuardedZero(t *testing.T) {
	p := paramTerm("p", 1)
	fs := frameSpan{name: "out", size: 16, elem: 1, entry: true}
	mem := Memory{Base: Register{Text: "sp", Class: ClassX, Num: -1}, Mode: MemOffset}
	instr := Instruction{Mnemonic: "str", Operands: []Operand{Register{Text: "xzr", Class: ClassX, Num: 31}, mem}}
	for _, conditional := range []bool{false, true} {
		name := "unconditional"
		var guard *term
		wantWrites := 1
		if conditional {
			name, guard, wantWrites = "conditional", p, 9
		}
		t.Run(name, func(t *testing.T) {
			state := &symbolicState{writes: map[string][]*spanWrite{fs.name: {{memory: zeroMemory, guard: guard}}}}
			x := &pathExecutor{}
			if reason, ok := x.frameSpanAccess(instr, state, fs, 0, mem); !ok {
				t.Fatalf("wide zero store was refused: %s", reason)
			}
			if got := len(state.writes[fs.name]); got != wantWrites {
				t.Fatalf("write count = %d, want %d", got, wantWrites)
			}
			for active := uint64(0); active < 2; active++ {
				for index := uint64(0); index < 16; index++ {
					want := uint64(0)
					if conditional && active == 0 && index >= 8 {
						want = 9
					}
					got := memoryAt(state.writes[fs.name], constTerm(index, 32), constTerm(9, 8)).eval(map[string]uint64{"p": active})
					if got != want {
						t.Fatalf("read after fill p=%d index=%d = %d, want %d", active, index, got, want)
					}
				}
			}
		})
	}
}
