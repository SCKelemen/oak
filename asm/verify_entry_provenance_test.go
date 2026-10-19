package asm

import "testing"

// Entry-readable is not an eternal promise: RV64 ra and AArch64 x30 can
// carry their incoming values before a call, but not after the call
// destroys them. All call-return shapes must use clobberGPR.
func TestEntryReadableRegisterDoesNotResurrectAfterCall(t *testing.T) {
	for _, tc := range []struct {
		name       string
		arch       string
		entryClass RegClass
		entryReg   int
		keepReg    int
	}{
		{"rv64 return address", ArchRV64, ClassRV64X, 1, 8},
		{"arm64 link register", ArchArm64, ClassX, 30, 19},
	} {
		t.Run(tc.name, func(t *testing.T) {
			state := &symbolicState{arch: tc.arch, regs: map[int]*term{}}
			one := Register{Class: tc.entryClass, Num: tc.entryReg}
			keep := Register{Class: tc.entryClass, Num: tc.keepReg}
			entry, ok := state.read(one)
			if !ok || entry.kind != termParam {
				t.Fatal("entry-readable register missing before call")
			}
			preserved, ok := state.read(keep)
			if !ok {
				t.Fatal("callee-saved register missing before call")
			}
			(&pathExecutor{arch: tc.arch}).forgetCallerSaved(state)
			if _, ok := state.read(one); ok {
				t.Fatal("call resurrected a clobbered entry register")
			}
			after, ok := state.read(keep)
			if !ok || !equalTerms(after, preserved) {
				t.Fatal("call destroyed a callee-saved entry register")
			}
			replacement := constTerm(42, 64)
			state.write(one, replacement)
			read, ok := state.read(one)
			if !ok || !equalTerms(read, replacement) {
				t.Fatal("a real write after the call did not rebind the register")
			}
			(&pathExecutor{arch: tc.arch}).forgetCallerSaved(state)
			if _, ok := state.read(one); ok {
				t.Fatal("second call recovered the original entry value")
			}
		})
	}
}

func TestEntryRegisterClobberIsForkLocal(t *testing.T) {
	for _, tc := range []struct {
		arch string
		reg  Register
	}{
		{ArchRV64, Register{Class: ClassRV64X, Num: 1}},
		{ArchArm64, Register{Class: ClassX, Num: 30}},
	} {
		untouched := &symbolicState{arch: tc.arch, regs: map[int]*term{}}
		branch := untouched.clone()
		branch.clobberGPR(tc.reg.Num)
		if _, ok := branch.read(tc.reg); ok {
			t.Fatalf("%s: clobbered branch recreated entry register", tc.arch)
		}
		if _, ok := untouched.read(tc.reg); !ok {
			t.Fatalf("%s: invalidation leaked across a clone", tc.arch)
		}
		// Also clone an already-invalidated branch to ensure its provenance
		// survives future forks and does not share mutable maps.
		next := branch.clone()
		if _, ok := next.read(tc.reg); ok {
			t.Fatalf("%s: cloning removed invalidation history", tc.arch)
		}
	}
}

func TestEntryRegisterClobberJoinsConservatively(t *testing.T) {
	for _, tc := range []struct {
		arch string
		reg  Register
	}{
		{ArchRV64, Register{Class: ClassRV64X, Num: 1}},
		{ArchArm64, Register{Class: ClassX, Num: 30}},
	} {
		initial := &symbolicState{arch: tc.arch, regs: map[int]*term{}}
		a := initial.clone()
		b := initial.clone()
		// The entry value was never read on either branch. The missing
		// materialized value must not allow the join to regenerate it.
		b.clobberGPR(tc.reg.Num)
		executor := &pathExecutor{arch: tc.arch}
		joined, ok := executor.mergeTwo(constTerm(1, 1), a, b)
		if !ok {
			t.Fatalf("%s: failed to merge compatible states", tc.arch)
		}
		if _, ok := joined.read(tc.reg); ok {
			t.Fatalf("%s: path join regenerated the clobbered entry register", tc.arch)
		}
		// Repeat with the safe path first materializing the entry value.
		a = initial.clone()
		b = initial.clone()
		if _, ok := a.read(tc.reg); !ok {
			t.Fatalf("%s: entry register absent before branch", tc.arch)
		}
		b.clobberGPR(tc.reg.Num)
		joined, ok = executor.mergeTwo(constTerm(1, 1), a, b)
		if !ok {
			t.Fatalf("%s: failed to merge materialized/unbound paths", tc.arch)
		}
		if _, ok := joined.read(tc.reg); ok {
			t.Fatalf("%s: join promoted a one-sided register to an entry fact", tc.arch)
		}
	}
}
