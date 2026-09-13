package prove

import (
	"strings"
	"testing"
)

// Guard exclusivity (docs/spec/112-protocols.md section 1): for every
// step whose lines from one state all carry guards, the prover decides
// whether the guards are pairwise disjoint — then Oak's first-line reading
// and the model checker's every-line reading coincide — and reports one
// advisory row per group, never deciding the exit status by it.
func TestGuardExclusivity(t *testing.T) {
	src := `
Quantum: protocol = {
  data { budget: u32 }
  init { budget: u32(2) }
  initial Running
  tick: Running -> Running when data.budget > u32(1) then { data.budget = data.budget - u32(1) }
  tick: Running -> Yielded when data.budget <= u32(1) then { data.budget = u32(2) }
  resume: Yielded -> Running
}
Lax: protocol = {
  data { level: u8 }
  init { level: u8(0) }
  initial Idle
  pump(amount: u8): Idle -> Busy when data.level < u8(200)
  pump(amount: u8): Idle -> Idle when amount > u8(3)
}
main: (): i32 = 0
`
	results, err := Theorems(check(t, src), 0)
	if err != nil {
		t.Fatal(err)
	}
	got := map[string]Result{}
	for _, r := range results {
		got[r.Name] = r
		if strings.Contains(r.Name, "__exclusive__") {
			t.Errorf("pair theorem %s not folded into its group", r.Name)
		}
	}
	if r := got["Quantum: guards of tick from Running"]; r.Status != Decided || !r.Advisory || !strings.Contains(r.Detail, "coincide") {
		t.Errorf("Quantum: %+v", r)
	}
	if r := got["Lax: guards of pump from Idle"]; r.Status != Refuted || !r.Advisory || !strings.Contains(r.Detail, "amount = 4") {
		t.Errorf("Lax: %+v", r)
	}
}
