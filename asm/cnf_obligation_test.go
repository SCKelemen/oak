package asm

import (
	"reflect"
	"testing"
)

func preparedCNFObligationBlaster(t *testing.T, names []string,
	traps []*term, claim *term) *blaster {
	t.Helper()
	widths := make(map[string]int, len(names))
	for _, name := range names {
		widths[name] = 1
	}
	bl := newCNFBlaster(names, widths)
	for index, trap := range traps {
		if bits := bl.blast(trap); len(bits) != 1 || bl.exceeded() {
			t.Fatalf("preparing trap %d produced %d bits, exceeded=%v",
				index, len(bits), bl.exceeded())
		}
	}
	if bits := bl.blast(claim); len(bits) != 1 || bl.exceeded() {
		t.Fatalf("preparing claim produced %d bits, exceeded=%v",
			len(bits), bl.exceeded())
	}
	return bl
}

func TestValidateCNFObligationAcceptsOutcomeMatrix(t *testing.T) {
	t.Run("false traps filtered and symbolic claim negated last", func(t *testing.T) {
		trap1 := paramTerm("trap1", 1)
		trap2 := paramTerm("trap2", 1)
		claim := paramTerm("claim", 1)
		traps := []*term{constTerm(0, 1), trap1, constTerm(0, 1), trap2}
		bl := preparedCNFObligationBlaster(t,
			[]string{"trap1", "trap2", "claim"}, traps, claim)
		if err := validateCNFObligation(bl, traps, claim,
			cnfObligationFormula, []int{2, 4, 7}); err != nil {
			t.Fatalf("valid formula refused: %v", err)
		}
	})

	t.Run("true claim leaves symbolic traps only", func(t *testing.T) {
		trap1 := paramTerm("trap1", 1)
		trap2 := paramTerm("trap2", 1)
		claim := constTerm(1, 1)
		traps := []*term{trap1, trap2}
		bl := preparedCNFObligationBlaster(t, []string{"trap1", "trap2"}, traps, claim)
		if err := validateCNFObligation(bl, traps, claim,
			cnfObligationFormula, []int{2, 4}); err != nil {
			t.Fatalf("valid trap-only formula refused: %v", err)
		}
	})

	t.Run("all constant false traps and true claim prove", func(t *testing.T) {
		claim := constTerm(1, 1)
		traps := []*term{constTerm(0, 1), constTerm(0, 1)}
		bl := preparedCNFObligationBlaster(t, nil, traps, claim)
		if err := validateCNFObligation(bl, traps, claim,
			cnfObligationConstantProven, nil); err != nil {
			t.Fatalf("valid constant proof refused: %v", err)
		}
	})

	t.Run("true trap settles and preserves symbolic trap audit", func(t *testing.T) {
		trap1 := paramTerm("trap1", 1)
		trap2 := paramTerm("trap2", 1)
		claim := paramTerm("claim", 1)
		traps := []*term{trap1, constTerm(1, 1), trap2}
		bl := preparedCNFObligationBlaster(t,
			[]string{"trap1", "trap2", "claim"}, traps, claim)
		if err := validateCNFObligation(bl, traps, claim,
			cnfObligationTrapAlways, []int{2, 4}); err != nil {
			t.Fatalf("valid constant-trap settlement refused: %v", err)
		}
	})

	t.Run("false claim settles after symbolic traps", func(t *testing.T) {
		trap := paramTerm("trap", 1)
		claim := constTerm(0, 1)
		traps := []*term{trap}
		bl := preparedCNFObligationBlaster(t, []string{"trap"}, traps, claim)
		if err := validateCNFObligation(bl, traps, claim,
			cnfObligationClaimFalse, []int{2}); err != nil {
			t.Fatalf("valid false-claim settlement refused: %v", err)
		}
	})

	t.Run("true trap takes precedence over false claim", func(t *testing.T) {
		trap := paramTerm("trap", 1)
		claim := constTerm(0, 1)
		traps := []*term{trap, constTerm(1, 1)}
		bl := preparedCNFObligationBlaster(t, []string{"trap"}, traps, claim)
		if err := validateCNFObligation(bl, traps, claim,
			cnfObligationTrapAlways, []int{2}); err != nil {
			t.Fatalf("valid trap precedence refused: %v", err)
		}
	})

	t.Run("duplicate and complementary traps are preserved", func(t *testing.T) {
		trap := paramTerm("trap", 1)
		negated := notTerm(trap)
		claim := constTerm(1, 1)
		traps := []*term{trap, trap, negated}
		bl := preparedCNFObligationBlaster(t, []string{"trap"}, traps, claim)
		if err := validateCNFObligation(bl, traps, claim,
			cnfObligationFormula, []int{2, 2, 3}); err != nil {
			t.Fatalf("valid repeated/complementary roots refused: %v", err)
		}
	})
}

func symbolicCNFObligationFixture(t *testing.T) (*blaster, []*term, *term) {
	t.Helper()
	trap1 := paramTerm("trap1", 1)
	trap2 := paramTerm("trap2", 1)
	claim := paramTerm("claim", 1)
	traps := []*term{trap1, trap2}
	return preparedCNFObligationBlaster(t,
		[]string{"trap1", "trap2", "claim"}, traps, claim), traps, claim
}

func TestValidateCNFObligationRefusesFormulaMutation(t *testing.T) {
	tests := []struct {
		name       string
		obligation []int
	}{
		{"missing first trap", []int{4, 7}},
		{"missing second trap", []int{2, 7}},
		{"added trap", []int{2, 4, 2, 7}},
		{"duplicated trap", []int{2, 2, 4, 7}},
		{"reordered traps", []int{4, 2, 7}},
		{"trap polarity changed", []int{3, 4, 7}},
		{"false constant leaked", []int{0, 2, 4, 7}},
		{"true constant leaked", []int{1, 2, 4, 7}},
		{"claim placed before traps", []int{7, 2, 4}},
		{"claim omitted", []int{2, 4}},
		{"claim not negated", []int{2, 4, 6}},
		{"trailing edge", []int{2, 4, 7, 2}},
		{"empty", nil},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			bl, traps, claim := symbolicCNFObligationFixture(t)
			if err := validateCNFObligation(bl, traps, claim,
				cnfObligationFormula, test.obligation); err == nil {
				t.Fatal("mutated final obligation accepted")
			}
		})
	}
}

func TestValidateCNFObligationRefusesOutcomeMutation(t *testing.T) {
	for _, outcome := range []cnfObligationOutcome{
		cnfObligationTrapAlways,
		cnfObligationClaimFalse,
		cnfObligationConstantProven,
	} {
		bl, traps, claim := symbolicCNFObligationFixture(t)
		if err := validateCNFObligation(bl, traps, claim,
			outcome, []int{2, 4, 7}); err == nil {
			t.Errorf("symbolic formula accepted as outcome %d", outcome)
		}
	}

	claim := constTerm(1, 1)
	traps := []*term{constTerm(0, 1)}
	for _, outcome := range []cnfObligationOutcome{
		cnfObligationTrapAlways,
		cnfObligationClaimFalse,
		cnfObligationFormula,
	} {
		bl := preparedCNFObligationBlaster(t, nil, traps, claim)
		if err := validateCNFObligation(bl, traps, claim, outcome, nil); err == nil {
			t.Errorf("constant proof accepted as outcome %d", outcome)
		}
	}

	trap := paramTerm("trap", 1)
	falseClaim := constTerm(0, 1)
	traps = []*term{trap}
	bl := preparedCNFObligationBlaster(t, []string{"trap"}, traps, falseClaim)
	if err := validateCNFObligation(bl, traps, falseClaim,
		cnfObligationTrapAlways, []int{2}); err == nil {
		t.Error("false claim without a true trap accepted as trap-always")
	}

	traps = []*term{trap, constTerm(1, 1)}
	bl = preparedCNFObligationBlaster(t, []string{"trap"}, traps, falseClaim)
	if err := validateCNFObligation(bl, traps, falseClaim,
		cnfObligationClaimFalse, []int{2}); err == nil {
		t.Error("true trap plus false claim accepted with the lower-precedence outcome")
	}
}

func TestValidateCNFObligationRefusesSettledRootMutation(t *testing.T) {
	t.Run("nil trap", func(t *testing.T) {
		claim := constTerm(1, 1)
		bl := newCNFBlaster(nil, nil)
		bl.blast(claim)
		if err := validateCNFObligation(bl, []*term{nil}, claim,
			cnfObligationConstantProven, nil); err == nil {
			t.Fatal("nil trap root accepted")
		}
	})

	t.Run("nil claim", func(t *testing.T) {
		trap := constTerm(0, 1)
		bl := newCNFBlaster(nil, nil)
		bl.blast(trap)
		if err := validateCNFObligation(bl, []*term{trap}, nil,
			cnfObligationConstantProven, nil); err == nil {
			t.Fatal("nil claim root accepted")
		}
	})

	t.Run("negative trap after true trap", func(t *testing.T) {
		badTrap := paramTerm("bad", 1)
		claim := constTerm(1, 1)
		traps := []*term{constTerm(1, 1), badTrap}
		bl := preparedCNFObligationBlaster(t, []string{"bad"}, traps, claim)
		bl.memo[badTrap][0] = -2
		if err := validateCNFObligation(bl, traps, claim,
			cnfObligationTrapAlways, []int{2}); err == nil {
			t.Fatal("negative trap root after settlement accepted")
		}
	})

	t.Run("negative claim after true trap", func(t *testing.T) {
		claim := paramTerm("claim", 1)
		traps := []*term{constTerm(1, 1)}
		bl := preparedCNFObligationBlaster(t, []string{"claim"}, traps, claim)
		bl.memo[claim][0] = -2
		if err := validateCNFObligation(bl, traps, claim,
			cnfObligationTrapAlways, nil); err == nil {
			t.Fatal("negative claim root after settlement accepted")
		}
	})

	t.Run("wrong-width replay", func(t *testing.T) {
		trap := paramTerm("wide", 2)
		claim := constTerm(1, 1)
		traps := []*term{trap}
		bl := newCNFBlaster([]string{"wide"}, map[string]int{"wide": 2})
		if bits := bl.blast(trap); len(bits) != 2 {
			t.Fatalf("wide preparation produced %d bits, want 2", len(bits))
		}
		bl.blast(claim)
		if err := validateCNFObligation(bl, traps, claim,
			cnfObligationFormula, []int{2}); err == nil {
			t.Fatal("multi-bit trap root accepted")
		}
	})
}

func TestExportTermCNFObligationAuditPreservesTextAndEvaluation(t *testing.T) {
	trap1 := paramTerm("trap1", 1)
	trap2 := paramTerm("trap2", 1)
	claim := paramTerm("claim", 1)
	cnf, reason, ok := exportTermCNF(
		"audited final obligation",
		[]string{"trap1", "trap2", "claim"},
		map[string]int{"trap1": 1, "trap2": 1, "claim": 1},
		claim,
		[]*term{constTerm(0, 1), trap1, constTerm(0, 1), trap2},
	)
	if !ok || reason != "" || cnf.Settled != nil {
		t.Fatalf("export = ok %v reason %q settled %#v", ok, reason, cnf.Settled)
	}
	if got, want := cnf.obligation, []int{2, 4, 7}; !reflect.DeepEqual(got, want) {
		t.Fatalf("obligation = %v, want %v", got, want)
	}
	if want := "c audited final obligation\np cnf 3 1\n1 2 -3 0\n"; cnf.Text != want {
		t.Fatalf("DIMACS = %q, want %q", cnf.Text, want)
	}
	for _, test := range []struct {
		name   string
		params map[string]uint64
		want   bool
	}{
		{"claim true and no trap", map[string]uint64{"claim": 1}, false},
		{"first trap", map[string]uint64{"trap1": 1, "claim": 1}, true},
		{"second trap", map[string]uint64{"trap2": 1, "claim": 1}, true},
		{"claim false", map[string]uint64{}, true},
	} {
		t.Run(test.name, func(t *testing.T) {
			if got := cnf.Evaluate(test.params); got != test.want {
				t.Errorf("Evaluate(%v) = %v, want %v", test.params, got, test.want)
			}
		})
	}
}

func TestExportTermCNFObligationAuditSettledOutcomes(t *testing.T) {
	check := func(t *testing.T, names []string, traps []*term, claim *term,
		wantKind DecisionKind, wantMessage string) {
		t.Helper()
		widths := make(map[string]int, len(names))
		for _, name := range names {
			widths[name] = 1
		}
		cnf, reason, ok := exportTermCNF("settled obligation", names, widths, claim, traps)
		if !ok || reason != "" {
			t.Fatalf("settled export refused: ok=%v reason=%q", ok, reason)
		}
		if cnf.Settled == nil || cnf.Settled.Kind != wantKind ||
			cnf.Settled.Message != wantMessage {
			t.Fatalf("settled = %#v, want kind %d message %q",
				cnf.Settled, wantKind, wantMessage)
		}
		if cnf.Text != "" || cnf.Clauses != 0 || len(cnf.obligation) != 0 {
			t.Fatalf("settled export emitted formula: clauses=%d obligation=%v text=%q",
				cnf.Clauses, cnf.obligation, cnf.Text)
		}
	}

	trapMessage := "the body traps on every input"
	t.Run("true trap first", func(t *testing.T) {
		check(t, []string{"trap", "claim"},
			[]*term{constTerm(1, 1), paramTerm("trap", 1)}, paramTerm("claim", 1),
			DecisionRefuted, trapMessage)
	})
	t.Run("true trap middle and false claim", func(t *testing.T) {
		check(t, []string{"trap1", "trap2"},
			[]*term{paramTerm("trap1", 1), constTerm(1, 1), paramTerm("trap2", 1)},
			constTerm(0, 1), DecisionRefuted, trapMessage)
	})
	t.Run("true trap last", func(t *testing.T) {
		check(t, []string{"trap"},
			[]*term{paramTerm("trap", 1), constTerm(1, 1)}, constTerm(1, 1),
			DecisionRefuted, trapMessage)
	})
	t.Run("false claim", func(t *testing.T) {
		check(t, []string{"trap"}, []*term{paramTerm("trap", 1)}, constTerm(0, 1),
			DecisionRefuted, "the claim is false on every input")
	})
	t.Run("constant proof", func(t *testing.T) {
		check(t, nil, []*term{constTerm(0, 1), constTerm(0, 1)}, constTerm(1, 1),
			DecisionProven, "at the bit level (the obligation is constant)")
	})
}

func TestExportTermCNFObligationAuditRefusesNilRoots(t *testing.T) {
	tests := []struct {
		name  string
		traps []*term
		claim *term
	}{
		{"nil trap", []*term{nil}, constTerm(1, 1)},
		{"nil claim", []*term{constTerm(0, 1)}, nil},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			cnf, reason, ok := exportTermCNF("nil root", nil, nil, test.claim, test.traps)
			if ok || reason == "" {
				t.Fatalf("nil root export = ok %v reason %q, want a refusal", ok, reason)
			}
			if cnf.Text != "" || cnf.Clauses != 0 || cnf.Variables != 0 ||
				cnf.Settled != nil || len(cnf.obligation) != 0 {
				t.Fatalf("refused nil root returned a partial CNF: %#v", cnf)
			}
		})
	}
}
