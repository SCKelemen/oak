package asm

import (
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"os"
	"reflect"
	"testing"
)

type rotateConsistencyTwinCase struct {
	Name           string   `json:"name"`
	Words          []uint32 `json:"words"`
	DataTerm       int      `json:"data_term"`
	CountTerm      int      `json:"count_term"`
	RotateTerm     int      `json:"rotate_term"`
	ExpectedStatus int      `json:"expected_status"`
	Params         []struct {
		Name  string `json:"name"`
		Width int    `json:"width"`
	} `json:"params"`
	Bindings []struct {
		Leaves []uint64 `json:"leaves"`
		Want   uint64   `json:"want"`
	} `json:"bindings"`
}

type rotateConsistencyTwinReceipt struct {
	Name       string      `json:"name"`
	BDDNodes   [][3]int    `json:"bdd_nodes"`
	BDDBits    []int       `json:"bdd_bits"`
	CNFNodes   [][3]uint32 `json:"cnf_nodes"`
	CNFBits    []int       `json:"cnf_bits"`
	CNFClauses [][]int     `json:"cnf_clauses"`
	Status     int         `json:"status"`
}

func rotateConsistencyDecodeTwin(t *testing.T, fixture rotateConsistencyTwinCase) ([]*term, []*term, []string, map[string]int) {
	t.Helper()
	w := fixture.Words
	if len(w) < 8 || int(w[0]) > rotateConsistencyFixtureNodes || int(w[1]) != len(fixture.Params) || w[2] == 0 || len(w) != 8+65*int(w[1])+8*int(w[0])+int(w[2]) {
		t.Fatal("invalid serialized fixture header/length")
	}
	names, widths := make([]string, len(fixture.Params)), map[string]int{}
	for i, p := range fixture.Params {
		if p.Width < 1 || p.Width > 64 || w[8+65*i] != uint32(p.Width) {
			t.Fatal("declared width mismatch")
		}
		names[i], widths[p.Name] = p.Name, p.Width
		for bit := 0; bit < 64; bit++ {
			want := problemNone
			if bit < p.Width {
				want = uint32(bit*(len(fixture.Params)+16) + i)
			}
			if w[9+65*i+bit] != want {
				t.Fatal("fixture input variable order is not the declared interleaved order")
			}
		}
	}
	operations := map[uint32]string{}
	for name, code := range problemBinaryOps {
		operations[code] = name
	}
	terms := make([]*term, int(w[0]))
	base := 8 + 65*len(names)
	for i := range terms {
		record := w[base+8*i : base+8*i+8]
		if record[2] < 1 || record[2] > 64 {
			t.Fatal("invalid term width")
		}
		current := &term{width: int(record[2]), value: uint64(record[6]) | uint64(record[7])<<32}
		child := func(index uint32) *term {
			if index >= uint32(i) {
				t.Fatalf("term%d has non-prior child%d", i, index)
			}
			return terms[index]
		}
		switch record[0] {
		case 0:
			if int(record[3]) >= len(names) {
				t.Fatal("invalid leaf")
			}
			current.kind = termParam
			current.name = names[record[3]]
			current.declared = widths[current.name]
		case 1:
			current.kind = termConst
		case 2:
			current.kind = termBinary
			current.op = operations[record[1]]
			if current.op == "" {
				t.Fatal("unsupported fixture binary code")
			}
			current.left, current.right = child(record[3]), child(record[4])
		case 3:
			if record[1] != 0 {
				t.Fatal("fixture decoder only admits ordinary equality comparisons")
			}
			current.kind = termCmp
			current.op = "eq"
			current.left, current.right = child(record[3]), child(record[4])
		case 4:
			current.kind = termIte
			current.left, current.right, current.cond = child(record[3]), child(record[4]), child(record[5])
		default:
			t.Fatalf("unsupported fixture kind%d", record[0])
		}
		terms[i] = current
	}
	roots := make([]*term, int(w[2]))
	for i, id := range w[base+8*len(terms):] {
		if int(id) >= len(terms) {
			t.Fatal("invalid root")
		}
		roots[i] = terms[id]
	}
	return terms, roots, names, widths
}

func TestRotateConsistencySerializedTwinFixtures(t *testing.T) {
	data, err := os.ReadFile("../testdata/ror_consistency.json")
	if err != nil {
		t.Fatal(err)
	}
	var document struct {
		Schema int                         `json:"schema"`
		Cases  []rotateConsistencyTwinCase `json:"cases"`
	}
	if err = json.Unmarshal(data, &document); err != nil {
		t.Fatal(err)
	}
	if document.Schema != 1 || len(document.Cases) == 0 {
		t.Fatal("invalid or empty twin fixture schema")
	}
	receipts := make([]rotateConsistencyTwinReceipt, 0, len(document.Cases))
	for _, fixture := range document.Cases {
		if !t.Run(fixture.Name, func(t *testing.T) {
			terms, roots, names, widths := rotateConsistencyDecodeTwin(t, fixture)
			if fixture.RotateTerm < 0 || fixture.RotateTerm >= len(terms) || fixture.DataTerm < 0 || fixture.DataTerm >= len(terms) || fixture.CountTerm < 0 || fixture.CountTerm >= len(terms) {
				t.Fatal("invalid recorded operand IDs")
			}
			root := terms[fixture.RotateTerm]
			if root.op != "ror" || root.left != terms[fixture.DataTerm] || root.right != terms[fixture.CountTerm] {
				t.Fatal("serialized ROR operand identities changed")
			}
			b, c := newBlaster(names, widths), newCNFBlaster(names, widths)
			b.slots, c.slots = 16, 16
			for _, term := range terms {
				if b.blast(term) == nil || c.blast(term) == nil || b.exceeded() || c.exceeded() {
					t.Fatal("unexpected unknown in serialized fixture")
				}
			}
			if len(b.bdd.nodes) > rotateConsistencyFixtureNodes || len(c.cnf.gates) > rotateConsistencyFixtureNodes {
				t.Fatal("serialized fixture exceeded structural ceiling")
			}
			circuit := &rotateConsistencyCircuit{bdd: b, cnf: c, bddBits: b.memo[root], cnfBits: c.memo[root], assignment: map[int]bool{}, values: make([]bool, c.cnf.variables+1)}
			slots := newTermEvaluator(terms...)
			claim, traps := roots[len(roots)-1], roots[:len(roots)-1]
			counterexampleSeen := false
			for _, binding := range fixture.Bindings {
				if len(binding.Leaves) != len(names) {
					t.Fatal("binding arity mismatch")
				}
				env := map[string]uint64{}
				for i, value := range binding.Leaves {
					if value&mask(widths[names[i]]) != value {
						t.Fatal("binding exceeds declared width")
					}
					env[names[i]] = value
				}
				want := rotateConsistencyReference(root.left.eval(env), root.right.eval(env), root.width, root.left.width, root.right.width)
				if want != binding.Want {
					t.Fatalf("recorded oracle=%#x independent permutation=%#x", binding.Want, want)
				}
				rotateConsistencyCheck(t, fixture.Name, root, slots, circuit, env, want)
				bad := claim.eval(env) != 1
				for _, trap := range traps {
					bad = bad || trap.eval(env) != 0
				}
				counterexampleSeen = counterexampleSeen || bad
				cnf := CNF{claim: claim, traps: traps}
				p := serializeProblem(b, claim, traps, NodeBudget, "interleaved")
				var set []uint32
				for variable, owner := range p.Owners {
					if env[owner.Param]>>uint(owner.Bit)&1 != 0 {
						set = append(set, variable)
					}
				}
				if cnf.Confirms(env) != bad || p.Confirms(set) != bad {
					t.Fatal("serialized counterexample confirmation disagreed")
				}
			}
			// A refuted fixture must include a concrete confirming binding.
			if (fixture.ExpectedStatus == 1) != counterexampleSeen {
				t.Fatal("recorded verdict and explicit witnesses disagree")
			}
			decision, exceeded := decideBlasted(b, traps, claim, names, slots)
			status := 0
			if decision.Kind == DecisionRefuted {
				status = 1
			} else if decision.Kind != DecisionProven {
				t.Fatalf("unexpected non-decision: %v", decision)
			}
			if exceeded || status != fixture.ExpectedStatus {
				t.Fatalf("serialized verdict=%d expected=%d exceeded=%v", status, fixture.ExpectedStatus, exceeded)
			}

			// Re-serialization may renumber dependency IDs when trap roots are
			// visited first. Check exact raw terms with an explicit ID mapping.
			p := serializeProblem(b, claim, traps, NodeBudget, "interleaved")
			var ordered []*term
			ids := map[*term]uint32{}
			var visit func(*term)
			visit = func(term *term) {
				if term == nil {
					return
				}
				if _, ok := ids[term]; ok {
					return
				}
				visit(term.cond)
				visit(term.left)
				visit(term.right)
				ids[term] = uint32(len(ordered))
				ordered = append(ordered, term)
			}
			for _, r := range roots {
				visit(r)
			}
			if int(p.Words[0]) != len(ordered) || p.Terms != len(ordered) || int(p.Words[2]) != len(roots) {
				t.Fatal("serialized terms or original trap roots lost")
			}
			oldIDs := map[*term]uint32{}
			for i, term := range terms {
				oldIDs[term] = uint32(i)
			}
			base := 8 + 65*len(names)
			for newID, term := range ordered {
				old := append([]uint32(nil), fixture.Words[base+8*int(oldIDs[term]):base+8*int(oldIDs[term])+8]...)
				for _, offset := range []int{3, 4, 5} {
					if old[0] != 0 && old[offset] != problemNone {
						old[offset] = ids[terms[old[offset]]]
					}
				}
				if !reflect.DeepEqual(old, p.Words[base+8*newID:base+8*newID+8]) {
					t.Fatalf("raw term identity/width/payload changed at mapped ID%d", newID)
				}
			}
			for i, r := range roots {
				if p.Words[base+8*len(ordered)+i] != ids[r] {
					t.Fatal("root order changed")
				}
			}

			receipt := rotateConsistencyTwinReceipt{Name: fixture.Name, BDDBits: append([]int(nil), b.memo[root]...), CNFBits: append([]int(nil), c.memo[root]...), CNFClauses: c.cnf.clauses, Status: status}
			for _, node := range b.bdd.nodes[1:] {
				receipt.BDDNodes = append(receipt.BDDNodes, [3]int{node.variable, node.low, node.high})
			}
			receipt.CNFNodes = make([][3]uint32, c.cnf.variables)
			for source, dimacs := range c.cnf.inputs {
				receipt.CNFNodes[dimacs-1] = [3]uint32{0x40000000 | uint32(source), 0, 0}
			}
			for _, gate := range c.cnf.gates {
				key, low, high := uint32(gate.op), uint32(gate.x), uint32(gate.y)
				if gate.op == cnfIte {
					key, low, high = 0x80000000|uint32(gate.x), uint32(gate.y), uint32(gate.z)
				}
				receipt.CNFNodes[gate.out-1] = [3]uint32{key, low, high}
			}
			// Match cnf_obligation: append the trap-first final clause only
			// when no root makes it constant true and a nonconstant remains.
			var obligation []int
			always := false
			for i, r := range roots {
				edge := c.memo[r][0]
				if i == len(roots)-1 {
					edge ^= 1
				}
				if edge == bddTrue {
					always = true
				} else if edge != bddFalse {
					obligation = append(obligation, cnfLit(edge))
				}
			}
			if !always && len(obligation) > 0 {
				receipt.CNFClauses = append(append([][]int(nil), receipt.CNFClauses...), obligation)
			}
			receipts = append(receipts, receipt)
		}) {
			t.FailNow()
		}
	}
	// Optional cross-gate evidence only; all assertions above are mandatory
	// without it. Never emit a receipt for a failed or incomplete test run.
	if path := os.Getenv("OAK_ROR_TWIN_RECEIPT"); path != "" && !t.Failed() {
		var payload any = receipts
		if os.Getenv("OAK_REQUIRE_ROR_TWIN") == "1" {
			source, run := os.Getenv("OAK_ROR_TWIN_SOURCE"), os.Getenv("OAK_ROR_TWIN_RUN")
			if len(source) != 64 || len(run) != 64 || len(receipts) != len(document.Cases) {
				t.Fatal("required Go twin receipt needs source/run identities and every fixture")
			}
			payload = struct {
				Schema  int                            `json:"schema"`
				Source  string                         `json:"source_sha256"`
				Run     string                         `json:"run"`
				Fixture string                         `json:"fixture_sha256"`
				Cases   []rotateConsistencyTwinReceipt `json:"cases"`
			}{1, source, run, fmt.Sprintf("%x", sha256.Sum256(data)), receipts}
		}
		bytes, err := json.MarshalIndent(payload, "", "  ")
		if err != nil {
			t.Fatal(err)
		}
		if err = os.WriteFile(path, append(bytes, '\n'), 0600); err != nil {
			t.Fatal(err)
		}
	} else if os.Getenv("OAK_REQUIRE_ROR_TWIN") == "1" {
		t.Fatal("OAK_REQUIRE_ROR_TWIN=1 requires a Go twin receipt path")
	}
}
