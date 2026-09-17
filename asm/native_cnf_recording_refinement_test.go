package asm

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"reflect"
	"sort"
	"strings"
	"testing"
)

// TestNativeCNFReplayRecordingMatchesLean projects fixed identities for Go
// term pointers and CNF keys. Those fixture-local maps are the explicit
// injectivity boundary between Go identity and the Nat identities in the
// executable recording model.
func TestNativeCNFReplayRecordingMatchesLean(t *testing.T) {
	examples := []string{"open Oak.CNFReplayCoverage"}

	t.Run("accepted sequential trace", func(t *testing.T) {
		fixture := newNativeCNFRecordingFixture()
		snapshot, err := renderNativeCNFRecordingSnapshot(fixture)
		if err != nil {
			t.Fatal(err)
		}
		examples = append(examples, "def recordingSnapshot : Snapshot := "+snapshot)

		termOrder := []int{30, 20, 30, 10}
		for _, id := range termOrder {
			roots := fixture.replay.bl.memo[fixture.terms[id]]
			if err := fixture.replay.recordTerm(fixture.terms[id], append([]int(nil), roots...)); err != nil {
				t.Fatalf("record term %d: %v", id, err)
			}
		}
		inputOrder := []int{30, 20, 30, 10}
		inputEdges := []int{4, 6, 4, 8}
		for index, source := range inputOrder {
			edge, err := fixture.replay.inputEdge(source)
			if err != nil || edge != inputEdges[index] {
				t.Fatalf("input %d = (%d, %v), want (%d, nil)", source, edge, err, inputEdges[index])
			}
		}
		gateOrder := []int{30, 20, 30, 10}
		gateEdges := []int{4, 6, 4, 8}
		for index, id := range gateOrder {
			edge, err := fixture.replay.gateEdge(fixture.gates[id])
			if err != nil || edge != gateEdges[index] {
				t.Fatalf("gate %d = (%d, %v), want (%d, nil)", id, edge, err, gateEdges[index])
			}
		}
		state, err := projectNativeCNFRecordingState(fixture)
		if err != nil {
			t.Fatal(err)
		}
		want := nativeCNFRecordingState{
			terms:  []nativeCNFRecordingTermEntry{{10, []int{8}}, {20, []int{4}}, {30, []int{2}}},
			inputs: []nativeCNFRecordingFlag{{10, true}, {20, true}, {30, true}},
			gates:  []nativeCNFRecordingFlag{{10, true}, {20, true}, {30, true}},
		}
		if !reflect.DeepEqual(state, want) {
			t.Fatalf("recorded state = %#v, want %#v", state, want)
		}
		stateLean := renderNativeCNFRecordingState(state)
		examples = append(examples,
			"example : inputEdge recordingSnapshot empty 30 = some (4, ⟨[], [30], []⟩) := by decide",
			"example : gateEdge recordingSnapshot empty 30 = some (4, ⟨[], [], [30]⟩) := by decide",
			"example : recordTerm recordingSnapshot empty 30 [2] = some ⟨[⟨30, [2]⟩], [], []⟩ := by decide",
			fmt.Sprintf("example : run recordingSnapshot %s = some %s := by decide",
				renderNativeCNFRecordingEvents(termOrder, inputOrder, gateOrder), stateLean))
	})

	t.Run("checked upserts", func(t *testing.T) {
		fixture := newNativeCNFRecordingFixture()
		fixture.replay.terms[fixture.terms[30]] = []int{99}
		if err := fixture.replay.recordTerm(fixture.terms[30], []int{2}); err != nil {
			t.Fatal(err)
		}
		if got := fixture.replay.terms[fixture.terms[30]]; !reflect.DeepEqual(got, []int{2}) {
			t.Fatalf("term upsert roots = %v, want [2]", got)
		}
		fixture.replay.inputs[30] = false
		if edge, err := fixture.replay.inputEdge(30); err != nil || edge != 4 || !fixture.replay.inputs[30] {
			t.Fatalf("input false-to-true update = (%d, %v, %t)", edge, err, fixture.replay.inputs[30])
		}
		fixture.replay.gateKeys[fixture.gates[30]] = false
		if edge, err := fixture.replay.gateEdge(fixture.gates[30]); err != nil || edge != 4 || !fixture.replay.gateKeys[fixture.gates[30]] {
			t.Fatalf("gate false-to-true update = (%d, %v, %t)", edge, err, fixture.replay.gateKeys[fixture.gates[30]])
		}
		examples = append(examples,
			"def forgedTermState : State := ⟨[⟨30, [99]⟩], [], []⟩",
			"example : recordTerm recordingSnapshot forgedTermState 30 [2] = some ⟨[⟨30, [2]⟩], [], []⟩ := by decide",
			"example : inputEdge recordingSnapshot ⟨[], [30], []⟩ 30 = some (4, ⟨[], [30], []⟩) := by decide",
			"example : gateEdge recordingSnapshot ⟨[], [], [30]⟩ 30 = some (4, ⟨[], [], [30]⟩) := by decide")
	})

	t.Run("refusals preserve prior writes", func(t *testing.T) {
		type refusalCase struct {
			name      string
			wantError string
			invoke    func(*nativeCNFRecordingFixture) (int, error)
			lean      string
		}
		cases := []refusalCase{
			{name: "missing term", wantError: "producer term memo does not contain the replayed roots", invoke: func(f *nativeCNFRecordingFixture) (int, error) {
				return 0, f.replay.recordTerm(f.terms[99], []int{2})
			}, lean: "recordTerm recordingSnapshot prefixState 99 [2] = none"},
			{name: "mismatched term roots", wantError: "producer term memo does not contain the replayed roots", invoke: func(f *nativeCNFRecordingFixture) (int, error) {
				return 0, f.replay.recordTerm(f.terms[30], []int{3})
			}, lean: "recordTerm recordingSnapshot prefixState 30 [3] = none"},
			{name: "missing input", wantError: "has no valid CNF input allocation", invoke: func(f *nativeCNFRecordingFixture) (int, error) {
				return f.replay.inputEdge(99)
			}, lean: "inputEdge recordingSnapshot prefixState 99 = none"},
			{name: "zero input output", wantError: "has no valid CNF input allocation", invoke: func(f *nativeCNFRecordingFixture) (int, error) {
				return f.replay.inputEdge(40)
			}, lean: "inputEdge recordingSnapshot prefixState 40 = none"},
			{name: "input output above variables", wantError: "has no valid CNF input allocation", invoke: func(f *nativeCNFRecordingFixture) (int, error) {
				return f.replay.inputEdge(41)
			}, lean: "inputEdge recordingSnapshot prefixState 41 = none"},
			{name: "input output above max int half", wantError: "has no valid CNF input allocation", invoke: func(f *nativeCNFRecordingFixture) (int, error) {
				return f.replay.inputEdge(42)
			}, lean: "inputEdge recordingSnapshot prefixState 42 = none"},
			{name: "missing gate", wantError: "non-folded gate has no valid exact memo entry", invoke: func(f *nativeCNFRecordingFixture) (int, error) {
				return f.replay.gateEdge(f.gates[99])
			}, lean: "gateEdge recordingSnapshot prefixState 99 = none"},
			{name: "zero gate output", wantError: "non-folded gate has no valid exact memo entry", invoke: func(f *nativeCNFRecordingFixture) (int, error) {
				return f.replay.gateEdge(f.gates[40])
			}, lean: "gateEdge recordingSnapshot prefixState 40 = none"},
			{name: "gate output above variables", wantError: "non-folded gate has no valid exact memo entry", invoke: func(f *nativeCNFRecordingFixture) (int, error) {
				return f.replay.gateEdge(f.gates[41])
			}, lean: "gateEdge recordingSnapshot prefixState 41 = none"},
			{name: "gate output above max int half", wantError: "non-folded gate has no valid exact memo entry", invoke: func(f *nativeCNFRecordingFixture) (int, error) {
				return f.replay.gateEdge(f.gates[42])
			}, lean: "gateEdge recordingSnapshot prefixState 42 = none"},
		}
		examples = append(examples, "def prefixState : State := ⟨[⟨30, [2]⟩], [30], [30]⟩")
		for _, test := range cases {
			t.Run(test.name, func(t *testing.T) {
				fixture := newNativeCNFRecordingFixture()
				seedNativeCNFRecordingPrefix(t, fixture)
				before, err := projectNativeCNFRecordingState(fixture)
				if err != nil {
					t.Fatal(err)
				}
				edge, invokeErr := test.invoke(fixture)
				if invokeErr == nil || invokeErr.Error() != test.wantError || edge != 0 {
					t.Fatalf("result = (%d, %v), want (0, %q)", edge, invokeErr, test.wantError)
				}
				after, err := projectNativeCNFRecordingState(fixture)
				if err != nil {
					t.Fatal(err)
				}
				if !reflect.DeepEqual(after, before) {
					t.Fatalf("refusal changed replay state: before=%#v after=%#v", before, after)
				}
				examples = append(examples, "example : "+test.lean+" := by decide")
			})
		}
	})

	t.Run("signed projection boundary", func(t *testing.T) {
		mutations := []struct {
			name   string
			mutate func(*nativeCNFRecordingFixture)
		}{
			{name: "negative variables", mutate: func(f *nativeCNFRecordingFixture) { f.replay.bl.cnf.variables = -1 }},
			{name: "negative max int", mutate: func(f *nativeCNFRecordingFixture) { f.replay.maxInt = -1 }},
			{name: "negative input key", mutate: func(f *nativeCNFRecordingFixture) { f.replay.bl.cnf.inputs[-1] = 2 }},
			{name: "negative input output", mutate: func(f *nativeCNFRecordingFixture) { f.replay.bl.cnf.inputs[50] = -1 }},
			{name: "negative gate output", mutate: func(f *nativeCNFRecordingFixture) { f.replay.bl.cnf.memo[f.gates[50]] = -1 }},
			{name: "negative term root", mutate: func(f *nativeCNFRecordingFixture) { f.replay.bl.memo[f.terms[30]] = []int{-1} }},
		}
		for _, test := range mutations {
			t.Run(test.name, func(t *testing.T) {
				fixture := newNativeCNFRecordingFixture()
				test.mutate(fixture)
				if _, err := renderNativeCNFRecordingSnapshot(fixture); err == nil {
					t.Fatal("signed producer field was projected to Nat")
				}
			})
		}
	})

	t.Run("identity projection is injective", func(t *testing.T) {
		fixture := newNativeCNFRecordingFixture()
		fixture.termIDs[fixture.terms[20]] = 30
		fixture.replay.terms[fixture.terms[20]] = []int{4}
		fixture.replay.terms[fixture.terms[30]] = []int{2}
		if _, err := projectNativeCNFRecordingState(fixture); err == nil {
			t.Fatal("duplicate projected term identity was accepted")
		}

		fixture = newNativeCNFRecordingFixture()
		fixture.gateIDs[fixture.gates[20]] = 30
		fixture.replay.gateKeys[fixture.gates[20]] = true
		fixture.replay.gateKeys[fixture.gates[30]] = true
		if _, err := projectNativeCNFRecordingState(fixture); err == nil {
			t.Fatal("duplicate projected gate identity was accepted")
		}
	})

	t.Run("full replay cache is stable", func(t *testing.T) {
		replay, root, err := newNativeCNFBookkeepingFixture()
		if err != nil {
			t.Fatal(err)
		}
		if _, err := replay.term(root); err != nil {
			t.Fatal(err)
		}
		before := snapshotNativeCNFReplayMaps(replay)
		if len(before.terms) != 3 || len(before.inputs) != 2 || len(before.gates) != 1 {
			t.Fatalf("full replay records terms/inputs/gates = %d/%d/%d, want 3/2/1",
				len(before.terms), len(before.inputs), len(before.gates))
		}
		if _, err := replay.term(root); err != nil {
			t.Fatal(err)
		}
		after := snapshotNativeCNFReplayMaps(replay)
		if !reflect.DeepEqual(after, before) {
			t.Fatalf("cache hit changed replay maps: before=%#v after=%#v", before, after)
		}
	})

	t.Run("recorded coverage completes", func(t *testing.T) {
		// This is an observed sequence of direct helper invocations. It is not
		// presented as a trace instrumented from nativeCNFReplay.term.
		replay, root, err := newNativeCNFBookkeepingFixture()
		if err != nil {
			t.Fatal(err)
		}
		replay.maxInt = 100
		if len(replay.bl.cnf.memo) != 1 {
			t.Fatalf("coverage gate memo has %d entries, want 1", len(replay.bl.cnf.memo))
		}
		var gate cnfKey
		for key := range replay.bl.cnf.memo {
			gate = key
		}
		fixture := &nativeCNFRecordingFixture{
			replay:  replay,
			terms:   map[int]*term{0: root, 1: root.right, 2: root.left},
			termIDs: map[*term]int{root: 0, root.right: 1, root.left: 2},
			gates:   map[int]cnfKey{0: gate},
			gateIDs: map[cnfKey]int{gate: 0},
		}
		if edge, err := replay.inputEdge(0); err != nil || edge != 2 {
			t.Fatalf("coverage input 0 = (%d, %v), want (2, nil)", edge, err)
		}
		if err := replay.recordTerm(root.left, []int{2}); err != nil {
			t.Fatal(err)
		}
		if err := replay.finish(); err == nil {
			t.Fatal("incomplete checked recording prefix passed finish")
		}
		if edge, err := replay.inputEdge(1); err != nil || edge != 4 {
			t.Fatalf("coverage input 1 = (%d, %v), want (4, nil)", edge, err)
		}
		if err := replay.recordTerm(root.right, []int{4}); err != nil {
			t.Fatal(err)
		}
		if edge, err := replay.gateEdge(gate); err != nil || edge != 6 {
			t.Fatalf("coverage gate = (%d, %v), want (6, nil)", edge, err)
		}
		if err := replay.recordTerm(root, []int{6}); err != nil {
			t.Fatal(err)
		}
		// Observe the repeated helper calls too; they must not inflate coverage.
		if _, err := replay.inputEdge(0); err != nil {
			t.Fatal(err)
		}
		if _, err := replay.gateEdge(gate); err != nil {
			t.Fatal(err)
		}
		if err := replay.recordTerm(root, []int{6}); err != nil {
			t.Fatal(err)
		}
		if err := replay.finish(); err != nil {
			t.Fatalf("complete checked recording trace: %v", err)
		}
		snapshot, err := renderNativeCNFRecordingSnapshot(fixture)
		if err != nil {
			t.Fatal(err)
		}
		start, err := renderNativeCNFReplayCoverageShape(replay.startShape)
		if err != nil {
			t.Fatal(err)
		}
		current, err := renderNativeCNFReplayCoverageShape(snapshotCNFObligationCounts(replay.bl))
		if err != nil {
			t.Fatal(err)
		}
		examples = append(examples,
			"def coverageSnapshot : Snapshot := "+snapshot,
			"def coverageStart : Shape := "+start,
			"def coverageCurrent : Shape := "+current,
			"def coverageEvents : List Event := [.input 0, .term 2 [2], .input 1, .term 1 [4], .gate 0, .term 0 [6], .input 0, .gate 0, .term 0 [6]]",
			"example : Oak.CNFReplayRecordedCoverage.check coverageSnapshot [.input 0, .term 2 [2]] coverageStart coverageCurrent = none := by decide",
			"example : (Oak.CNFReplayRecordedCoverage.check coverageSnapshot coverageEvents coverageStart coverageCurrent).isSome = true := by decide")
	})

	if t.Failed() {
		return
	}
	t.Run("kernel", func(t *testing.T) {
		runNativeCNFBookkeepingKernel(t, "Oak.CNFReplayRecordedCoverage", "Oak.CNFReplayRecording",
			"NativeCNFReplayRecordingProductionPins.lean", examples)
	})
}

// TestNativeCNFReplayRecordingMutationSites is a deliberately syntactic pin:
// it covers direct indexed writes/deletes through the nativeCNFReplay method
// receiver. It is not an alias analysis or a proof of universal control flow.
func TestNativeCNFReplayRecordingMutationSites(t *testing.T) {
	fileSet := token.NewFileSet()
	file, err := parser.ParseFile(fileSet, "native_bitwise_certificate.go", nil, 0)
	if err != nil {
		t.Fatal(err)
	}
	allowed := map[string]string{"terms": "recordTerm", "inputs": "inputEdge", "gateKeys": "gateEdge"}
	writes := map[string]int{}
	calls := map[string]map[string]bool{}
	for _, declaration := range file.Decls {
		function, ok := declaration.(*ast.FuncDecl)
		if !ok || function.Recv == nil || function.Body == nil || len(function.Recv.List) != 1 {
			continue
		}
		receiverName, ok := nativeCNFReplayReceiver(function.Recv.List[0])
		if !ok {
			continue
		}
		ast.Inspect(function.Body, func(node ast.Node) bool {
			switch node := node.(type) {
			case *ast.AssignStmt:
				for _, expression := range node.Lhs {
					index, indexed := expression.(*ast.IndexExpr)
					if !indexed {
						continue
					}
					field, direct := nativeCNFReplayReceiverField(index.X, receiverName)
					if !direct || allowed[field] == "" {
						continue
					}
					if function.Name.Name != allowed[field] {
						t.Errorf("direct %s map write occurs in %s, want only %s", field, function.Name.Name, allowed[field])
					}
					writes[field]++
				}
			case *ast.CallExpr:
				if selector, selected := node.Fun.(*ast.SelectorExpr); selected {
					if identifier, direct := selector.X.(*ast.Ident); direct && identifier.Name == receiverName {
						if calls[function.Name.Name] == nil {
							calls[function.Name.Name] = map[string]bool{}
						}
						calls[function.Name.Name][selector.Sel.Name] = true
					}
				}
				if identifier, builtin := node.Fun.(*ast.Ident); builtin && identifier.Name == "delete" && len(node.Args) > 0 {
					field, direct := nativeCNFReplayReceiverField(node.Args[0], receiverName)
					if direct && allowed[field] != "" && function.Name.Name != allowed[field] {
						t.Errorf("direct delete from %s occurs in %s, want only %s", field, function.Name.Name, allowed[field])
					}
				}
			}
			return true
		})
	}
	for field := range allowed {
		if writes[field] != 1 {
			t.Errorf("direct indexed writes to r.%s = %d, want exactly 1", field, writes[field])
		}
	}
	for caller, callee := range map[string]string{"term": "inputEdge", "apply": "gateEdge"} {
		if !calls[caller][callee] {
			t.Errorf("%s does not directly route through %s", caller, callee)
		}
	}
	if !calls["term"]["recordTerm"] {
		t.Error("term does not directly route through recordTerm")
	}
}

type nativeCNFRecordingFixture struct {
	replay  *nativeCNFReplay
	terms   map[int]*term
	termIDs map[*term]int
	gates   map[int]cnfKey
	gateIDs map[cnfKey]int
}

type nativeCNFRecordingTermEntry struct {
	id    int
	roots []int
}

type nativeCNFRecordingFlag struct {
	id    int
	value bool
}

type nativeCNFRecordingState struct {
	terms  []nativeCNFRecordingTermEntry
	inputs []nativeCNFRecordingFlag
	gates  []nativeCNFRecordingFlag
}

func newNativeCNFRecordingFixture() *nativeCNFRecordingFixture {
	// Invalid output allocations are retained deliberately: this fixture is
	// not constructor-admitted and isolates the private recording guards.
	terms := map[int]*term{
		10: constTerm(0, 1), 20: constTerm(0, 1), 30: constTerm(0, 1), 99: constTerm(0, 1),
	}
	gates := map[int]cnfKey{
		10: {op: opXor, x: 2, y: 4, z: -1},
		20: {op: opOr, x: 2, y: 4, z: -1},
		30: {op: opAnd, x: 2, y: 4, z: -1},
		40: {op: 40, x: 2, y: 4, z: -1},
		41: {op: 41, x: 2, y: 4, z: -1},
		42: {op: 42, x: 2, y: 4, z: -1},
		50: {op: 50, x: 2, y: 4, z: -1},
		99: {op: 99, x: 2, y: 4, z: -1},
	}
	bl := &blaster{
		cnf: &cnfBuilder{
			variables: 9,
			inputs:    map[int]int{10: 4, 20: 3, 30: 2, 40: 0, 41: 10, 42: 6},
			memo: map[cnfKey]int{
				gates[10]: 4, gates[20]: 3, gates[30]: 2,
				gates[40]: 0, gates[41]: 10, gates[42]: 6,
			},
		},
		memo: map[*term][]int{terms[10]: {8}, terms[20]: {4}, terms[30]: {2}},
	}
	replay := &nativeCNFReplay{
		bl: bl, terms: map[*term][]int{}, inputs: map[int]bool{}, gateKeys: map[cnfKey]bool{}, maxInt: 10,
	}
	termIDs := map[*term]int{}
	for id, term := range terms {
		termIDs[term] = id
	}
	gateIDs := map[cnfKey]int{}
	for id, key := range gates {
		gateIDs[key] = id
	}
	return &nativeCNFRecordingFixture{replay: replay, terms: terms, termIDs: termIDs, gates: gates, gateIDs: gateIDs}
}

func seedNativeCNFRecordingPrefix(t *testing.T, fixture *nativeCNFRecordingFixture) {
	t.Helper()
	if err := fixture.replay.recordTerm(fixture.terms[30], []int{2}); err != nil {
		t.Fatal(err)
	}
	if edge, err := fixture.replay.inputEdge(30); err != nil || edge != 4 {
		t.Fatalf("seed input = (%d, %v), want (4, nil)", edge, err)
	}
	if edge, err := fixture.replay.gateEdge(fixture.gates[30]); err != nil || edge != 4 {
		t.Fatalf("seed gate = (%d, %v), want (4, nil)", edge, err)
	}
}

func renderNativeCNFRecordingSnapshot(fixture *nativeCNFRecordingFixture) (string, error) {
	if fixture == nil || fixture.replay == nil || fixture.replay.bl == nil || fixture.replay.bl.cnf == nil {
		return "", fmt.Errorf("nil recording fixture")
	}
	if err := validateNativeCNFRecordingIdentities(fixture); err != nil {
		return "", err
	}
	if fixture.replay.bl.cnf.variables < 0 || fixture.replay.maxInt < 0 {
		return "", fmt.Errorf("negative snapshot scalar is outside the Nat projection")
	}
	terms := make([]nativeCNFRecordingTermEntry, 0, len(fixture.replay.bl.memo))
	seenTerms := map[int]bool{}
	for key, roots := range fixture.replay.bl.memo {
		id, known := fixture.termIDs[key]
		if !known || id < 0 || seenTerms[id] {
			return "", fmt.Errorf("term identities are missing, negative, or noninjective")
		}
		seenTerms[id] = true
		copied := append([]int(nil), roots...)
		if firstNegative(copied) {
			return "", fmt.Errorf("negative term root is outside the Nat projection")
		}
		terms = append(terms, nativeCNFRecordingTermEntry{id: id, roots: copied})
	}
	sort.Slice(terms, func(i, j int) bool { return terms[i].id < terms[j].id })
	inputs, err := renderNativeCNFRecordingAllocations(fixture.replay.bl.cnf.inputs, nil)
	if err != nil {
		return "", err
	}
	gates, err := renderNativeCNFRecordingAllocations(fixture.replay.bl.cnf.memo, fixture.gateIDs)
	if err != nil {
		return "", err
	}
	return fmt.Sprintf("⟨%s, %s, %s, %d, %d⟩", renderNativeCNFRecordingTerms(terms), inputs,
		gates, fixture.replay.bl.cnf.variables, fixture.replay.maxInt), nil
}

func renderNativeCNFRecordingAllocations[K comparable](allocations map[K]int, identities map[K]int) (string, error) {
	entries := make([][2]int, 0, len(allocations))
	seen := map[int]bool{}
	for raw, output := range allocations {
		var id int
		if identities == nil {
			projected, ok := any(raw).(int)
			if !ok {
				return "", fmt.Errorf("allocation key is not an int")
			}
			id = projected
		} else {
			var known bool
			id, known = identities[raw]
			if !known {
				return "", fmt.Errorf("allocation identity is missing")
			}
		}
		if id < 0 || output < 0 || seen[id] {
			return "", fmt.Errorf("allocation identity/output is negative or noninjective")
		}
		seen[id] = true
		entries = append(entries, [2]int{id, output})
	}
	sort.Slice(entries, func(i, j int) bool { return entries[i][0] < entries[j][0] })
	parts := make([]string, len(entries))
	for index, entry := range entries {
		parts[index] = fmt.Sprintf("(%d, %d)", entry[0], entry[1])
	}
	return "[" + strings.Join(parts, ", ") + "]", nil
}

func projectNativeCNFRecordingState(fixture *nativeCNFRecordingFixture) (nativeCNFRecordingState, error) {
	state := nativeCNFRecordingState{}
	if err := validateNativeCNFRecordingIdentities(fixture); err != nil {
		return state, err
	}
	seenTerms := map[int]bool{}
	for key, roots := range fixture.replay.terms {
		id, known := fixture.termIDs[key]
		if !known || id < 0 || seenTerms[id] || firstNegative(roots) {
			return state, fmt.Errorf("recorded term is outside the Nat identity projection")
		}
		seenTerms[id] = true
		state.terms = append(state.terms, nativeCNFRecordingTermEntry{id: id, roots: append([]int(nil), roots...)})
	}
	for source, value := range fixture.replay.inputs {
		if source < 0 {
			return state, fmt.Errorf("recorded input is outside the Nat identity projection")
		}
		state.inputs = append(state.inputs, nativeCNFRecordingFlag{id: source, value: value})
	}
	seenGates := map[int]bool{}
	for key, value := range fixture.replay.gateKeys {
		id, known := fixture.gateIDs[key]
		if !known || id < 0 || seenGates[id] {
			return state, fmt.Errorf("recorded gate is outside the Nat identity projection")
		}
		seenGates[id] = true
		state.gates = append(state.gates, nativeCNFRecordingFlag{id: id, value: value})
	}
	sort.Slice(state.terms, func(i, j int) bool { return state.terms[i].id < state.terms[j].id })
	sort.Slice(state.inputs, func(i, j int) bool { return state.inputs[i].id < state.inputs[j].id })
	sort.Slice(state.gates, func(i, j int) bool { return state.gates[i].id < state.gates[j].id })
	return state, nil
}

func validateNativeCNFRecordingIdentities(fixture *nativeCNFRecordingFixture) error {
	for name, identities := range map[string][]int{
		"term": mapValues(fixture.termIDs),
		"gate": mapValues(fixture.gateIDs),
	} {
		seen := map[int]bool{}
		for _, id := range identities {
			if id < 0 || seen[id] {
				return fmt.Errorf("%s identities are negative or noninjective", name)
			}
			seen[id] = true
		}
	}
	return nil
}

func mapValues[K comparable](entries map[K]int) []int {
	values := make([]int, 0, len(entries))
	for _, value := range entries {
		values = append(values, value)
	}
	return values
}

func snapshotNativeCNFReplayMaps(replay *nativeCNFReplay) struct {
	terms  map[*term][]int
	inputs map[int]bool
	gates  map[cnfKey]bool
} {
	state := struct {
		terms  map[*term][]int
		inputs map[int]bool
		gates  map[cnfKey]bool
	}{terms: map[*term][]int{}, inputs: map[int]bool{}, gates: map[cnfKey]bool{}}
	for key, roots := range replay.terms {
		state.terms[key] = append([]int(nil), roots...)
	}
	for key, value := range replay.inputs {
		state.inputs[key] = value
	}
	for key, value := range replay.gateKeys {
		state.gates[key] = value
	}
	return state
}

func renderNativeCNFRecordingState(state nativeCNFRecordingState) string {
	terms := renderNativeCNFRecordingTerms(state.terms)
	inputs := make([]string, len(state.inputs))
	for index, entry := range state.inputs {
		inputs[index] = fmt.Sprint(entry.id)
	}
	gates := make([]string, len(state.gates))
	for index, entry := range state.gates {
		gates[index] = fmt.Sprint(entry.id)
	}
	return fmt.Sprintf("⟨%s, [%s], [%s]⟩", terms, strings.Join(inputs, ", "), strings.Join(gates, ", "))
}

func renderNativeCNFRecordingTerms(terms []nativeCNFRecordingTermEntry) string {
	parts := make([]string, len(terms))
	for index, entry := range terms {
		roots := make([]string, len(entry.roots))
		for rootIndex, root := range entry.roots {
			roots[rootIndex] = fmt.Sprint(root)
		}
		parts[index] = fmt.Sprintf("⟨%d, [%s]⟩", entry.id, strings.Join(roots, ", "))
	}
	return "[" + strings.Join(parts, ", ") + "]"
}

func renderNativeCNFRecordingEvents(termOrder, inputOrder, gateOrder []int) string {
	events := make([]string, 0, len(termOrder)+len(inputOrder)+len(gateOrder))
	termRoots := map[int]int{10: 8, 20: 4, 30: 2}
	for _, id := range termOrder {
		events = append(events, fmt.Sprintf(".term %d [%d]", id, termRoots[id]))
	}
	for _, id := range inputOrder {
		events = append(events, fmt.Sprintf(".input %d", id))
	}
	for _, id := range gateOrder {
		events = append(events, fmt.Sprintf(".gate %d", id))
	}
	return "[" + strings.Join(events, ", ") + "]"
}

func firstNegative(values []int) bool {
	for _, value := range values {
		if value < 0 {
			return true
		}
	}
	return false
}

func nativeCNFReplayReceiver(field *ast.Field) (string, bool) {
	if len(field.Names) != 1 {
		return "", false
	}
	pointer, ok := field.Type.(*ast.StarExpr)
	if !ok {
		return "", false
	}
	typeName, ok := pointer.X.(*ast.Ident)
	return field.Names[0].Name, ok && typeName.Name == "nativeCNFReplay"
}

func nativeCNFReplayReceiverField(expression ast.Expr, receiver string) (string, bool) {
	selector, ok := expression.(*ast.SelectorExpr)
	if !ok {
		return "", false
	}
	identifier, ok := selector.X.(*ast.Ident)
	return selector.Sel.Name, ok && identifier.Name == receiver
}
