package main

import (
	"fmt"
	"math/rand"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/experiments/verification-poc/frontend"
	"github.com/SCKelemen/oak/experiments/verification-poc/internal/lrat"
)

var cases = []string{"enum", "enum-broken", "counter", "counter-broken", "wrap"}

func fixture(t *testing.T, name string) *Model {
	t.Helper()
	m, e := loadModel(filepath.Join("examples/native", name+".json"))
	if e != nil {
		t.Fatal(e)
	}
	return m
}
func readText(t *testing.T, path string) string {
	t.Helper()
	b, e := os.ReadFile(path)
	if e != nil {
		t.Fatal(e)
	}
	return string(b)
}
func TestPythonMigrationParity(t *testing.T) {
	for _, name := range cases {
		t.Run(name, func(t *testing.T) {
			m := fixture(t, name)
			base := filepath.Join("testdata/parity", name)
			var expected frontend.Document
			if e := readJSON(filepath.Join(base, "document.json"), &expected); e != nil {
				t.Fatal(e)
			}
			doc := *m.Document
			doc.SourceHash = ""
			if !reflect.DeepEqual(doc, expected) {
				t.Fatalf("native checked document differs from Python reference\nactual: %s\nexpected: %s", jsonText(doc), jsonText(expected))
			}
			files := project(m)
			for _, name := range []string{"initial.cnf", "base.cnf", "step.cnf", "initial.smt2", "base.smt2", "step.smt2", "Model.tla", "Model.cfg", "Model.lean"} {
				expected := readText(t, filepath.Join(base, name))
				if files[name] != expected {
					t.Errorf("projection parity failed: %s\nactual:\n%s\nexpected:\n%s", name, files[name], expected)
				}
			}
			var cert Certificate
			if e := readJSON(filepath.Join(base, "evidence.json"), &cert); e != nil {
				t.Fatal(e)
			}
			// Migration only: the old certificate is explicitly rebound in this
			// test, never in the CLI. Its CNF hashes and proof/trace are unchanged.
			if _, e := verify(m, &cert); e == nil {
				t.Fatal("accepted old evidence identity")
			}
			cert.Format = evidenceFormat
			cert.Digest = m.Digest
			if _, e := verify(m, &cert); e != nil {
				t.Fatalf("existing Python evidence rejected: %v", e)
			}
		})
	}
}
func complete(c *Circuit, inputs map[string]bool) map[int]bool {
	env := map[int]bool{c.One: true}
	for name, id := range c.Inputs {
		env[id] = inputs[name]
	}
	for _, g := range c.Gates {
		a, b := env[absolute(g.Args[0])] == (g.Args[0] > 0), env[absolute(g.Args[1])] == (g.Args[1] > 0)
		v := a != b
		if g.Op == "and" {
			v = a && b
		}
		if g.Op == "or" {
			v = a || b
		}
		env[g.ID] = v
	}
	return env
}
func bit(env map[int]bool, x int) bool { return env[absolute(x)] == (x > 0) }
func cnfHolds(clauses [][]int, env map[int]bool) bool {
	for _, c := range clauses {
		satisfied := false
		for _, x := range c {
			if bit(env, x) {
				satisfied = true
				break
			}
		}
		if !satisfied {
			return false
		}
	}
	return true
}
func TestGateEquivalences(t *testing.T) {
	for _, op := range []string{"and", "or", "xor"} {
		for i := 0; i < 6; i++ {
			for j := 0; j < 6; j++ {
				c := newCircuit()
				x, y := c.input("x"), c.input("y")
				ls := []int{x, -x, y, -y, c.One, -c.One}
				root := c.gate(op, ls[i], ls[j])
				for mask := 0; mask < 1<<c.Count; mask++ {
					env := map[int]bool{}
					for v := 1; v <= c.Count; v++ {
						env[v] = mask&(1<<(v-1)) != 0
					}
					if !env[c.One] {
						continue
					}
					a, b := bit(env, ls[i]), bit(env, ls[j])
					want := a != b
					if op == "and" {
						want = a && b
					}
					if op == "or" {
						want = a || b
					}
					if cnfHolds(c.Clauses, env) != (bit(env, root) == want) {
						t.Fatalf("unsound %s gate", op)
					}
				}
			}
		}
	}
}
func TestBitVectorsExhaustive(t *testing.T) {
	c := newCircuit()
	a, b := []int{}, []int{}
	for i := 0; i < 4; i++ {
		a = append(a, c.input(fmt.Sprintf("a%d", i)))
		b = append(b, c.input(fmt.Sprintf("b%d", i)))
	}
	sum, less, eq := c.add(a, b), c.less(a, b), c.equal(a, b)
	for x := 0; x < 16; x++ {
		for y := 0; y < 16; y++ {
			inputs := map[string]bool{}
			for i := 0; i < 4; i++ {
				inputs[fmt.Sprintf("a%d", i)] = x&(1<<i) != 0
				inputs[fmt.Sprintf("b%d", i)] = y&(1<<i) != 0
			}
			env := complete(c, inputs)
			n := 0
			for i, v := range sum {
				if bit(env, v) {
					n |= 1 << i
				}
			}
			if n != (x+y)&15 || bit(env, less) != (x < y) || bit(env, eq) != (x == y) || !cnfHolds(c.Clauses, env) {
				t.Fatal("bit-vector semantics mismatch", x, y)
			}
		}
	}
}
func TestByteArithmeticAllValues(t *testing.T) {
	c := newCircuit()
	a := []int{}
	for i := 0; i < 8; i++ {
		a = append(a, c.input(fmt.Sprint(i)))
	}
	plus, minus := c.add(a, c.constant(1, 8)), c.add(a, c.constant(255, 8))
	for x := 0; x < 256; x++ {
		inputs := map[string]bool{}
		for i := 0; i < 8; i++ {
			inputs[fmt.Sprint(i)] = x&(1<<i) != 0
		}
		env := complete(c, inputs)
		for i, xs := range [][]int{plus, minus} {
			n := 0
			for j, v := range xs {
				if bit(env, v) {
					n |= 1 << j
				}
			}
			want := (x + 1) & 255
			if i == 1 {
				want = (x - 1) & 255
			}
			if n != want {
				t.Fatal("byte arithmetic mismatch", x, i)
			}
		}
	}
}
func TestEncodedObligationsMatchSemantics(t *testing.T) {
	for _, name := range cases {
		m := fixture(t, name)
		states, e := m.states()
		if e != nil {
			t.Fatal(e)
		}
		if len(states) > 10 {
			all := states
			states = nil
			for _, i := range []int{0, 1, 2, 3, 4, 127, 128, 254, 255} {
				states = append(states, all[i])
			}
		}
		for _, role := range []string{"initial", "base", "step"} {
			c, root := encode(m, role)
			for _, s := range states {
				for _, target := range states {
					envs := map[string]State{"s": s, "t": target}
					inputs := map[string]bool{}
					for name := range c.Inputs {
						parts := strings.Split(name, ".")
						i := 0
						fmt.Sscan(parts[2], &i)
						v := envs[parts[0]][parts[1]]
						n := 0
						for _, f := range m.Fields {
							if f.Name != parts[1] {
								continue
							}
							if f.Type == "Bool" {
								if v.(bool) {
									n = 1
								}
							} else if f.Type == "u8" {
								n, _ = number(v)
							} else {
								for j, x := range m.Enums[f.Type] {
									if x == v {
										n = j
										break
									}
								}
							}
						}
						inputs[name] = n&(1<<i) != 0
					}
					env := complete(c, inputs)
					ini, inv := truth(m.Terms["initial"], s, target), truth(m.Terms["invariant"], s, target)
					want := ini
					if role == "base" {
						want = ini && !inv
					}
					if role == "step" {
						want = inv && truth(m.Terms["step"], s, target) && !truth(m.Terms["invariant"], target, nil)
					}
					if bit(env, root) != want || !cnfHolds(c.Clauses, env) {
						t.Fatalf("%s %s encoding mismatch", name, role)
					}
				}
			}
		}
	}
}
func TestLocalProofAndCounterexampleChecks(t *testing.T) {
	for _, name := range []string{"enum", "counter", "wrap"} {
		m := fixture(t, name)
		c, e := localProof(m)
		if e != nil {
			t.Fatal(e)
		}
		if _, e := verify(m, c); e != nil {
			t.Fatal(e)
		}
		original := c.Proofs["step"]
		c.Proofs["step"] = Proof{original.SHA, ""}
		if _, e := verify(m, c); e == nil {
			t.Fatal("accepted missing proof")
		}
		c.Proofs["step"] = Proof{"bad", original.LRAT}
		if _, e := verify(m, c); e == nil {
			t.Fatal("accepted replaced formula")
		}
	}
	for _, name := range []string{"enum-broken", "counter-broken"} {
		m := fixture(t, name)
		c, e := findTrace(m)
		if e != nil {
			t.Fatal(e)
		}
		want := 3
		if name == "counter-broken" {
			want = 5
		}
		if len(c.States) != want {
			t.Fatal("wrong shortest trace")
		}
		if _, e := verify(m, c); e != nil {
			t.Fatal(e)
		}
		c.States = []State{c.States[0], c.States[len(c.States)-1]}
		if _, e := verify(m, c); e == nil {
			t.Fatal("accepted illegal edge")
		}
	}
	if _, e := localProof(fixture(t, "enum-broken")); e == nil {
		t.Fatal("proved unsafe invariant")
	}
	if _, e := findTrace(fixture(t, "wrap")); e == nil {
		t.Fatal("found spurious counterexample")
	}
}
func TestSmallCNFSearchAgainstTruthTables(t *testing.T) {
	rng := rand.New(rand.NewSource(420))
	for iteration := 0; iteration < 100; iteration++ {
		clauses := [][]int{}
		for count := rng.Intn(8) + 1; count > 0; count-- {
			c := []int{}
			for n := rng.Intn(4); n > 0; n-- {
				lit := rng.Intn(3) + 1
				if rng.Intn(2) == 0 {
					lit = -lit
				}
				c = append(c, lit)
			}
			clauses = append(clauses, c)
		}
		var text strings.Builder
		fmt.Fprintf(&text, "p cnf 3 %d\n", len(clauses))
		for _, c := range clauses {
			for _, x := range c {
				fmt.Fprintf(&text, "%d ", x)
			}
			text.WriteString("0\n")
		}
		sat := false
		for mask := 0; mask < 8; mask++ {
			env := map[int]bool{1: mask&1 != 0, 2: mask&2 != 0, 3: mask&4 != 0}
			sat = sat || cnfHolds(clauses, env)
		}
		proof, e := localLRAT(text.String(), nil)
		if sat {
			if e == nil {
				t.Fatal("proved SAT formula")
			}
		} else {
			if e != nil {
				t.Fatal(e)
			}
			if _, e := lrat.Check(text.String(), proof); e != nil {
				t.Fatal(e)
			}
		}
	}
}
func TestSourceIdentityAndInputRejections(t *testing.T) {
	m := fixture(t, "wrap")
	cfg := m.Config
	cfg.Arithmetic = ""
	if _, e := newModel(m.Document, cfg); e == nil {
		t.Fatal("implicit arithmetic accepted")
	}
	for _, s := range []State{{"count": true}, {"count": 256}, {"count": -1}, {"count": 1, "extra": 1}} {
		if m.valid(s) == nil {
			t.Fatal("invalid byte state accepted")
		}
	}
	for _, raw := range []string{`{"format":"x","format":"y"}`, `{"unknown":true}`, `{} {}`, `{"proofs":{"base":{"cnf_sha256":"x","cnf_sha256":"y"}}}`} {
		var c Certificate
		if decode([]byte(raw), &c) == nil {
			t.Fatal("invalid JSON accepted", raw)
		}
	}
	dir := t.TempDir()
	source := readText(t, "examples/native/enum.oak")
	cfg = fixture(t, "enum").Config
	if e := os.WriteFile(filepath.Join(dir, "enum.oak"), []byte(source+"\n// identity changed\n"), 0644); e != nil {
		t.Fatal(e)
	}
	if e := os.WriteFile(filepath.Join(dir, "enum.json"), []byte(jsonText(cfg)), 0644); e != nil {
		t.Fatal(e)
	}
	changed, e := loadModel(filepath.Join(dir, "enum.json"))
	if e != nil {
		t.Fatal(e)
	}
	original := fixture(t, "enum")
	cert, e := localProof(original)
	if e != nil {
		t.Fatal(e)
	}
	if _, e := verify(changed, cert); e == nil {
		t.Fatal("accepted stale source evidence")
	}
}
func TestSyntheticTraceImports(t *testing.T) {
	m := fixture(t, "counter-broken")
	bound := 5
	query, e := bmc(m, bound, true)
	if e != nil {
		t.Fatal(e)
	}
	pairs := []string{}
	for i := 0; i <= bound; i++ {
		pairs = append(pairs, fmt.Sprintf("(s%d_f_count #x%02x)", i, i))
	}
	raw := "sat\n(" + strings.Join(pairs, " ") + ")\n"
	r := receipt(m, "z3", query, raw, &bound)
	cert, e := importTrace(m, "z3", query, raw, r, &bound)
	if e != nil || len(cert.States) != 5 {
		t.Fatal("Z3 trace import failed", e)
	}
	if _, e := importTrace(m, "z3", query, raw+" ", r, &bound); e == nil {
		t.Fatal("accepted stale output")
	}
	bad := strings.Replace(raw, "#x02", "#xff", 1)
	if _, e := importTrace(m, "z3", query, bad, receipt(m, "z3", query, bad, &bound), &bound); e == nil {
		t.Fatal("accepted forged transition")
	}
	for _, bad := range []string{"unknown", strings.Replace(raw, "#x00", "#b0", 1), strings.Replace(raw, "s1_f_count", "s0_f_count", 1)} {
		if _, e := fromZ3(m, bad, bound); e == nil {
			t.Fatal("accepted malformed SMT trace")
		}
	}
	m = fixture(t, "enum-broken")
	trace, e := findTrace(m)
	if e != nil {
		t.Fatal(e)
	}
	entries := []any{}
	for i, s := range trace.States {
		entries = append(entries, []any{i + 1, map[string]any{"state": map[string]any{"f_phase": "Phase." + s["phase"].(string)}}})
	}
	raw = jsonText(map[string]any{"vars": []string{"state"}, "counterexample": map[string]any{"state": entries, "action": []any{}}})
	files := project(m)
	query = files["Model.tla"] + "\n" + files["Model.cfg"]
	cert, e = importTrace(m, "tlc", query, raw, receipt(m, "tlc", query, raw, nil), nil)
	if e != nil || len(cert.States) != 3 {
		t.Fatal("TLC import failed", e)
	}
	if _, e := fromTLC(m, strings.Replace(raw, "Phase.Idle", "Other.Idle", 1)); e == nil {
		t.Fatal("accepted wrong enum")
	}
}
func TestBackendFailsClosed(t *testing.T) {
	m := fixture(t, "enum")
	for _, r := range []Execution{{Stdout: "sat"}, {ExitCode: ptr(0), Stdout: "unknown\n"}, {ExitCode: ptr(1), Stdout: "sat\n"}} {
		fake := func([]string, string, time.Duration) Execution { return r }
		result := runBackend(m, "z3", t.TempDir(), true, 3, time.Second, "", fake)
		if result.Passed {
			t.Fatal("accepted unknown or failed tool")
		}
	}
	t.Setenv("PATH", t.TempDir())
	if probe("z3", t.TempDir(), "", time.Second).Available {
		t.Fatal("accepted missing tool")
	}
	if versionMatches("z3", "Z3 4.13.40") || !versionMatches("z3", "Z3 version 4.13.4 - 64 bit") {
		t.Fatal("version matching error")
	}
}
func ptr(n int) *int { return &n }
func TestSlowTool(t *testing.T) {
	if len(os.Args) > 1 && os.Args[len(os.Args)-1] == "slow-tool-helper" {
		time.Sleep(time.Second)
	}
}
func TestToolTimeout(t *testing.T) {
	r := execute([]string{os.Args[0], "-test.run=^TestSlowTool$", "--", "slow-tool-helper"}, t.TempDir(), 20*time.Millisecond)
	if r.ExitCode != nil || r.Error == "" {
		t.Fatal("timeout reported as tool result")
	}
}
func TestCLIAndMalformedImport(t *testing.T) {
	out := filepath.Join(t.TempDir(), "proof.json")
	if _, e := command([]string{"prove-local", "--out", out, "examples/native/enum.json"}); e != nil {
		t.Fatal(e)
	}
	if _, e := command([]string{"verify", "examples/native/enum.json", out}); e != nil {
		t.Fatal(e)
	}
	if _, e := command([]string{"verify", "examples/native/enum-broken.json", out}); e == nil {
		t.Fatal("CLI accepted mismatched evidence")
	}
	if _, e := command([]string{"emit", "examples/native/enum.json"}); e == nil {
		t.Fatal("missing output accepted")
	}
}
func TestBooleanAndNonPowerOfTwoEnumDomains(t *testing.T) {
	for _, test := range []struct {
		name, source    string
		invalidEncoding bool
	}{
		{"boolean", `State: type = { flag: Bool }
initial: (s: State): Bool = !s.flag
safe: (s: State): Bool = !s.flag
step: (s: State, t: State): Bool = t.flag == s.flag
`, false},
		{"enum3", `E: type = | A | B | C
State: type = { mode: E }
initial: (s: State): Bool = true
safe: (s: State): Bool = false
step: (s: State, t: State): Bool = true
`, true},
	} {
		t.Run(test.name, func(t *testing.T) {
			dir := t.TempDir()
			cfg := Config{Source: "model.oak", Initial: "initial", Step: "step", Invariant: "safe"}
			if e := os.WriteFile(filepath.Join(dir, "model.oak"), []byte(test.source), 0644); e != nil {
				t.Fatal(e)
			}
			if e := os.WriteFile(filepath.Join(dir, "model.json"), []byte(jsonText(cfg)), 0644); e != nil {
				t.Fatal(e)
			}
			m, e := loadModel(filepath.Join(dir, "model.json"))
			if e != nil {
				t.Fatal(e)
			}
			if !test.invalidEncoding {
				proof, e := localProof(m)
				if e != nil {
					t.Fatal(e)
				}
				if _, e := verify(m, proof); e != nil {
					t.Fatal(e)
				}
				return
			}
			c, root := encode(m, "base")
			for n := 0; n < 4; n++ {
				inputs := map[string]bool{}
				for key := range c.Inputs {
					parts := strings.Split(key, ".")
					i := 0
					fmt.Sscan(parts[2], &i)
					inputs[key] = n&(1<<i) != 0
				}
				env := complete(c, inputs)
				if bit(env, root) != (n < 3) {
					t.Fatal("invalid enum bit pattern admitted", n)
				}
			}
		})
	}
}
func TestOriginalBooleanModelsUseNativeOak(t *testing.T) {
	safe, e := loadModel("examples/borrow.json")
	if e != nil {
		t.Fatal(e)
	}
	proof, e := localProof(safe)
	if e != nil {
		t.Fatal(e)
	}
	if _, e := verify(safe, proof); e != nil {
		t.Fatal(e)
	}
	broken, e := loadModel("examples/broken.json")
	if e != nil {
		t.Fatal(e)
	}
	trace, e := findTrace(broken)
	if e != nil {
		t.Fatal(e)
	}
	if len(trace.States) != 3 {
		t.Fatal("Boolean model trace changed")
	}
	if _, e := verify(broken, trace); e != nil {
		t.Fatal(e)
	}
}
func TestClosedSetsPreserveReachableSafetyCapability(t *testing.T) {
	m := fixture(t, "counter")
	cert, e := closedSet(m)
	if e != nil {
		t.Fatal(e)
	}
	if _, e := verify(m, cert); e != nil {
		t.Fatal(e)
	}
	original := cert.States
	cert.States = original[:len(original)-1]
	if _, e := verify(m, cert); e == nil {
		t.Fatal("accepted omitted successor")
	}
	cert.States = append(append([]State{}, original...), State{"count": 4})
	if _, e := verify(m, cert); e == nil {
		t.Fatal("accepted unsafe member")
	}
	cert.States = append(append([]State{}, original...), original[0])
	if _, e := verify(m, cert); e == nil {
		t.Fatal("accepted duplicate state")
	}
	cert.States = original[1:]
	if _, e := verify(m, cert); e == nil {
		t.Fatal("accepted omitted initial state")
	}
	source := `State: type = { count: u8 }
initial: (s: State): Bool = s.count == u8(0)
safe: (s: State): Bool = s.count <= u8(3)
step: (s: State, t: State): Bool = s.count ? {
  | 0 => t.count == u8(0)
  | _ => true
}
`
	dir := t.TempDir()
	cfg := Config{Source: "model.oak", Initial: "initial", Step: "step", Invariant: "safe"}
	if e := os.WriteFile(filepath.Join(dir, "model.oak"), []byte(source), 0644); e != nil {
		t.Fatal(e)
	}
	if e := os.WriteFile(filepath.Join(dir, "model.json"), []byte(jsonText(cfg)), 0644); e != nil {
		t.Fatal(e)
	}
	m, e = loadModel(filepath.Join(dir, "model.json"))
	if e != nil {
		t.Fatal(e)
	}
	if _, e := localProof(m); e == nil {
		t.Fatal("proved noninductive invariant")
	}
	cert, e = closedSet(m)
	if e != nil {
		t.Fatal(e)
	}
	if len(cert.States) != 1 {
		t.Fatal("wrong reachable closure")
	}
	if _, e := verify(m, cert); e != nil {
		t.Fatal(e)
	}
	out := filepath.Join(dir, "closure.json")
	if _, e := command([]string{"closed-set", "--out", out, filepath.Join(dir, "model.json")}); e != nil {
		t.Fatal(e)
	}
	if _, e := command([]string{"verify", filepath.Join(dir, "model.json"), out}); e != nil {
		t.Fatal(e)
	}
}
