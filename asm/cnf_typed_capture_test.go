package asm

// Retained captured-instance diagnostic. Historical capture authentication is
// unchanged and separate from the new implementation manifest in its launcher.
import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/internal/lrat"
)

const tcInput = "/workspace/shared/native-shell-evidence/fourth-timeout/final-ew-memory-capture"
const tcSnapshot = "eed691e2941ab006b24bfc22e956c68195c73e52951a9cfbb3493dc345f601b5"

type tcCaptureNode struct {
	Record, Name, Op                  string
	ID, Kind, UseWidth, DeclaredWidth int
	Cond, Left, Right                 int
	Args                              []int
	Value                             uint64
	Answer                            int
}
type tcGraph struct {
	nodes        []*term
	roots        map[string]int
	widths       map[string]int
	declarations map[string]int
	reads        []int
}
type tcBudget struct {
	visits     int
	valuations int
}

func (b *tcBudget) charge(n int) error {
	if n < 0 || n > 262144-b.visits {
		return tcErr("budget")
	}
	b.visits += n
	return nil
}
func tcErr(code string) error { return errors.New(code) }
func tcSHA(b []byte) string   { return fmt.Sprintf("%x", sha256.Sum256(b)) }
func tcRead(path string, limit int64) ([]byte, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	info, err := f.Stat()
	if err != nil || !info.Mode().IsRegular() || info.Size() > limit {
		_ = f.Close()
		return nil, tcErr("input-cap")
	}
	b, err := io.ReadAll(io.LimitReader(f, limit+1))
	err = errors.Join(err, f.Close())
	if int64(len(b)) > limit {
		return nil, tcErr("input-cap")
	}
	return b, err
}
func tcSafePath(name string) bool {
	return name != "" && !filepath.IsAbs(name) && filepath.Clean(name) == name && name != ".." && !strings.HasPrefix(name, "../")
}

func tcLoadCapture(budget *tcBudget) (*tcGraph, error) {
	manifestBytes, err := tcRead(tcInput+"/CAPTURE_SHA256.json", 1<<20)
	if err != nil || tcSHA(manifestBytes) != "87439d21d0cfef12d1f773ae47d654c4d5b7fa8d91273187c37073180ce45e14" {
		return nil, tcErr("capture-manifest")
	}
	var manifest map[string]string
	if json.Unmarshal(manifestBytes, &manifest) != nil || len(manifest) != 39 {
		return nil, tcErr("capture-manifest")
	}
	for name, hash := range manifest {
		if !tcSafePath(name) {
			return nil, tcErr("capture-path")
		}
		b, err := tcRead(filepath.Join(tcInput, name), 8<<20)
		if err != nil || tcSHA(b) != hash {
			return nil, fmt.Errorf("capture-file: %s", name)
		}
	}
	sourceBytes, err := tcRead(tcInput+"/data/source-identity.json", 1<<20)
	if err != nil {
		return nil, err
	}
	var source struct {
		Directory string            `json:"directory"`
		Files     map[string]string `json:"files_sha256"`
	}
	if json.Unmarshal(sourceBytes, &source) != nil || len(source.Files) != 17 || source.Directory != "/workspace/shared/native-shell-evidence/fourth-timeout/allocation-probe/source" {
		return nil, tcErr("historical-source-manifest")
	}
	for name, hash := range source.Files {
		if !tcSafePath(name) {
			return nil, tcErr("historical-source-path")
		}
		b, err := tcRead(filepath.Join(source.Directory, name), 8<<20)
		if err != nil || tcSHA(b) != hash {
			return nil, fmt.Errorf("historical-source-file: %s", name)
		}
	}
	dag, err := tcRead(tcInput+"/data/final-ew.dag.jsonl", 8<<20)
	if err != nil || tcSHA(dag) != "ce31540d3262ebe9a1d102478e0b8fa511fdc22426bf39e75a1354ef5f32cbf1" {
		return nil, tcErr("dag-identity")
	}
	context, err := tcRead(tcInput+"/data/final-ew.context.jsonl", (8<<20)-int64(len(dag)))
	if err != nil || tcSHA(context) != "0f2ada284d3fb6bd649da2e82b1e58ccddae5822ffa6cfd8077e92838f7aff8d" {
		return nil, tcErr("context-identity")
	}
	// Context bytes are authenticated evidence only. No context root is evaluated
	// or conjoined to a premise. Exact DAG authentication also binds every root
	// mapping and every recorded width callback, not merely the node snapshot.
	g := &tcGraph{roots: map[string]int{}, widths: map[string]int{}}
	edges, formats := 0, 0
	child := func(id int) (*term, error) {
		if id == -1 {
			return nil, nil
		}
		if id < 0 || id >= len(g.nodes) {
			return nil, tcErr("graph-shape")
		}
		return g.nodes[id], nil
	}
	for _, line := range bytes.Split(dag, []byte{'\n'}) {
		if len(line) == 0 {
			continue
		}
		var r tcCaptureNode
		if json.Unmarshal(line, &r) != nil {
			return nil, tcErr("capture-json")
		}
		if err := budget.charge(1); err != nil {
			return nil, err
		}
		switch r.Record {
		case "format":
			formats++
		case "width_callback":
			if _, duplicate := g.widths[r.Name]; duplicate || len(g.widths) >= 8192 {
				return nil, tcErr("width-inventory")
			}
			g.widths[r.Name] = r.Answer
		case "root":
			if _, duplicate := g.roots[r.Name]; duplicate {
				return nil, tcErr("root-inventory")
			}
			if r.ID < -1 || r.ID >= len(g.nodes) {
				return nil, tcErr("root-inventory")
			}
			g.roots[r.Name] = r.ID
		case "node":
			if r.ID != len(g.nodes) || len(g.nodes) >= 8192 || r.Kind < 0 || r.Kind > int(termQuant) || r.UseWidth < 1 || r.UseWidth > 64 || r.DeclaredWidth < 0 || r.DeclaredWidth > 64 || len(r.Args) > 32768-edges {
				return nil, tcErr("graph-shape")
			}
			refs := append([]int{r.Cond, r.Left, r.Right}, r.Args...)
			t := &term{kind: termKind(r.Kind), width: r.UseWidth, declared: r.DeclaredWidth, name: r.Name, value: r.Value, op: r.Op}
			for j, id := range refs {
				v, err := child(id)
				if err != nil {
					return nil, err
				}
				if id >= 0 || j >= 3 {
					edges++
					if err := budget.charge(1); err != nil {
						return nil, err
					}
				}
				switch j {
				case 0:
					t.cond = v
				case 1:
					t.left = v
				case 2:
					t.right = v
				default:
					t.args = append(t.args, v)
				}
			}
			g.nodes = append(g.nodes, t)
		default:
			return nil, tcErr("capture-record")
		}
		if edges+len(g.roots) > 32768 {
			return nil, tcErr("graph-budget")
		}
	}
	snapshot, err := g.checkedSnapshot(budget)
	if err != nil {
		return nil, err
	}
	if formats != 1 || len(g.nodes) != 4915 || edges != 6512 || len(g.roots) != 293 || len(g.widths) != 63 || snapshot != tcSnapshot {
		return nil, tcErr("capture-inventory")
	}
	for name, id := range map[string]int{"raw.premise": 104, "raw.left": 207, "raw.right": 371, "domain": 3190} {
		actual, ok := g.roots[name]
		if !ok || actual != id {
			return nil, tcErr("root-identity")
		}
	}
	return g, nil
}
func (g *tcGraph) checkedSnapshot(budget *tcBudget) (string, error) {
	// Topological order lets one walk assign identities and serialize children.
	// Charge each node and all three fixed reference lookups before allocating.
	if err := budget.charge(4 * len(g.nodes)); err != nil {
		return "", err
	}
	ids := map[*term]int{nil: -1}
	h := sha256.New()
	for i, t := range g.nodes {
		if err := budget.charge(len(t.args)); err != nil {
			return "", err
		}
		ids[t] = i
		ref := func(t *term) int {
			if id, ok := ids[t]; ok {
				return id
			}
			return -2
		}
		args := make([]int, len(t.args))
		for j, a := range t.args {
			args[j] = ref(a)
		}
		b, err := json.Marshal(tcCaptureNode{Record: "node", ID: i, Kind: int(t.kind), UseWidth: t.width, DeclaredWidth: t.declared, Name: t.name, Value: t.value, Op: t.op, Cond: ref(t.cond), Left: ref(t.left), Right: ref(t.right), Args: args})
		if err != nil {
			return "", err
		}
		_, _ = h.Write(b)
	}
	return hex.EncodeToString(h.Sum(nil)), nil
}

func tcValidateGraph(g *tcGraph, budget *tcBudget) error {
	g.declarations = map[string]int{}
	g.reads = nil
	ids := map[*term]int{}
	refs := 0
	for i, t := range g.nodes {
		if err := budget.charge(1); err != nil {
			return err
		}
		if t == nil || t.width < 1 || t.width > 64 || len(t.args) != 0 || t.value & ^mask(t.width) != 0 {
			return tcErr("graph-shape")
		}
		for _, child := range []*term{t.cond, t.left, t.right} {
			if child != nil {
				id, exists := ids[child]
				if !exists || id >= i {
					return tcErr("graph-shape")
				}
				refs++
				if refs > 32768 {
					return tcErr("budget")
				}
				if err := budget.charge(1); err != nil {
					return err
				}
			}
		}
		switch t.kind {
		case termParam:
			if t.name == "" || len(t.name) > 128 || strings.ContainsAny(t.name, "\x00\r\n") || t.declared < 1 || t.declared > 64 || t.op != "" || t.value != 0 || t.cond != nil || t.left != nil || t.right != nil {
				return tcErr("graph-shape")
			}
			if _, _, element := elementParam(t.name); element {
				return tcErr("graph-shape")
			}
			if old, exists := g.declarations[t.name]; exists && old != t.declared {
				return tcErr("graph-shape")
			}
			g.declarations[t.name] = t.declared
		case termConst:
			if t.name != "" || t.op != "" || t.declared != 0 || t.cond != nil || t.left != nil || t.right != nil {
				return tcErr("graph-shape")
			}
		case termBinary, termCmp:
			if t.name != "" || t.declared != 0 || t.value != 0 || t.cond != nil || t.left == nil || t.right == nil {
				return tcErr("graph-shape")
			}
			if t.kind == termBinary {
				switch t.op {
				case "add", "sub", "and", "or", "xor", "shl", "shr":
				default:
					return tcErr("graph-shape")
				}
			} else {
				switch t.op {
				case "eq", "ne", "lo", "hs":
				default:
					return tcErr("graph-shape")
				}
				if t.left.width != t.right.width {
					return tcErr("graph-shape")
				}
			}
		case termIte:
			if t.name != "" || t.op != "" || t.declared != 0 || t.value != 0 || t.cond == nil || t.left == nil || t.right == nil {
				return tcErr("graph-shape")
			}
		case termSelect:
			if t.name != "ew" || t.width != 32 || t.op != "" || t.declared != 0 || t.value != 0 || t.cond != nil || t.left == nil || t.left.width != 32 || t.right != nil {
				return tcErr("graph-shape")
			}
			g.reads = append(g.reads, i)
		default:
			return tcErr("graph-shape")
		}
		ids[t] = i
	}
	return nil
}
func tcRawGraph(capture *tcGraph, budget *tcBudget) (*tcGraph, error) {
	seen := map[*term]bool{}
	stack := []*term{capture.nodes[104], capture.nodes[207], capture.nodes[371]}
	for len(stack) != 0 {
		t := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if err := budget.charge(1); err != nil {
			return nil, err
		}
		if t == nil || seen[t] {
			continue
		}
		seen[t] = true
		stack = append(stack, t.cond, t.left, t.right)
		stack = append(stack, t.args...)
	}
	if len(seen) != 372 {
		return nil, tcErr("raw-reachability")
	}
	if err := budget.charge(len(capture.nodes)); err != nil {
		return nil, err
	}
	for i, t := range capture.nodes {
		if seen[t] != (i < 372) {
			return nil, tcErr("raw-node-identity")
		}
	}
	g := &tcGraph{nodes: capture.nodes[:372], roots: map[string]int{"raw.premise": 104, "raw.left": 207, "raw.right": 371}}
	if err := tcValidateGraph(g, budget); err != nil {
		return nil, err
	}
	wantDeclarations := map[string]int{"width": 32, "signed": 1, "v": 64, "le.state_at": 32, "le.bytes_at": 32, "ew[?]": 32}
	if len(g.declarations) != len(wantDeclarations) || len(g.reads) != 18 {
		return nil, tcErr("raw-inventory")
	}
	for name, width := range wantDeclarations {
		if g.declarations[name] != width {
			return nil, tcErr("raw-declarations")
		}
	}
	kinds := [6]int{}
	bits := 0
	for _, width := range g.declarations {
		bits += width
	}
	for _, t := range g.nodes {
		kinds[t.kind]++
	}
	if kinds != [6]int{31, 87, 158, 53, 25, 18} || bits != 193 {
		return nil, tcErr("raw-inventory")
	}
	return g, nil
}

func TestTypedCNFSavedCapture(t *testing.T) {
	if os.Getenv("OAK_TYPED_CNF_SAVED_CAPTURE") != "1" {
		t.Skip("retained-capture gate is explicit")
	}
	budget := new(tcBudget)
	capture, err := tcLoadCapture(budget)
	if err != nil {
		t.Fatal(err)
	}
	raw, err := tcRawGraph(capture, budget)
	if err != nil {
		t.Fatal(err)
	}
	names := make([]string, 0, len(raw.declarations))
	for name := range raw.declarations {
		names = append(names, name)
	}
	sort.Strings(names)
	p, l, r := raw.nodes[104], raw.nodes[207], raw.nodes[371]
	producer, claim, clauses := typedCNFProduce(p, l, r, names, raw.declarations)
	audited, err := checkTypedCNFImplication(context.Background(), producer, p, l, r, claim, clauses, typedCNFDiagnosticLimits)
	if err != nil {
		t.Fatal(err)
	}
	if audited.Nodes != 375 || audited.Inputs != 353 || audited.ReadBlocks != 5 || audited.Claim != 5780 || audited.Obligation != 5781 || producer.cnf.variables != 2890 || len(clauses) != 10352 {
		t.Fatalf("captured inventory: %+v", audited)
	}
	const label = "captured raw premise implies eq32; independent reads; diagnostic only"
	formula := typedCNFDIMACS(label, producer.cnf.variables, clauses)
	saved, err := tcRead("/workspace/shared/native-shell-evidence/fourth-timeout/cnf-certificate-diagnostic/data/obligation.cnf", 8<<20)
	if err != nil {
		t.Fatal(err)
	}
	if formula != string(saved) {
		t.Fatal("captured CNF bytes differ")
	}
	if tcSHA(saved) != "ca659ecd4ed22d4e5d461edb10999857acfb6a008572baee77d0bd35cacb962a" {
		t.Fatal("saved CNF identity")
	}
	proof, err := tcRead("/workspace/shared/native-shell-evidence/fourth-timeout/cnf-certificate-diagnostic/data/obligation.lrat", 8<<20)
	if err != nil {
		t.Fatal(err)
	}
	if tcSHA(proof) != "a04613d4720c24082730adedec8d3242d8dbaf1b0d9b2aeff7e6b87375197c90" {
		t.Fatal("saved proof identity")
	}
	checked, err := lrat.CheckWithLimits(context.Background(), formula, string(proof), lrat.Limits{MaxWork: 16777216, MaxStorage: 16777216, MaxCount: 16777216, MaxFormulaBytes: 8 << 20, MaxCertificateBytes: 8 << 20})
	if err != nil {
		t.Fatal(err)
	}
	if checked.Additions != 1561 || checked.Deletions != 561 {
		t.Fatalf("saved proof counts: %+v", checked)
	}
	t.Logf("typed replay: nodes=%d inputs=%d gates=%d reads=%d visits=%d CNF_SHA256=%s additions=%d deletions=%d", audited.Nodes, audited.Inputs, audited.Gates, audited.ReadBlocks, audited.Visits, tcSHA(saved), checked.Additions, checked.Deletions)
}
