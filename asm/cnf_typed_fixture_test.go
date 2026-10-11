package asm

// This supplied-instance fixture is a diagnostic regression gate. It has no
// authority to admit compiler results or to establish a Go-to-Lean refinement.
import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"testing"
	"unicode/utf8"

	"github.com/SCKelemen/oak/internal/lrat"
)

const (
	typedFixtureDirectory   = "testdata/typed_cnf"
	typedFixtureSHA256      = "28a4a236698433c45989a24a402908ff81debd6230161154dcc3fec2e10299e9"
	typedFixtureNodesSHA256 = "21abfe4ad490408de1460361d8c8d0e89c37ceb1dd4d4b0e317bb9066eff9366"
	typedFixtureCNFSHA256   = "ca659ecd4ed22d4e5d461edb10999857acfb6a008572baee77d0bd35cacb962a"
	typedFixtureProofSHA256 = "3d189c4e459438315c2bef4485ae81dda1ad4c2e931a5ff6879c910fcbde66c4"
	typedFixtureFormat      = "oak-typed-cnf-fixture-v1"
	typedFixtureProfile     = "raw-implication-independent-ew-reads-v1"
	typedFixtureLabel       = "captured raw premise implies eq32; independent reads; diagnostic only"
	typedFixtureSourceCap   = 8 << 20
)

type typedFixtureDeclaration struct {
	Name  string `json:"name"`
	Width int    `json:"width"`
}

func typedFixtureDeclarations() []typedFixtureDeclaration {
	return []typedFixtureDeclaration{{"ew[?]", 32}, {"le.bytes_at", 32}, {"le.state_at", 32}, {"signed", 1}, {"v", 64}, {"width", 32}}
}

type typedFixture struct {
	graph       *tcGraph
	formula     string
	certificate string
}

// Decode an exact object schema before decoding typed values. encoding/json's
// ordinary struct decoding alone accepts duplicate and case-folded field names,
// omitted zero-valued fields and null values. None is part of this format.
func typedFixtureObject(data []byte, fields []string, into any) error {
	if len(data) == 0 || len(data) > 4096 || !utf8.Valid(data) {
		return errors.New("fixture JSON byte cap or UTF-8")
	}
	d := json.NewDecoder(bytes.NewReader(data))
	start, err := d.Token()
	if err != nil || start != json.Delim('{') {
		return errors.New("fixture JSON must be an object")
	}
	want := make(map[string]bool, len(fields))
	for _, name := range fields {
		want[name] = false
	}
	for d.More() {
		key, err := d.Token()
		if err != nil {
			return err
		}
		name, ok := key.(string)
		seen, known := want[name]
		if !ok || !known || seen {
			return errors.New("duplicate or unknown fixture field")
		}
		var value json.RawMessage
		if err := d.Decode(&value); err != nil {
			return err
		}
		if bytes.Equal(bytes.TrimSpace(value), []byte("null")) {
			return errors.New("null fixture field")
		}
		want[name] = true
	}
	end, err := d.Token()
	if err != nil || end != json.Delim('}') {
		return errors.New("unterminated fixture object")
	}
	for _, seen := range want {
		if !seen {
			return errors.New("missing fixture field")
		}
	}
	var extra json.RawMessage
	if err := d.Decode(&extra); err != io.EOF {
		return errors.New("trailing fixture JSON")
	}
	return json.Unmarshal(data, into)
}

func typedFixtureManifest(data []byte) error {
	var m struct {
		Format            string            `json:"format"`
		Profile           string            `json:"profile"`
		Roots             json.RawMessage   `json:"roots"`
		Declarations      []json.RawMessage `json:"declarations"`
		NodesSHA256       string            `json:"nodes_sha256"`
		CNFSHA256         string            `json:"cnf_sha256"`
		CertificateSHA256 string            `json:"certificate_sha256"`
	}
	fields := []string{"format", "profile", "roots", "declarations", "nodes_sha256", "cnf_sha256", "certificate_sha256"}
	if err := typedFixtureObject(data, fields, &m); err != nil {
		return err
	}
	if m.Format != typedFixtureFormat || m.Profile != typedFixtureProfile || m.NodesSHA256 != typedFixtureNodesSHA256 || m.CNFSHA256 != typedFixtureCNFSHA256 || m.CertificateSHA256 != typedFixtureProofSHA256 {
		return errors.New("unsupported fixture profile or identity")
	}
	var roots struct {
		Premise int `json:"premise"`
		Left    int `json:"left"`
		Right   int `json:"right"`
	}
	if err := typedFixtureObject(m.Roots, []string{"premise", "left", "right"}, &roots); err != nil {
		return err
	}
	if roots.Premise != 104 || roots.Left != 207 || roots.Right != 371 {
		return errors.New("fixture root identity")
	}
	declarations := typedFixtureDeclarations()
	if len(m.Declarations) != len(declarations) {
		return errors.New("fixture declaration count")
	}
	for i, raw := range m.Declarations {
		var declaration typedFixtureDeclaration
		if err := typedFixtureObject(raw, []string{"name", "width"}, &declaration); err != nil {
			return err
		}
		if declaration != declarations[i] {
			return errors.New("fixture declarations must be exact and sorted")
		}
	}
	return nil
}

type typedFixtureNode struct {
	ID       int    `json:"id"`
	Kind     int    `json:"kind"`
	Width    int    `json:"width"`
	Declared int    `json:"declared"`
	Cond     int    `json:"cond"`
	Left     int    `json:"left"`
	Right    int    `json:"right"`
	Value    uint64 `json:"value"`
	Name     string `json:"name"`
	Op       string `json:"op"`
	Args     []int  `json:"args"`
}

func typedFixtureDecodeNode(data []byte) (typedFixtureNode, error) {
	var node typedFixtureNode
	err := typedFixtureObject(data, []string{"id", "kind", "width", "declared", "cond", "left", "right", "value", "name", "op", "args"}, &node)
	return node, err
}

func typedFixtureGraph(data []byte) (*tcGraph, error) {
	if len(data) == 0 || len(data) > 64<<10 || !utf8.Valid(data) || data[len(data)-1] != '\n' {
		return nil, errors.New("fixture node text cap, UTF-8 or final newline")
	}
	lines := bytes.Split(data[:len(data)-1], []byte{'\n'})
	if len(lines) != 372 {
		return nil, errors.New("fixture node count")
	}
	g := &tcGraph{nodes: make([]*term, 0, 372)}
	budget := new(tcBudget)
	for i, line := range lines {
		if len(line) == 0 || len(line) > 1024 {
			return nil, errors.New("fixture node line cap")
		}
		n, err := typedFixtureDecodeNode(line)
		if err != nil {
			return nil, fmt.Errorf("fixture node %d: %w", i, err)
		}
		if n.ID != i || n.Kind < int(termParam) || n.Kind > int(termSelect) || n.Width < 1 || n.Width > 64 || n.Declared < 0 || n.Declared > 64 || len(n.Args) != 0 || len(n.Name) > 128 || len(n.Op) > 8 {
			return nil, errors.New("fixture node shape")
		}
		if err := budget.charge(4); err != nil {
			return nil, err
		}
		children := [3]*term{}
		for j, id := range []int{n.Cond, n.Left, n.Right} {
			if id < -1 || id >= i {
				return nil, errors.New("fixture node topology")
			}
			if id != -1 {
				children[j] = g.nodes[id]
			}
		}
		// Allocate once per record, even when two records have identical syntax.
		g.nodes = append(g.nodes, &term{kind: termKind(n.Kind), width: n.Width, declared: n.Declared, name: n.Name, op: n.Op, value: n.Value, cond: children[0], left: children[1], right: children[2]})
	}
	// This helper traverses only these in-memory nodes; it never loads historical
	// capture files. It checks exact 0..371 reachability, shape, widths, the six
	// declarations, 18 reads, 193 declared bits and the per-kind inventory.
	raw, err := tcRawGraph(g, budget)
	if err != nil {
		return nil, err
	}
	if raw.nodes[104].width != 1 || raw.nodes[207].width != 32 || raw.nodes[371].width != 32 {
		return nil, errors.New("fixture root width")
	}
	return raw, nil
}

func typedFixtureRead(directory, name string, capBytes int64, wantSize int, wantSHA256 string) ([]byte, error) {
	path := filepath.Join(directory, name)
	before, err := os.Lstat(path)
	if err != nil {
		return nil, err
	}
	if !before.Mode().IsRegular() || before.Size() > capBytes || before.Size() != int64(wantSize) {
		return nil, errors.New("fixture file type, size or cap")
	}
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	after, statErr := f.Stat()
	if statErr != nil || !os.SameFile(before, after) {
		return nil, errors.Join(errors.New("fixture file changed"), statErr, f.Close())
	}
	data, readErr := io.ReadAll(io.LimitReader(f, capBytes+1))
	if err := errors.Join(readErr, f.Close()); err != nil {
		return nil, err
	}
	if len(data) != wantSize || int64(len(data)) > capBytes || tcSHA(data) != wantSHA256 {
		return nil, errors.New("fixture file identity or cap")
	}
	return data, nil
}

func loadTypedCNFFixture(directory string) (*typedFixture, error) {
	info, err := os.Lstat(directory)
	if err != nil || !info.IsDir() {
		return nil, errors.Join(errors.New("fixture directory missing or not a directory"), err)
	}
	manifest, err := typedFixtureRead(directory, "fixture.json", 4096, 789, typedFixtureSHA256)
	if err != nil {
		return nil, err
	}
	if err := typedFixtureManifest(manifest); err != nil {
		return nil, err
	}
	nodes, err := typedFixtureRead(directory, "nodes.jsonl", 64<<10, 43172, typedFixtureNodesSHA256)
	if err != nil {
		return nil, err
	}
	graph, err := typedFixtureGraph(nodes)
	if err != nil {
		return nil, err
	}
	formula, err := typedFixtureRead(directory, "raw.cnf", 256<<10, 164134, typedFixtureCNFSHA256)
	if err != nil {
		return nil, err
	}
	certificate, err := typedFixtureRead(directory, "raw.lrat", 512<<10, 478063, typedFixtureProofSHA256)
	if err != nil {
		return nil, err
	}
	return &typedFixture{graph: graph, formula: string(formula), certificate: string(certificate)}, nil
}

// Success requires both exact independently replayed CNF and a complete bounded
// LRAT check. Any error, partial checker counters or cancellation returns no audit.
func checkTypedCNFFixture(ctx context.Context, fixture *typedFixture) (typedCNFAudit, error) {
	if ctx == nil || fixture == nil || fixture.graph == nil {
		return typedCNFAudit{}, errors.New("missing fixture or context")
	}
	if err := ctx.Err(); err != nil {
		return typedCNFAudit{}, err
	}
	raw := fixture.graph
	if len(raw.nodes) != 372 {
		return typedCNFAudit{}, errors.New("fixture graph inventory")
	}
	names := make([]string, 0, 6)
	for _, declaration := range typedFixtureDeclarations() {
		names = append(names, declaration.Name)
	}
	p, l, r := raw.nodes[104], raw.nodes[207], raw.nodes[371]
	producer, claim, clauses := typedCNFProduce(p, l, r, names, raw.declarations)
	audit, err := checkTypedCNFImplication(ctx, producer, p, l, r, claim, clauses, typedCNFLimits{Nodes: 375, Visits: 4194304, Gates: 2537, Variables: 2890})
	if err != nil {
		return typedCNFAudit{}, err
	}
	if audit.Nodes != 375 || audit.Inputs != 353 || audit.Gates != 2537 || audit.ReadBlocks != 5 || audit.Claim != 5780 || audit.Obligation != 5781 || producer.cnf.variables != 2890 || len(clauses) != 10352 {
		return typedCNFAudit{}, errors.New("fixture replay inventory")
	}
	formula := typedCNFDIMACS(typedFixtureLabel, producer.cnf.variables, clauses)
	if formula != fixture.formula || tcSHA([]byte(formula)) != typedFixtureCNFSHA256 || tcSHA([]byte(fixture.certificate)) != typedFixtureProofSHA256 {
		return typedCNFAudit{}, errors.New("fixture CNF or proof bytes differ")
	}
	checked, err := lrat.CheckWithLimits(ctx, formula, fixture.certificate, lrat.Limits{MaxWork: 16777216, MaxStorage: 16777216, MaxCount: 16777216, MaxFormulaBytes: 8 << 20, MaxCertificateBytes: 8 << 20})
	if err != nil {
		return typedCNFAudit{}, err
	}
	if checked.Additions != 5409 || checked.Deletions != 6163 {
		return typedCNFAudit{}, errors.New("fixture complete proof inventory")
	}
	if err := ctx.Err(); err != nil {
		return typedCNFAudit{}, err
	}
	return audit, nil
}

func TestTypedCNFDurableFixture(t *testing.T) {
	fixture, err := loadTypedCNFFixture(typedFixtureDirectory)
	if err != nil {
		t.Fatal(err)
	}
	audit, err := checkTypedCNFFixture(t.Context(), fixture)
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("durable supplied instance: nodes=%d inputs=%d gates=%d reads=%d visits=%d CNF_SHA256=%s LRAT_SHA256=%s additions=5409 deleted_ids=6163 final_empty_id=15761", audit.Nodes, audit.Inputs, audit.Gates, audit.ReadBlocks, audit.Visits, typedFixtureCNFSHA256, typedFixtureProofSHA256)
}
