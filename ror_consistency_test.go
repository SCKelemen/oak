package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"regexp"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/compiler"
)

type oakRORFixture struct {
	Name       string   `json:"name"`
	Words      []uint32 `json:"words"`
	DataTerm   uint32   `json:"data_term"`
	CountTerm  uint32   `json:"count_term"`
	RotateTerm uint32   `json:"rotate_term"`
	Bindings   []struct {
		Leaves []uint64 `json:"leaves"`
		Want   uint64   `json:"want"`
	} `json:"bindings"`
	ExpectedStatus uint32 `json:"expected_status"`
}

type oakRORTwinReceipt struct {
	Name       string      `json:"name"`
	BDDNodes   [][3]uint32 `json:"bdd_nodes"`
	BDDBits    []uint32    `json:"bdd_bits"`
	CNFNodes   [][3]uint32 `json:"cnf_nodes"`
	CNFBits    []uint32    `json:"cnf_bits"`
	CNFClauses [][]int     `json:"cnf_clauses"`
	Status     uint32      `json:"status"`
}

// Optional developer receipts retain their array format. The required lane
// accepts only a fresh receipt bound to this run, the complete source tree,
// and the exact serialized fixture bytes.
func oakRORLoadTwinReceipts(fixture []byte) ([]oakRORTwinReceipt, error) {
	path := os.Getenv("OAK_ROR_TWIN_RECEIPT")
	required := os.Getenv("OAK_REQUIRE_ROR_TWIN") == "1"
	if path == "" {
		if required {
			return nil, fmt.Errorf("OAK_REQUIRE_ROR_TWIN=1 requires a Go twin receipt path")
		}
		return nil, nil
	}
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var receipts []oakRORTwinReceipt
	if required {
		source, run := os.Getenv("OAK_ROR_TWIN_SOURCE"), os.Getenv("OAK_ROR_TWIN_RUN")
		if len(source) != 64 || len(run) != 64 {
			return nil, fmt.Errorf("required Go twin receipt needs source/run identities")
		}
		var envelope struct {
			Schema  int                 `json:"schema"`
			Source  string              `json:"source_sha256"`
			Run     string              `json:"run"`
			Fixture string              `json:"fixture_sha256"`
			Cases   []oakRORTwinReceipt `json:"cases"`
		}
		if err := json.Unmarshal(data, &envelope); err != nil {
			return nil, err
		}
		if envelope.Schema != 1 || envelope.Source != source || envelope.Run != run || envelope.Fixture != fmt.Sprintf("%x", sha256.Sum256(fixture)) {
			return nil, fmt.Errorf("stale or substituted Go twin receipt: schema/source/run/fixture mismatch")
		}
		receipts = envelope.Cases
	} else if err := json.Unmarshal(data, &receipts); err != nil {
		return nil, err
	}
	if len(receipts) != 30 {
		return nil, fmt.Errorf("incomplete Go twin receipt: got %d cases, want 30", len(receipts))
	}
	for i := range receipts {
		if len(receipts[i].BDDNodes) == 0 {
			receipts[i].BDDNodes = nil
		}
		if len(receipts[i].CNFNodes) == 0 {
			receipts[i].CNFNodes = nil
		}
		if len(receipts[i].CNFClauses) == 0 {
			receipts[i].CNFClauses = nil
		}
	}
	return receipts, nil
}

func oakRORMask(w uint32) uint64 { return ^uint64(0) >> (64 - w) }

// Independent oracle: copy each output bit from its mathematical source
// position. It does not use the scalar shift/or implementation or a barrel.
func oakRORPermutation(x, k uint64, dw, cw, w uint32) uint64 {
	x &= oakRORMask(dw) & oakRORMask(w)
	k &= oakRORMask(cw) & oakRORMask(w)
	k %= uint64(w)
	var out uint64
	for i := uint32(0); i < w; i++ {
		if x&(uint64(1)<<((uint64(i)+k)%uint64(w))) != 0 {
			out |= uint64(1) << i
		}
	}
	return out
}

func (f oakRORFixture) term(t uint32) []uint32 {
	at := 8 + f.Words[1]*65 + t*8
	return f.Words[at : at+8]
}

func (f oakRORFixture) roots() []uint32 {
	at := 8 + f.Words[1]*65 + f.Words[0]*8
	return f.Words[at : at+f.Words[2]]
}

func (f oakRORFixture) assignments(leaves []uint64) map[uint32]bool {
	set := map[uint32]bool{}
	for leaf, value := range leaves {
		at := 8 + leaf*65
		for bit := uint32(0); bit < f.Words[at]; bit++ {
			set[f.Words[at+1+int(bit)]] = value&(uint64(1)<<bit) != 0
		}
	}
	return set
}

// The fixture language is deliberately small. Other operators are rejected,
// so this checker cannot silently substitute an unsupported term result.
func (f oakRORFixture) values(t *testing.T, leaves []uint64) []uint64 {
	t.Helper()
	vals := make([]uint64, f.Words[0])
	for i := range vals {
		q := f.term(uint32(i))
		switch q[0] {
		case 0:
			vals[i] = leaves[q[3]] & oakRORMask(q[2])
		case 1:
			vals[i] = uint64(q[6]) | uint64(q[7])<<32
		case 2:
			x, k := vals[q[3]], vals[q[4]]
			switch q[1] {
			case 0:
				vals[i] = x & k & oakRORMask(q[2])
			case 9:
				vals[i] = oakRORPermutation(x, k, f.term(q[3])[2], f.term(q[4])[2], q[2])
			default:
				t.Fatalf("unsupported fixture binary %d", q[1])
			}
		case 3:
			if q[1] != 0 {
				t.Fatalf("unsupported fixture comparison %d", q[1])
			}
			if vals[q[3]] == vals[q[4]] {
				vals[i] = 1
			}
		default:
			t.Fatalf("unsupported fixture kind %d", q[0])
		}
	}
	return vals
}

func (f oakRORFixture) fails(vals []uint64) bool {
	roots := f.roots()
	for _, root := range roots[:len(roots)-1] {
		if vals[root] != 0 {
			return true
		}
	}
	return vals[roots[len(roots)-1]] != 1
}

// Include unchanged production declarations and their transitive references.
// This keeps the C-backed test independent of the full prover driver, parser,
// shell, SAT search, and native build. Source declaration boundaries are
// anchored at column zero; executable Oak bodies are never rewritten.
func oakRORSource(t *testing.T, harness string) string {
	t.Helper()
	decl := regexp.MustCompile(`(?m)^([A-Za-z_][A-Za-z_0-9]*):`)
	ident := regexp.MustCompile(`[A-Za-z_][A-Za-z_0-9]*`)
	comments := regexp.MustCompile(`(?m)//[^\n]*`)
	blocks := map[string]string{}
	var order []string
	for _, src := range []string{oakSolverSource, oakLoweringSource, oakCNFSource, oakDriverHelpersSource, oakLRATSource, oakSATSource} {
		matches := decl.FindAllStringSubmatchIndex(src, -1)
		for i, m := range matches {
			end := len(src)
			if i+1 < len(matches) {
				end = matches[i+1][0]
			}
			name := src[m[2]:m[3]]
			if _, exists := blocks[name]; exists {
				t.Fatalf("duplicate Oak declaration %s", name)
			}
			blocks[name] = src[m[0]:end]
			order = append(order, name)
		}
	}
	needed := map[string]bool{}
	var visit func(string)
	visit = func(src string) {
		for _, name := range ident.FindAllString(comments.ReplaceAllString(src, ""), -1) {
			if body, ok := blocks[name]; ok && !needed[name] {
				needed[name] = true
				visit(body)
			}
		}
	}
	visit(harness)
	var out strings.Builder
	out.WriteString("package main\nimport(\"host\")\n")
	for _, name := range order {
		if needed[name] {
			out.WriteString(blocks[name])
			out.WriteByte('\n')
		}
	}
	out.WriteString(harness)
	return out.String()
}

func oakRORReadWord(t *testing.T, in io.Reader) uint32 {
	t.Helper()
	var n uint32
	if _, err := fmt.Fscan(in, &n); err != nil {
		t.Fatalf("short or malformed Oak result: %v", err)
	}
	return n
}

func oakRORRead64(t *testing.T, in io.Reader) uint64 {
	t.Helper()
	lo := oakRORReadWord(t, in)
	return uint64(lo) | uint64(oakRORReadWord(t, in))<<32
}

func oakRORReadNodes(t *testing.T, in io.Reader) [][3]uint32 {
	t.Helper()
	n := oakRORReadWord(t, in)
	if n < 1 || n > 4096 {
		t.Fatalf("invalid Oak node count %d", n)
	}
	nodes := make([][3]uint32, n-1)
	for i := range nodes {
		for j := range nodes[i] {
			nodes[i][j] = oakRORReadWord(t, in)
		}
	}
	return nodes
}

func oakRORReadBits(t *testing.T, in io.Reader, w uint32) []uint32 {
	t.Helper()
	bits := make([]uint32, w)
	for i := range bits {
		bits[i] = oakRORReadWord(t, in)
	}
	return bits
}

func oakRORBDD(t *testing.T, nodes [][3]uint32, bits []uint32, set map[uint32]bool) uint64 {
	t.Helper()
	var word uint64
	for bit, e := range bits {
		steps := 0
		for e >= 2 {
			if int(e/2) > len(nodes) || steps > len(nodes) {
				t.Fatal("invalid/cyclic Oak BDD edge")
			}
			n := nodes[e/2-1]
			parity := e & 1
			e = n[1]
			if set[n[0]] {
				e = n[2]
			}
			e ^= parity
			steps++
		}
		word |= uint64(e) << bit
	}
	return word
}

func oakRORCNF(t *testing.T, nodes [][3]uint32, bits []uint32, set map[uint32]bool) (uint64, []bool) {
	t.Helper()
	value := make([]bool, len(nodes)+1)
	edge := func(e uint32, upper int) bool {
		if int(e/2) >= upper {
			t.Fatal("forward or invalid Oak CNF gate")
		}
		return value[e/2] != (e&1 != 0)
	}
	for i, n := range nodes {
		upper := i + 1
		switch {
		case n[0]&0x80000000 != 0:
			if edge(n[0]^0x80000000, upper) {
				value[upper] = edge(n[1], upper)
			} else {
				value[upper] = edge(n[2], upper)
			}
		case n[0]&0x40000000 != 0:
			value[upper] = set[n[0]^0x40000000]
		case n[0] == 0:
			value[upper] = edge(n[1], upper) && edge(n[2], upper)
		case n[0] == 1:
			value[upper] = edge(n[1], upper) || edge(n[2], upper)
		case n[0] == 2:
			value[upper] = edge(n[1], upper) != edge(n[2], upper)
		default:
			t.Fatalf("unknown Oak CNF key %d", n[0])
		}
	}
	var word uint64
	for bit, e := range bits {
		if edge(e, len(value)) {
			word |= uint64(1) << bit
		}
	}
	return word, value
}

func TestOakRORConsistency(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Fatal("C compiler required for the ROR consistency gate")
	}
	data, err := os.ReadFile(filepath.Join("testdata", "ror_consistency.json"))
	if err != nil {
		t.Fatal(err)
	}
	var suite struct {
		Schema int             `json:"schema"`
		Cases  []oakRORFixture `json:"cases"`
	}
	if err := json.Unmarshal(data, &suite); err != nil {
		t.Fatal(err)
	}
	if suite.Schema != 1 || len(suite.Cases) != 30 {
		t.Fatal("missing bounded ROR fixtures")
	}
	receipts, err := oakRORLoadTwinReceipts(data)
	if err != nil {
		t.Fatal(err)
	}
	harness, err := os.ReadFile(filepath.Join("testdata", "ror_consistency_harness.oak"))
	if err != nil {
		t.Fatal(err)
	}
	source := oakRORSource(t, string(harness))
	dir := t.TempDir()
	srcpath, cpath, bin := filepath.Join(dir, "ror.oak"), filepath.Join(dir, "ror.c"), filepath.Join(dir, "ror")
	if err := os.WriteFile(srcpath, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "oak.mod"), []byte("module oak.test.ror\noak 0.1.0\n"), 0600); err != nil {
		t.Fatal(err)
	}
	generated, err := compiler.New().WithPackageDir(dir).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(cpath, []byte(generated), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()
	if out, err := exec.CommandContext(ctx, cc, "-std=c99", "-O1", "-ffp-contract=off", "-o", bin, cpath, "-lm").CombinedOutput(); err != nil {
		t.Fatalf("cc: %v\n%s", err, out)
	}
	for index, f := range suite.Cases {
		if !t.Run(f.Name, func(t *testing.T) {
			w := f.term(f.RotateTerm)[2]
			dw, cw := f.term(f.DataTerm)[2], f.term(f.CountTerm)[2]
			words := append([]uint32(nil), f.Words...)
			for _, b := range f.Bindings {
				for _, value := range b.Leaves {
					words = append(words, uint32(value), uint32(value>>32))
				}
			}
			header := []uint32{uint32(len(words)), uint32(len(f.Words)), f.RotateTerm, uint32(len(f.Bindings))}
			var input bytes.Buffer
			if err := binary.Write(&input, binary.LittleEndian, append(header, words...)); err != nil {
				t.Fatal(err)
			}
			run := exec.CommandContext(ctx, bin)
			run.Stdin = &input
			out, err := run.CombinedOutput()
			if err != nil {
				t.Fatalf("Oak ROR %s (W=%d dataW=%d countW=%d): %v\n%s", f.Name, w, dw, cw, err, out)
			}
			in := bufio.NewReader(bytes.NewReader(out))
			got := oakRORTwinReceipt{Name: f.Name, Status: oakRORReadWord(t, in)}
			if got.Status != f.ExpectedStatus {
				t.Fatalf("Oak status %d, want %d", got.Status, f.ExpectedStatus)
			}
			got.BDDNodes = oakRORReadNodes(t, in)
			got.BDDBits = oakRORReadBits(t, in, w)
			nw := oakRORReadWord(t, in)
			if nw > 256 {
				t.Fatal("oversized Oak witness")
			}
			witness := map[uint32]bool{}
			for i := uint32(0); i < nw; i++ {
				witness[oakRORReadWord(t, in)] = true
			}
			pauses := oakRORReadWord(t, in)
			if f.Name == "w5_both_symbols" && pauses == 0 {
				t.Fatal("rotate never paused inside its symbolic stages")
			}
			cnfOutcome := oakRORReadWord(t, in)
			if cnfOutcome > 2 {
				t.Fatal("unsupported CNF outcome")
			}
			got.CNFNodes = oakRORReadNodes(t, in)
			got.CNFBits = oakRORReadBits(t, in, w)
			nc := oakRORReadWord(t, in)
			if nc > 16384 {
				t.Fatal("oversized Oak clause list")
			}
			got.CNFClauses = make([][]int, nc)
			for i := range got.CNFClauses {
				n := oakRORReadWord(t, in)
				if n > 64 {
					t.Fatal("oversized Oak clause")
				}
				for j := uint32(0); j < n; j++ {
					lit := oakRORReadWord(t, in)
					v := int(lit/2) + 1
					if lit&1 == 0 {
						v = -v
					}
					got.CNFClauses[i] = append(got.CNFClauses[i], v)
				}
			}
			check := func(leaves []uint64, recorded *uint64, isWitness bool) {
				t.Helper()
				vals := f.values(t, leaves)
				want := vals[f.RotateTerm]
				if recorded != nil && want != *recorded {
					t.Fatalf("fixture expected %x, independent permutation %x", *recorded, want)
				}
				set := f.assignments(leaves)
				if value := oakRORBDD(t, got.BDDNodes, got.BDDBits, set); value != want {
					t.Fatalf("BDD=%x, permutation=%x, leaves=%v", value, want, leaves)
				}
				value, gates := oakRORCNF(t, got.CNFNodes, got.CNFBits, set)
				if value != want {
					t.Fatalf("CNF=%x, permutation=%x, leaves=%v", value, want, leaves)
				}
				satisfied := true
				for _, clause := range got.CNFClauses {
					holds := false
					for _, lit := range clause {
						v := lit
						if v < 0 {
							v = -v
						}
						if v >= len(gates) {
							t.Fatal("clause variable out of range")
						}
						holds = holds || gates[v] == (lit > 0)
					}
					satisfied = satisfied && holds
				}
				fail := f.fails(vals)
				if cnfOutcome == 0 && satisfied != fail || cnfOutcome == 1 && fail || cnfOutcome == 2 && !fail {
					t.Fatalf("CNF obligation disagrees with independent roots: outcome=%d satisfied=%t failure=%t", cnfOutcome, satisfied, fail)
				}
				actual := oakRORRead64(t, in)
				x, k := oakRORRead64(t, in), oakRORRead64(t, in)
				fold := oakRORRead64(t, in)
				if actual != want || fold != want || oakRORPermutation(x, k, dw, cw, w) != want {
					t.Fatalf("runtime=%x fold=%x want=%x data=%x count=%x leaves=%v", actual, fold, want, x, k, leaves)
				}
				for _, root := range f.roots() {
					if actual := oakRORRead64(t, in); actual != vals[root] {
						t.Fatalf("runtime root %d=%x, want %x", root, actual, vals[root])
					}
				}
				construct := oakRORRead64(t, in)
				if want := oakRORPermutation(x, k, dw, cw, dw); construct != want {
					t.Fatalf("constructor=%x, permutation at data width=%x", construct, want)
				}
				if isWitness && !fail {
					t.Fatal("Oak counterexample failed independent confirmation")
				}
			}
			for _, b := range f.Bindings {
				check(b.Leaves, &b.Want, false)
			}
			if got.Status == 1 {
				leaves := make([]uint64, f.Words[1])
				for leaf := range leaves {
					at := 8 + leaf*65
					for bit := uint32(0); bit < f.Words[at]; bit++ {
						if witness[f.Words[at+1+int(bit)]] {
							leaves[leaf] |= uint64(1) << bit
						}
					}
				}
				check(leaves, nil, true)
			}
			var extra string
			if _, err := fmt.Fscan(in, &extra); err != io.EOF {
				t.Fatalf("unexpected Oak output %q (%v)", extra, err)
			}
			if len(got.BDDNodes) == 0 {
				got.BDDNodes = nil
			}
			if len(got.CNFNodes) == 0 {
				got.CNFNodes = nil
			}
			if len(got.CNFClauses) == 0 {
				got.CNFClauses = nil
			}
			if receipts != nil && !reflect.DeepEqual(got, receipts[index]) {
				t.Fatalf("Go/Oak node, gate, clause, or serialized output mismatch for %s\nOak=%+v\nGo=%+v", f.Name, got, receipts[index])
			}
		}) {
			t.FailNow()
		}
	}
}
