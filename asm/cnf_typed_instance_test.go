package asm

// Portable writer for the bounded supplied-instance proof pipeline. Generated
// Lean remains an output artifact; this test does not change compiler admission.
import (
	"fmt"
	"io"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"testing"
)

type typedInstanceWriter struct {
	directory string
	bytes     int
	files     []string
}

func (w *typedInstanceWriter) save(name, source string) error {
	if filepath.Base(name) != name || filepath.Ext(name) != ".lean" {
		return fmt.Errorf("invalid instance source name")
	}
	if len(source) > typedFixtureSourceCap || w.bytes > typedFixtureSourceCap-len(source) {
		return fmt.Errorf("aggregate instance source cap")
	}
	path := filepath.Join(w.directory, name)
	file, err := os.OpenFile(path, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0600)
	if err != nil {
		return err
	}
	n, err := file.WriteString(source)
	if err == nil && n != len(source) {
		err = io.ErrShortWrite
	}
	closeErr := file.Close()
	if err != nil {
		return err
	}
	if closeErr != nil {
		return closeErr
	}
	w.bytes += len(source)
	w.files = append(w.files, name)
	return nil
}
func typedInstanceRoots(bits []int) string {
	out := make([]string, len(bits))
	for i, bit := range bits {
		if bit < 0 {
			panic("negative checked edge")
		}
		out[i] = strconv.Itoa(bit)
	}
	return "[" + strings.Join(out, ", ") + "]"
}
func TestTypedCNFEmitInstance(t *testing.T) {
	root, explicit := os.LookupEnv("OAK_TYPED_CNF_INSTANCE_OUT")
	if !explicit {
		root = filepath.Join(t.TempDir(), "TypedCNFInstance")
	}
	if !filepath.IsAbs(root) || filepath.Clean(root) != root {
		t.Fatal("OAK_TYPED_CNF_INSTANCE_OUT must be a clean absolute fresh directory")
	}
	if _, err := os.Lstat(root); !os.IsNotExist(err) {
		t.Fatal("instance output must not exist")
	}
	fixture, err := loadTypedCNFFixture(typedFixtureDirectory)
	if err != nil {
		t.Fatal(err)
	}
	audit, err := checkTypedCNFFixture(t.Context(), fixture)
	if err != nil {
		t.Fatal(err)
	}
	raw := fixture.graph
	names := make([]string, 0, len(raw.declarations))
	for name := range raw.declarations {
		names = append(names, name)
	}
	sort.Strings(names)
	formula := fixture.formula
	// A new deterministic topological numbering preserves every owned pointer,
	// including distinct nodes with identical syntax. It is not the capture ID.
	bl := audit.snapshot
	ids := map[*term]int{}
	var nodes []*term
	var visit func(*term)
	visit = func(term *term) {
		if term == nil {
			return
		}
		if _, seen := ids[term]; seen {
			return
		}
		visit(term.cond)
		visit(term.left)
		visit(term.right)
		ids[term] = len(nodes)
		nodes = append(nodes, term)
	}
	for _, term := range audit.roots {
		visit(term)
	}
	if len(nodes) != 375 {
		t.Fatal("instance node coverage")
	}
	allocation, err := renderCNFAllocationSnapshot(bl.cnf)
	if err != nil {
		t.Fatal(err)
	}
	header := "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace TypedCNFInstance\nopen Oak\nopen Oak.RupCheck Oak.TseitinCNF Oak.CNFReplayApply Oak.CNFReplayTerm\nopen Oak.CNFTypedCircuit Oak.CNFTypedNode Oak.CNFTypedMemory Oak.CNFTypedBridge\n\n"
	var base strings.Builder
	base.WriteString("import Oak.CNFTypedBridge\nimport TypedCNFRefutation.Original\n\n" + header)
	fmt.Fprintf(&base, "def allocation : CNFDenseAllocation.Snapshot := %s\n", allocation)
	words := map[*term]string{}
	vectors := map[*term]string{}
	derivations := map[*term]string{}
	proofs := make([]string, len(nodes))
	structural := map[*term]int{}
	structures := map[typedCNFStructure]int{}
	for id, node := range nodes {
		key := typedCNFStructure{node.kind, node.width, node.declared, node.name, node.op, node.value, structural[node.cond], structural[node.left], structural[node.right]}
		structure, ok := structures[key]
		if !ok {
			structure = len(structures) + 1
			structures[key] = structure
		}
		structural[node] = structure
		word, roots, derived := fmt.Sprintf("n%d", id), fmt.Sprintf("r%d", id), fmt.Sprintf("d%d", id)
		words[node], vectors[node], derivations[node] = word, roots, derived
		bits := bl.memo[node]
		fmt.Fprintf(&base, "def %s : List Nat := %s\n", roots, typedInstanceRoots(bits))
		var body strings.Builder
		declare := func(name string, width int, expr string) {
			fmt.Fprintf(&base, "def %s : Word %d := %s\n", name, width, expr)
		}
		prove := func(name, word, roots, node string) {
			fmt.Fprintf(&body, "theorem %s : Derivation context %s %s := %s\n", name, word, roots, node)
		}
		adapt := func(child *term, width int, label string) (string, string, string) {
			if child.width == width {
				return words[child], vectors[child], derivations[child]
			}
			w, v, d := word+label, roots+label, derived+label
			declare(w, width, fmt.Sprintf(".view %d %s", width, words[child]))
			fmt.Fprintf(&base, "def %s : List Nat := %s\n", v, typedInstanceRoots(replayAdapt(bl.memo[child], width)))
			prove(d, w, v, fmt.Sprintf(".view %d %s (by decide)", width, derivations[child]))
			return w, v, d
		}
		switch node.kind {
		case termConst:
			declare(word, node.width, fmt.Sprintf(".constant (BitVec.ofNat %d %d)", node.width, node.value))
			prove(derived, word, roots, fmt.Sprintf(".constant (BitVec.ofNat %d %d) %s (by decide)", node.width, node.value, roots))
		case termParam:
			declared := node.declaredWidth()
			pw, pv, pd := word, roots, derived
			if node.width != declared {
				pw, pv, pd = word+"decl", roots+"decl", derived+"decl"
				paramBits := make([]int, declared)
				for bit := range paramBits {
					source := bit*(len(names)+8) + bl.index[node.name]
					out, ok := bl.cnf.inputs[source]
					if !ok {
						t.Fatal("unallocated full declaration in instance")
					}
					paramBits[bit] = 2 * out
				}
				fmt.Fprintf(&base, "def %s : List Nat := %s\n", pv, typedInstanceRoots(paramBits))
			}
			declare(pw, declared, fmt.Sprintf(".parameter %d %s", declared, strconv.Quote(node.name)))
			prove(pd, pw, pv, fmt.Sprintf(".parameter (position := %d) (by decide) (by decide) (by decide) (by decide)", bl.index[node.name]))
			if node.width != declared {
				declare(word, node.width, fmt.Sprintf(".view %d %s", node.width, pw))
				prove(derived, word, roots, fmt.Sprintf(".view %d %s (by decide)", node.width, pd))
			}
		case termBinary:
			aw, av, ad := adapt(node.left, node.width, "left")
			bw, bv, bd := adapt(node.right, node.width, "right")
			declare(word, node.width, fmt.Sprintf(".binary .%s %s %s", node.op, aw, bw))
			a, b := "(rootBits "+av+")", "(rootBits "+bv+")"
			circuit := ""
			switch node.op {
			case "and", "or", "xor":
				op := map[string]int{"and": 0, "or": 1, "xor": 2}[node.op]
				circuit = fmt.Sprintf("(fun bit => .binary %d (%s bit) (%s bit))", op, a, b)
			case "add":
				circuit = fmt.Sprintf("(sumTerm %s %s (.constant false))", a, b)
			case "sub":
				circuit = fmt.Sprintf("(sumTerm %s (complementBits %s) (.constant true))", a, b)
			case "shl", "shr":
				stages := 5
				if node.width == 64 {
					stages = 6
				}
				circuit = fmt.Sprintf("(barrelBits %d %t %s %s %d)", node.width, node.op == "shl", a, b, stages)
			default:
				t.Fatal("instance unsupported binary")
			}
			prove(derived, word, roots, fmt.Sprintf(".binary .%s %s %s %s rfl (by decide)", node.op, circuit, ad, bd))
		case termCmp:
			cw, cv, cd := word, roots, derived
			if node.width != 1 {
				cw, cv, cd = word+"bool", roots+"bool", derived+"bool"
				fmt.Fprintf(&base, "def %s : List Nat := [%d]\n", cv, bits[0])
			}
			declare(cw, 1, fmt.Sprintf(".compare .%s %s %s", node.op, words[node.left], words[node.right]))
			prove(cd, cw, cv, fmt.Sprintf(".compare .%s %s %s (by decide)", node.op, derivations[node.left], derivations[node.right]))
			if node.width != 1 {
				declare(word, node.width, fmt.Sprintf(".view %d %s", node.width, cw))
				prove(derived, word, roots, fmt.Sprintf(".view %d %s (by decide)", node.width, cd))
			}
		case termIte:
			aw, _, ad := adapt(node.left, node.width, "left")
			bw, _, bd := adapt(node.right, node.width, "right")
			declare(word, node.width, fmt.Sprintf(".ite %s %s %s", words[node.cond], aw, bw))
			boolean := "(.narrow " + words[node.cond] + ")"
			if node.cond.width != 1 {
				switch {
				case node.cond.kind == termCmp:
					boolean = fmt.Sprintf("(.view %d (.narrow %sbool))", node.cond.width, words[node.cond])
				case node.cond.kind == termParam && node.cond.declaredWidth() == 1:
					boolean = fmt.Sprintf("(.view %d (.narrow %sdecl))", node.cond.width, words[node.cond])
				default:
					t.Fatal("instance guard lacks syntactic Boolean proof")
				}
			}
			prove(derived, word, roots, fmt.Sprintf(".ite %s %s %s (by decide) %s (by decide)", derivations[node.cond], ad, bd, boolean))
		case termSelect:
			slot := -1
			for i, read := range bl.selects {
				if read.span == node.name && structural[read.index] == structural[node.left] {
					if slot != -1 {
						t.Fatal("ambiguous instance read slot")
					}
					slot = i
				}
			}
			if slot < 0 {
				t.Fatal("instance read key")
			}
			declare(word, 32, fmt.Sprintf(".read %s %s", strconv.Quote(node.name), words[node.left]))
			prove(derived, word, roots, fmt.Sprintf(".read (slot := %d) %s (by rfl) (by decide)", slot, derivations[node.left]))
		default:
			t.Fatal("instance unsupported kind")
		}
		proofs[id] = body.String()
	}
	parameters := make([]string, len(names))
	for i, name := range names {
		parameters[i] = fmt.Sprintf("⟨%s, %d⟩", strconv.Quote(name), bl.widths[name])
	}
	reads := make([]string, len(bl.selects))
	for i, read := range bl.selects {
		if words[read.index] == "" {
			t.Fatal("unmapped canonical read index")
		}
		reads[i] = fmt.Sprintf("⟨%s, %s⟩", strconv.Quote(read.span), words[read.index])
	}
	fmt.Fprintf(&base, "def context : Context := ⟨allocation, [%s], [%s], 9223372036854775807⟩\n", strings.Join(parameters, ", "), strings.Join(reads, ", "))
	clauses := append(append([][]int(nil), bl.cnf.clauses...), []int{cnfLit(audit.Obligation)})
	fmt.Fprintf(&base, "def trace : CNFClauseTrace.Snapshot := ⟨allocation, %s, [%d], %s⟩\n", renderCNFTraceClauses(bl.cnf.clauses), audit.Obligation, renderCNFTraceClauses(clauses))
	base.WriteString("\nend TypedCNFInstance\n")
	if err := t.Context().Err(); err != nil {
		t.Fatal(err)
	}
	if err := os.Mkdir(root, 0700); err != nil {
		t.Fatal(err)
	}
	writer := &typedInstanceWriter{directory: root}
	if err := writer.save("Data.lean", base.String()); err != nil {
		t.Fatal(err)
	}
	checks := "import TypedCNFInstance.Data\n\n" + header + "theorem trace_some : (CNFClauseTrace.check trace).isSome = true := by decide\n\ndef checked : CNFClauseTrace.Checked := (CNFClauseTrace.check trace).get trace_some\ntheorem trace_accepted : CNFClauseTrace.check trace = some checked := Option.eq_some_of_isSome trace_some\n\ntheorem clauses_bound : CNFClauseTrace.decodeClauses trace.emitted = some TypedCNFRefutation.original.toList := by decide\ntheorem database_bound : CNFClauseTrace.emittedDatabase? trace = some (databaseOfClauses TypedCNFRefutation.original.toList) := by\n  simp only [CNFClauseTrace.emittedDatabase?, clauses_bound, Option.map_some]\n\nend TypedCNFInstance\n"
	if err := writer.save("Checks.lean", checks); err != nil {
		t.Fatal(err)
	}
	previous := "Checks"
	for first := 0; first < len(proofs); first += 25 {
		last := first + 25
		if last > len(proofs) {
			last = len(proofs)
		}
		name := fmt.Sprintf("Nodes%02d", first/25)
		source := "import TypedCNFInstance." + previous + "\n\n" + header + strings.Join(proofs[first:last], "\n") + "\nend TypedCNFInstance\n"
		if err := writer.save(name+".lean", source); err != nil {
			t.Fatal(err)
		}
		previous = name
	}
	final := fmt.Sprintf("import TypedCNFInstance.%s\nimport TypedCNFRefutation.Final\n\n", previous) + header
	final += fmt.Sprintf("theorem complete_claim : Derivation context (implication %s %s %s) [%d] := by\n  simpa only [%s, %s, %s, %s, implication, BitVec.ofBool_true, BitVec.ofNat_eq_ofNat] using %s\n\n", words[audit.roots[0]], words[audit.roots[1]], words[audit.roots[2]], audit.Claim, words[audit.roots[3]], words[audit.roots[3].left], words[audit.roots[3].right], vectors[audit.roots[3]], derivations[audit.roots[3]])
	final += fmt.Sprintf("theorem supplied_raw_implication : ∀ scalars memory, (concreteEval scalars memory %s).toNat ≠ 0 → concreteEval scalars memory %s = concreteEval scalars memory %s :=\n  refutation_implies_concrete rfl trace_accepted database_bound complete_claim rfl TypedCNFRefutation.exact_cnf_unsatisfiable\n\n#print axioms supplied_raw_implication\nend TypedCNFInstance\n", words[audit.roots[0]], words[audit.roots[1]], words[audit.roots[2]])
	if err := writer.save("Final.lean", final); err != nil {
		t.Fatal(err)
	}
	if err := writer.complete(); err != nil {
		t.Fatal(err)
	}
	if err := t.Context().Err(); err != nil {
		t.Fatal(err)
	}
	t.Logf("supplied typed instance source: nodes=%d modules=%d bytes=%d rawRoots=104/207/371 copiedRoots=%d/%d/%d/%d CNF_SHA256=%s", len(nodes), len(writer.files), writer.bytes, ids[audit.roots[0]], ids[audit.roots[1]], ids[audit.roots[2]], ids[audit.roots[3]], tcSHA([]byte(formula)))
}

// The driver relies on this exact initial inventory before portable transforms.
func (w *typedInstanceWriter) complete() error {
	want := []string{"Data.lean", "Checks.lean"}
	for i := 0; i < 15; i++ {
		want = append(want, fmt.Sprintf("Nodes%02d.lean", i))
	}
	want = append(want, "Final.lean")
	if len(w.files) != len(want) {
		return fmt.Errorf("instance source inventory")
	}
	for i := range want {
		if w.files[i] != want[i] {
			return fmt.Errorf("instance source order")
		}
	}
	entries, err := os.ReadDir(w.directory)
	if err != nil {
		return err
	}
	if len(entries) != len(want) {
		return fmt.Errorf("instance output directory inventory")
	}
	sort.Strings(want)
	bytes := int64(0)
	for i, entry := range entries {
		info, err := entry.Info()
		if err != nil {
			return err
		}
		if entry.Name() != want[i] || !info.Mode().IsRegular() || info.Size() > int64(typedFixtureSourceCap)-bytes {
			return fmt.Errorf("instance output file inventory or cap")
		}
		bytes += info.Size()
	}
	if bytes != int64(w.bytes) {
		return fmt.Errorf("instance output byte count")
	}
	return nil
}
