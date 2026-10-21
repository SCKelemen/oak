package compiler

import (
	"encoding/json"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/optir"
	"github.com/SCKelemen/oak/stdlib"
)

func TestStatefulCopyRawProjection(t *testing.T) {
	comp := statefulCopyCompilation(t, statefulCopySource(t))
	artifact, err := comp.StatefulCopyOptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	program := artifact.Program()
	if err := optir.VerifyStatefulProgram(program); err != nil {
		t.Fatal(err)
	}
	if len(program.Functions()) != 2 || len(program.ByteAccesses()) != 2 || len(program.Calls()) != 1 {
		t.Fatalf("wrong raw closure: %d functions %d accesses %d calls", len(program.Functions()), len(program.ByteAccesses()), len(program.Calls()))
	}
	again, err := comp.StatefulCopyOptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	same, err := optir.ExactStatefulProgramEqual(program, again.Program())
	if err != nil || !same {
		t.Fatalf("nondeterministic raw projection: %t %v", same, err)
	}
	if !reflect.DeepEqual(artifact.Sources(), again.Sources()) {
		t.Fatal("source bytes changed")
	}
	for _, f := range program.Functions() {
		t.Logf("%s: %d raw blocks", f.Structured.Name, len(f.CFG.Blocks))
	}
	sources := artifact.Sources()
	if len(sources) != 3 || sources[2].Text != stdlib.Prelude || sources[0].Text != stdlib.Packages["bytes"] || sources[1].Text != statefulCopySource(t) {
		t.Fatal("original dependency/source bytes not retained")
	}
	sources[2].Text = "mutated"
	if artifact.Sources()[2].Text == "mutated" {
		t.Fatal("source snapshot aliases caller")
	}
	if len(artifact.IndexProofs()) == 0 {
		t.Fatal("checked extent identity was not retained")
	}
	if path := os.Getenv("OAK_STATEFUL_RAW_EXPORT"); path != "" {
		// Diagnostic JSON is refreshed from this exact checked artifact; formal
		// fixture generation below consumes the same owned program snapshots.
		data, err := artifact.ExportJSON()
		if err != nil {
			t.Fatal(err)
		}
		if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, data, 0644); err != nil {
			t.Fatal(err)
		}
		lean, err := artifact.ExportLean()
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path+".lean", []byte(lean), 0644); err != nil {
			t.Fatal(err)
		}
	}
}

func TestStatefulCopyRawExportIdentity(t *testing.T) {
	artifact, err := statefulCopyCompilation(t, statefulCopySource(t)).StatefulCopyOptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	first, err := artifact.ExportJSON()
	if err != nil {
		t.Fatal(err)
	}
	second, err := artifact.ExportJSON()
	if err != nil || string(first) != string(second) {
		t.Fatal("export not deterministic", err)
	}
	if err := artifact.ValidateExportJSON(first); err != nil {
		t.Fatal(err)
	}
	data, err := artifact.Export()
	if err != nil {
		t.Fatal(err)
	}
	mutations := map[string]func(*StatefulRawExport){
		"profile":           func(d *StatefulRawExport) { d.Profile = "other" },
		"source bytes":      func(d *StatefulRawExport) { d.Sources[2].Text += "\n" },
		"source package":    func(d *StatefulRawExport) { d.Sources[1].Package = "counterfeit-bytes" },
		"source context":    func(d *StatefulRawExport) { d.Functions[0].CFG.Blocks[0].Operations[0].Source.Context = "other" },
		"callee operation":  func(d *StatefulRawExport) { d.Functions[0].CFG.Blocks[0].Operations[0].Operands = []optir.ValueID{1} },
		"structured alone":  func(d *StatefulRawExport) { d.Functions[0].Structured.Body.Nodes[0].Operation.Code = "unknown" },
		"authority operand": func(d *StatefulRawExport) { d.Accesses[0].Index++ },
		"authority extent":  func(d *StatefulRawExport) { d.IndexProofs[0].Proof.Witness = "forged" },
		"type declaration":  func(d *StatefulRawExport) { d.Types[0].Declaration.Context = "forged" },
		"call summary":      func(d *StatefulRawExport) { d.Calls[0].Effects = nil },
	}
	for name, mutate := range mutations {
		t.Run(name, func(t *testing.T) {
			var changed StatefulRawExport
			raw, _ := json.Marshal(data)
			if err := json.Unmarshal(raw, &changed); err != nil {
				t.Fatal(err)
			}
			mutate(&changed)
			raw, _ = json.Marshal(changed)
			if artifact.ValidateExportJSON(raw) == nil {
				t.Fatal("changed export admitted")
			}
		})
	}
	for _, raw := range [][]byte{append(first, []byte("{}")...), []byte(strings.Replace(string(first), `"Profile":`, `"Unknown": 1, "Profile":`, 1)), []byte(strings.Replace(string(first), `"descriptor.length"`, `"unknown.op"`, 1))} {
		if artifact.ValidateExportJSON(raw) == nil {
			t.Fatal("malformed transport admitted")
		}
	}
	lean1, err := artifact.ExportLean()
	if err != nil {
		t.Fatal(err)
	}
	lean2, _ := artifact.ExportLean()
	if lean1 != lean2 || !strings.Contains(lean1, `code := "memory.byte-store"`) {
		t.Fatal("Lean export is unstable or omitted actual byte store")
	}
}

func TestStatefulCopyRawAdmissionRefusals(t *testing.T) {
	source := statefulCopySource(t)
	for name, changed := range map[string]string{
		"global initializer":     source + "\nglobal: u32 = u32(0)\n",
		"shadowed payload":       strings.Replace(source, ".Ok(count) => count == n", ".Ok(n) => n == n", 1),
		"shadowed builtin":       source + "\nlen: (src: []u8): u32 = u32(0)\n",
		"shadowed local builtin": strings.Replace(source, "n: u32 = len(src)", "len: u32 = u32(0)\n  n: u32 = len(src)", 1),
		"wider source":           strings.Replace(source, "src: []u8", "src: []u32", 1),
		"different root":         strings.Replace(source, "copy_checked:", "other:", 1),
		"missing call":           strings.Replace(source, "bytes.copy_into(dst, src)", ".Ok(n)", 1),
		"different callee":       strings.Replace(source, "bytes.copy_into(dst, src)", "bytes.copy_into(dst, src) + u32(0)", 1),
	} {
		t.Run(name, func(t *testing.T) {
			if _, err := statefulCopyCompilation(t, changed).StatefulCopyOptIR().Get(); err == nil {
				t.Fatal("unsupported raw profile admitted")
			}
		})
	}
	comp := statefulCopyCompilation(t, source).WithSyntaxRewrite(func(tree *SyntaxTree) error {
		for _, statement := range tree.Root.Statements {
			if f, ok := statement.(*ast.FunctionStatement); ok && f.Name.Value == "copy_checked" {
				f.Name.Value = "changed"
			}
		}
		return nil
	})
	if _, err := comp.StatefulCopyOptIR().Get(); err == nil {
		t.Fatal("external source rewrite admitted")
	}
	// This widening is deliberately isolated from scalar whole-cell globals.
	model, err := statefulCopyCompilation(t, source).Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	globals := checkedOptIRGlobals(model.Tree.Root, model.TypeChecker)
	for _, typ := range globals {
		if typ == optir.TypeByteView || typ == optir.TypeByteSpan || typ == optir.TypeCopyResult || typ == optir.TypeCopyError {
			t.Fatal("raw profile widened scalar globals")
		}
	}
}

// Executes the actual freshly produced CFG, not the profile unit-test graph.
func TestStatefulCopyRawExecutionCorpus(t *testing.T) {
	artifact, err := statefulCopyCompilation(t, statefulCopySource(t)).StatefulCopyOptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	program := artifact.Program()
	cases := 0
	run := func(dst, src optir.StatefulDescriptor, before optir.StatefulMemory) {
		t.Helper()
		expected := make(optir.StatefulMemory, len(before))
		for a, b := range before {
			expected[a] = b
		}
		success := src.Length <= dst.Length
		if success {
			for i := uint32(0); i < src.Length; i++ {
				expected[dst.Base+uint64(i)] = before[src.Base+uint64(i)]
			}
		}
		got, err := optir.ExecuteStatefulProgram(program, dst, src, before, 10000)
		if err != nil || got.Outcome != optir.StatefulReturned || got.Value.Type != optir.TypeBool || got.Value.Bool != success || len(got.Calls) != 1 {
			t.Fatalf("case %d failed: %+v %v", cases, got, err)
		}
		result := got.Calls[0].Value
		if result.Type != optir.TypeCopyResult || result.Payload == nil {
			t.Fatal("lost concrete Result")
		}
		if success {
			if result.Variant != string(optir.TypeCopyResult)+".Ok" || result.Payload.Type != "u32" || result.Payload.Uint != src.Length {
				t.Fatal("wrong count/variant")
			}
		} else {
			if result.Variant != string(optir.TypeCopyResult)+".Err" || result.Payload.Type != optir.TypeCopyError || result.Payload.Variant != string(optir.TypeCopyError)+".DestinationTooSmall" || result.Payload.Payload != nil {
				t.Fatal("lost nested error")
			}
		}
		if !reflect.DeepEqual(got.Memory, expected) {
			t.Fatalf("wrong memory/frame in actual CFG case %d", cases)
		}
		// Exact IR cost is derived from this generated graph, not target fuel.
		fuel := uint64(16)
		if success {
			fuel = 19 + 7*uint64(src.Length)
		}
		if got.Steps != fuel {
			t.Fatalf("unexpected actual CFG cost %d vs %d", got.Steps, fuel)
		}
		exact, err := optir.ExecuteStatefulProgram(program, dst, src, before, fuel)
		if err != nil || exact.Outcome != optir.StatefulReturned {
			t.Fatal("exact IR fuel failed", err)
		}
		short, err := optir.ExecuteStatefulProgram(program, dst, src, before, fuel-1)
		if err != nil || short.Outcome != optir.StatefulExhausted || short.Value.Type == optir.TypeCopyResult {
			t.Fatal("IR exhaustion confused with Result", err)
		}
		cases++
	}
	corpus := bytesCopyCases()
	applicable := 0
	for _, c := range corpus {
		if uint64(c.offset) > uint64(len(c.dst)) {
			continue
		} // no valid subwindow for these copy_at-only cases
		before := optir.StatefulMemory{99: 11, 100: 17, 200: 29, 299: 31, 999: 43}
		for i, b := range c.dst {
			before[100+uint64(i)] = b
		}
		for i, b := range c.src {
			before[200+uint64(i)] = b
		}
		run(optir.StatefulDescriptor{Base: 100 + uint64(c.offset), Length: uint32(len(c.dst)) - c.offset}, optir.StatefulDescriptor{Base: 200, Length: uint32(len(c.src))}, before)
		applicable++
	}
	for _, d := range []uint32{0, 1, 3, 5} {
		for _, s := range []uint32{0, 1, 2, 3, 5} {
			before := optir.StatefulMemory{}
			for i, b := range []byte{11, 22, 33, 44, 55, 66, 77} {
				before[100+uint64(i)] = b
			}
			for i, b := range []byte{81, 0, 128, 255, 17, 240, 82} {
				before[200+uint64(i)] = b
			}
			run(optir.StatefulDescriptor{Base: 101, Length: d}, optir.StatefulDescriptor{Base: 201, Length: s}, before)
		}
	}
	run(optir.StatefulDescriptor{Base: 101, Length: 0}, optir.StatefulDescriptor{Base: 201, Length: 0}, optir.StatefulMemory{100: 173, 200: 219})
	// One coherent backing, disjoint nonzero-offset windows. Source window stays
	// unchanged while bytes elsewhere in the very same source owner do change.
	for s := uint32(0); s <= 5; s++ {
		for d := uint32(0); d <= 6; d++ {
			before := optir.StatefulMemory{}
			for i := uint64(0); i < 20; i++ {
				before[100+i] = byte(i * 43)
			}
			run(optir.StatefulDescriptor{Base: 112, Length: d}, optir.StatefulDescriptor{Base: 102, Length: s}, before)
		}
	}
	t.Logf("actual raw CFG: %d cases; %d/%d prior corpus cases have valid subwindow inputs; all 21 frozen offset cases plus 42 same-owner-shaped disjoint cases", cases, applicable, len(corpus))
}

func walkRawOperations(region *optir.Region, visit func(*optir.Operation)) {
	for i := range region.Nodes {
		node := &region.Nodes[i]
		switch {
		case node.Operation != nil:
			visit(node.Operation)
		case node.If != nil:
			walkRawOperations(&node.If.Then, visit)
			walkRawOperations(&node.If.Else, visit)
		case node.While != nil:
			walkRawOperations(&node.While.Condition, visit)
			walkRawOperations(&node.While.Body, visit)
		}
	}
}
func TestStatefulCopyRawProducedMutations(t *testing.T) {
	artifact, err := statefulCopyCompilation(t, statefulCopySource(t)).StatefulCopyOptIR().Get()
	if err != nil {
		t.Fatal(err)
	}
	p := artifact.Program()
	for name, mutate := range map[string]func([]optir.StatefulFunction){
		"unknown opcode": func(fs []optir.StatefulFunction) {
			walkRawOperations(&fs[0].Structured.Body, func(op *optir.Operation) {
				if op.Code == optir.OpByteStore {
					op.Code = "arbitrary.store"
				}
			})
		},
		"wrong call target": func(fs []optir.StatefulFunction) {
			walkRawOperations(&fs[1].Structured.Body, func(op *optir.Operation) {
				if op.Code == optir.OpCall {
					op.Attributes[0].Value = "copy_checked"
				}
			})
		},
		"swapped call operands": func(fs []optir.StatefulFunction) {
			walkRawOperations(&fs[1].Structured.Body, func(op *optir.Operation) {
				if op.Code == optir.OpCall {
					op.Operands[0], op.Operands[1] = op.Operands[1], op.Operands[0]
				}
			})
		},
		"missing store effect": func(fs []optir.StatefulFunction) {
			walkRawOperations(&fs[0].Structured.Body, func(op *optir.Operation) {
				if op.Code == optir.OpByteStore {
					op.Effects = []optir.Effect{optir.EffectTrap}
				}
			})
		},
		"wrong Result payload": func(fs []optir.StatefulFunction) {
			walkRawOperations(&fs[0].Structured.Body, func(op *optir.Operation) {
				if op.Code == optir.OpADTConstruct && op.Results[0].Type == optir.TypeCopyResult {
					op.Operands = []optir.ValueID{1}
				}
			})
		},
		"store before load": func(fs []optir.StatefulFunction) {
			var reorder func(*optir.Region)
			reorder = func(r *optir.Region) {
				for i := range r.Nodes {
					n := &r.Nodes[i]
					if n.If != nil {
						reorder(&n.If.Then)
						reorder(&n.If.Else)
					}
					if n.While != nil {
						n.While.Body.Nodes[0], n.While.Body.Nodes[1] = n.While.Body.Nodes[1], n.While.Body.Nodes[0]
					}
				}
			}
			reorder(&fs[0].Structured.Body)
		},
	} {
		t.Run(name, func(t *testing.T) {
			fs := p.Functions()
			mutate(fs)
			for i := range fs {
				cfg, err := optir.Project(fs[i].Structured)
				if err != nil {
					return
				}
				fs[i].CFG = cfg
			}
			if _, err := optir.NewStatefulProgram(p.Root(), fs, p.Types(), p.ByteAccesses(), p.Calls()); err == nil {
				t.Fatal("changed actual produced graph admitted")
			}
		})
	}
	// Profile typing alone is deliberately NOT advertised as copying semantics.
	// A typed increment-by-two remains well-formed, but executing that changed
	// actual CFG demonstrably violates byte copying. The fresh kernel mutation
	// gate additionally rejects its actual translation-validator acceptance theorem.
	fs := p.Functions()
	changed := false
	walkRawOperations(&fs[0].Structured.Body, func(op *optir.Operation) {
		if op.Code == optir.OpConstInt && op.Attributes[0].Value == "1" {
			op.Attributes[0].Value = "2"
			changed = true
		}
	})
	if !changed {
		t.Fatal("did not locate real increment")
	}
	fs[0].CFG, err = optir.Project(fs[0].Structured)
	if err != nil {
		t.Fatal(err)
	}
	wrong, err := optir.NewStatefulProgram(p.Root(), fs, p.Types(), p.ByteAccesses(), p.Calls())
	if err != nil {
		t.Fatal("typed mutation should reach semantic validation", err)
	}
	before := optir.StatefulMemory{10: 128, 11: 255, 20: 7, 21: 8}
	got, err := optir.ExecuteStatefulProgram(wrong, optir.StatefulDescriptor{Base: 20, Length: 2}, optir.StatefulDescriptor{Base: 10, Length: 2}, before, 1000)
	if err != nil || got.Outcome != optir.StatefulReturned || got.Memory[21] != 8 || got.Memory[21] == before[11] {
		t.Fatal("increment mutation failed to expose semantic gap", err)
	}
}
