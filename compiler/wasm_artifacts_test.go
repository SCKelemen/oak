package compiler

import (
	"bytes"
	"context"
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/optir"
	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/wasm"
)

func wasmArtifactCFG(name, value string) optir.CFG {
	return optir.CFG{Name: name, Entry: 1, Results: []optir.Type{"i32"}, Blocks: []optir.Block{{
		ID: 1, Operations: []optir.Operation{{Code: optir.OpConstInt,
			Results:    []optir.Value{{ID: 1, Type: "i32"}},
			Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: value}},
		}}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}},
	}}}
}

func wasmArtifactFunction(name, value string) wasm.FunctionInput {
	function := optir.Function{Name: name, Results: []optir.Type{"i32"}, Body: optir.Region{
		Nodes: []optir.Node{{Operation: &optir.Operation{Code: optir.OpConstInt,
			Results:    []optir.Value{{ID: 1, Type: "i32"}},
			Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: value}},
		}}}, Yield: []optir.ValueID{1},
	}}
	cfg, err := optir.Project(function)
	if err != nil {
		panic(err)
	}
	return wasm.FunctionInput{Structured: function, CFG: cfg}
}

func TestWasmArtifactPipeline(t *testing.T) {
	d, _ := (target.Target{OS: target.OSCore, Arch: target.ArchWasm32}).Describe()
	input := []optir.CFG{wasmArtifactCFG("f", "42"), wasmArtifactCFG("g", "3")}
	first, err := emitWasmGraph(context.Background(), d, input)
	if err != nil {
		t.Fatal(err)
	}
	legacy, err := wasm.Emit(input)
	if err != nil || !reflect.DeepEqual(first.Module, legacy) {
		t.Fatal("DAG changed the safe emitter's output", err)
	}
	unadmitted, err := wasm.EncodeCandidate(input)
	if err != nil || unadmitted.ByteValidation != nil || unadmitted.TranslationVerified || !bytes.Equal(unadmitted.Bytes, legacy.Bytes) {
		t.Fatal("materialization acquired admission authority", err)
	}
	if len(first.Pipeline.Steps) != 4 || first.Module.ByteValidation == nil || first.Module.TranslationVerified {
		t.Fatal("missing byte-only admission provenance", first)
	}
	wrongTarget, _ := (target.Target{OS: target.OSLinux, Arch: target.ArchArm64}).Describe()
	if output, err := admitWasmCandidate(context.Background(), wrongTarget, first.Module); err == nil || len(output.Bytes) != 0 {
		t.Fatal("Wasm output admitted under another target", err)
	}
	second, err := emitWasmGraph(context.Background(), d, []optir.CFG{input[1], input[0]})
	if err != nil || !reflect.DeepEqual(first, second) {
		t.Fatal("reordering identical CFGs changed recipes/bytes", err)
	}
	input[0].Blocks[0].Operations[0].Attributes[0].Value = "43"
	changed, err := emitWasmGraph(context.Background(), d, input)
	if err != nil || changed.Pipeline.Steps[3].Artifact == first.Pipeline.Steps[3].Artifact || bytes.Equal(changed.Module.Bytes, first.Module.Bytes) {
		t.Fatal("changed input reused output/admission", err)
	}
	for _, corrupt := range []func(*wasm.Module){
		func(m *wasm.Module) { m.Bytes[0] = 1 },
		func(m *wasm.Module) { m.Exports[0].Name = "wrong" },
		func(m *wasm.Module) { m.TranslationVerified = true },
	} {
		candidate, _ := wasm.Emit(input) // includes a previously valid report
		corrupt(&candidate)
		output, report, err := runEmissionGraph(context.Background(), d,
			opt.ArtifactKey{Kind: opt.ArtifactChecked, Name: "bad-wasm", Version: "v1"}, true,
			emissionBackend[bool, wasm.Module]{
				name: "wasm", materializeRevision: "test", admissionRevision: "test",
				materialize: func(context.Context, target.Description, bool) (wasm.Module, error) { return candidate, nil },
				admit:       admitWasmCandidate,
			})
		if err == nil || len(output.Bytes) != 0 || output.ByteValidation != nil || len(report.Steps) != 0 {
			t.Fatal("stale report authorized corrupt bytes/claims", err)
		}
	}
	comp := New().WithSource("main.oak", "main: (): i32 = 42")
	api, err := comp.EmitWasmWithReport().Get()
	if err != nil {
		t.Fatal(err)
	}
	module, err := comp.EmitWasm().Get()
	if err != nil || !reflect.DeepEqual(api.Module, module) {
		t.Fatal("compatibility API diverged", err)
	}
	bad, err := comp.WithVerifiedProfile().EmitWasmWithReport().Get()
	if err == nil || len(bad.Module.Bytes) != 0 || len(bad.Pipeline.Steps) != 0 {
		t.Fatal("verified-only returned partial artifact", err)
	}
}

func TestWasmStructuredArtifactPipeline(t *testing.T) {
	d, _ := (target.Target{OS: target.OSCore, Arch: target.ArchWasm32}).Describe()
	input := []wasm.FunctionInput{wasmArtifactFunction("f", "42"), wasmArtifactFunction("g", "3")}
	first, err := emitStructuredWasmGraph(context.Background(), d, input)
	if err != nil {
		t.Fatal(err)
	}
	legacy, err := wasm.EmitStructured(input)
	if err != nil || !reflect.DeepEqual(first.Module, legacy) || len(first.Pipeline.Steps) != 4 {
		t.Fatal("structured DAG changed safe materialization/admission", err)
	}
	reordered, err := emitStructuredWasmGraph(context.Background(), d, []wasm.FunctionInput{input[1], input[0]})
	if err != nil || !reflect.DeepEqual(first, reordered) {
		t.Fatal("structured declaration order changed recipes/bytes", err)
	}
	input[0].Structured.Body.Nodes[0].Operation.Attributes[0].Value = "43"
	if output, err := emitStructuredWasmGraph(context.Background(), d, input); err == nil || len(output.Module.Bytes) != 0 || len(output.Pipeline.Steps) != 0 {
		t.Fatal("mismatched structured identity reached admission", err)
	}
}

func TestOptIRGraphSnapshot(t *testing.T) {
	input := wasmArtifactCFG("f", "42")
	graph, refs, err := newOptIRAnalysisGraph(input, optir.CheckedMemoryAuthority{})
	if err != nil {
		t.Fatal(err)
	}
	input.Blocks[0].Operations[0].Attributes[0].Value = "99"
	run, err := graph.Run(context.Background(), nil, refs.cfgV0.Key())
	if err != nil {
		t.Fatal(err)
	}
	root, err := refs.cfgV0.Value(run)
	if err != nil || root.Blocks[0].Operations[0].Attributes[0].Value != "42" {
		t.Fatal("caller mutated an already-keyed graph input", err)
	}
}
