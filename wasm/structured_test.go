package wasm

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/optir"
)

func structuredConstant(value string) FunctionInput {
	function := optir.Function{Name: "constant", Results: []optir.Type{"u32"}, Body: optir.Region{
		Nodes: []optir.Node{{Operation: &optir.Operation{Code: optir.OpConstInt,
			Results:    []optir.Value{{ID: 1, Type: "u32"}},
			Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: value}},
		}}}, Yield: []optir.ValueID{1},
	}}
	cfg, err := optir.Project(function)
	if err != nil {
		panic(err)
	}
	return FunctionInput{Structured: function, CFG: cfg}
}

func TestStructuredInputBindsExactCFG(t *testing.T) {
	input := structuredConstant("7")
	want, err := Emit([]optir.CFG{input.CFG})
	if err != nil {
		t.Fatal(err)
	}
	got, err := EmitStructured([]FunctionInput{input})
	if err != nil {
		t.Fatal(err)
	}
	if string(got.Bytes) != string(want.Bytes) {
		t.Fatal("structured authority changed an established direct encoding")
	}
	input.CFG.Blocks[0].Operations[0].Attributes[0].Value = "8"
	if module, err := EmitStructured([]FunctionInput{input}); err == nil || len(module.Bytes) != 0 || !strings.Contains(err.Error(), "disagrees") {
		t.Fatal("mismatched structured/CFG pair was admitted", err)
	}
}

func TestStructuredInputRejectsSharedOrDeepControl(t *testing.T) {
	shared := &optir.If{}
	function := optir.Function{Name: "shared", Body: optir.Region{Nodes: []optir.Node{{If: shared}, {If: shared}}}}
	if module, err := EncodeStructuredCandidate([]FunctionInput{{Structured: function}}); err == nil || len(module.Bytes) != 0 || !strings.Contains(err.Error(), "shared or cyclic") {
		t.Fatal("shared structured control reached recursive validation", err)
	}

	region := optir.Region{}
	for i := 0; i <= maxStructuredControlDepth; i++ {
		branch := &optir.If{Then: region}
		region = optir.Region{Nodes: []optir.Node{{If: branch}}}
	}
	function = optir.Function{Name: "deep", Body: region}
	if module, err := EncodeStructuredCandidate([]FunctionInput{{Structured: function}}); err == nil || len(module.Bytes) != 0 || !strings.Contains(err.Error(), "depth") {
		t.Fatal("deep structured control reached recursive validation", err)
	}
}
