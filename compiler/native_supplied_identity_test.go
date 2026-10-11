package compiler

import (
	"bytes"
	"math"
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/asm"
)

func TestNativeSuppliedIdentityClassifiesFunctionFields(t *testing.T) {
	// These fields are bound by the complete source/compiler/target recipe and
	// the checked declaration, not by this machine-body observation digest.
	excluded := map[string]string{
		"Signature":        "checked declaration identity",
		"Line":             "diagnostic source location",
		"Records":          "whole-program source type declarations",
		"ADTs":             "whole-program source type declarations",
		"Constants":        "source recipe semantic environment",
		"Globals":          "source recipe semantic environment",
		"Callees":          "source recipe semantic environment and actual verdict dependencies",
		"Externs":          "source recipe semantic environment",
		"Body":             "source recipe semantic environment",
		"Tables":           "source recipe semantic environment",
		"LoweringMetadata": "explicitly not assembly contract or verifier authority",
	}
	function, body := reflect.TypeOf(asm.Function{}), reflect.TypeOf(nativeSuppliedBody{})
	for i := 0; i < function.NumField(); i++ {
		field := function.Field(i)
		observed, included := body.FieldByName(field.Name)
		if included == (excluded[field.Name] != "") || (included && observed.Type != field.Type) {
			t.Fatalf("asm.Function.%s requires one reviewed identity classification", field.Name)
		}
	}
	for i := 0; i < body.NumField(); i++ {
		if _, exists := function.FieldByName(body.Field(i).Name); !exists {
			t.Fatalf("stale supplied identity field %s", body.Field(i).Name)
		}
	}
	for name := range excluded {
		if _, exists := function.FieldByName(name); !exists {
			t.Fatalf("stale supplied identity exclusion %s", name)
		}
	}
}

func TestNativeSuppliedIdentityBindsTypedBodyAndEncoding(t *testing.T) {
	unit := func() *asm.Function {
		return &asm.Function{Name: "unit", Arch: asm.ArchArm64, Items: []asm.Item{
			asm.Label{Name: "entry", Line: 1}, asm.Align{Bytes: 4, Line: 2},
			asm.Instruction{Mnemonic: "mov", Line: 3, Operands: []asm.Operand{
				asm.Register{Text: "w0", Class: asm.ClassW, Num: 0, Lane: -1}, asm.Immediate{Value: 1},
			}},
		}}
	}
	mutations := map[string]func(*asm.Function){
		"name":              func(f *asm.Function) { f.Name += "_changed" },
		"arch":              func(f *asm.Function) { f.Arch = asm.ArchRV64 },
		"inert":             func(f *asm.Function) { f.Inert = true },
		"items":             func(f *asm.Function) { f.Items = f.Items[1:] },
		"bindings":          func(f *asm.Function) { f.Bindings = []asm.Binding{{Param: "value", OnStack: true, Stack: 8}} },
		"clobbers":          func(f *asm.Function) { f.Clobbers = []asm.Register{{Class: asm.ClassX, Num: 9}} },
		"frame":             func(f *asm.Function) { f.Frame = 16 },
		"system":            func(f *asm.Function) { f.System = true },
		"align":             func(f *asm.Function) { f.Align = 32 },
		"compressed":        func(f *asm.Function) { f.Compressed = true },
		"compressed-set":    func(f *asm.Function) { f.CompressedSet = true },
		"float-file":        func(f *asm.Function) { f.FloatFile = true },
		"vector-file":       func(f *asm.Function) { f.VectorFile = true },
		"fallback":          func(f *asm.Function) { f.Fallback = true },
		"composites":        func(f *asm.Function) { f.Composites = map[string]asm.Composite{"R": {Size: 16}} },
		"stack-args":        func(f *asm.Function) { f.StackArgs = 8 },
		"packed-stack-args": func(f *asm.Function) { f.PackedStackArgs = true },
		"two-chunk-results": func(f *asm.Function) { f.TwoChunkResults = map[string]bool{"callee": true} },
		"frame-objects":     func(f *asm.Function) { f.FrameObjects = []asm.FrameObject{{Offset: 8, Size: 16}} },
		"result-slot":       func(f *asm.Function) { f.ResultSlot = "result" },
	}
	for name, change := range map[string]func(*asm.Instruction){
		"mnemonic":                      func(i *asm.Instruction) { i.Mnemonic = "add" },
		"condition":                     func(i *asm.Instruction) { i.Cond = "eq" },
		"operand-value":                 func(i *asm.Instruction) { i.Operands[1] = asm.Immediate{Value: 2} },
		"operand-type":                  func(i *asm.Instruction) { i.Operands[1] = asm.FloatImmediate{Value: 1} },
		"same-spelling-register-class":  func(i *asm.Instruction) { r := i.Operands[0].(asm.Register); r.Class = asm.ClassX; i.Operands[0] = r },
		"same-spelling-register-number": func(i *asm.Instruction) { r := i.Operands[0].(asm.Register); r.Num = 1; i.Operands[0] = r },
		"memory-mode":                   func(i *asm.Instruction) { i.Operands[1] = asm.Memory{Mode: asm.MemPostIndex, Offset: 8} },
		"checked-facts":                 func(i *asm.Instruction) { i.CheckedFacts = []asm.CheckedFactRef{{ID: "fact", Extent: 8}} },
		"call-site":                     func(i *asm.Instruction) { i.OptIRCallSite = 7 },
	} {
		mutations[name] = func(f *asm.Function) { i := f.Items[2].(asm.Instruction); change(&i); f.Items[2] = i }
	}
	want := nativeSuppliedBodyDigest(unit())
	if len(want) != 64 || want != nativeSuppliedBodyDigest(unit()) {
		t.Fatal("supplied identity is absent or pointer-dependent")
	}
	for name, mutate := range mutations {
		t.Run(name, func(t *testing.T) {
			changed := unit()
			mutate(changed)
			if got := nativeSuppliedBodyDigest(changed); len(got) != 64 || got == want {
				t.Fatalf("typed supplied-body mutation escaped identity: %s", name)
			}
		})
	}
	left, right := unit(), unit()
	left.TwoChunkResults = map[string]bool{"a": true, "b": false}
	right.TwoChunkResults = map[string]bool{"b": false, "a": true}
	if nativeSuppliedBodyDigest(left) != nativeSuppliedBodyDigest(right) {
		t.Fatal("map insertion order changed body identity")
	}
	for _, f := range []float64{math.Inf(1), math.NaN()} {
		bad := unit()
		bad.Items = []asm.Item{asm.Instruction{Operands: []asm.Operand{asm.FloatImmediate{Value: f}}}}
		if nativeSuppliedBodyDigest(bad) != "" {
			t.Fatal("unsupported float acquired a valid identity")
		}
	}
	var positive, negative bytes.Buffer
	if !writeNativeSuppliedValue(&positive, reflect.ValueOf(float64(0))) || !writeNativeSuppliedValue(&negative, reflect.ValueOf(math.Copysign(0, -1))) || bytes.Equal(positive.Bytes(), negative.Bytes()) {
		t.Fatal("floating point sign bits were collapsed")
	}
	if writeNativeSuppliedValue(&positive, reflect.ValueOf(make(chan int))) {
		t.Fatal("unknown projection data was accepted")
	}
	type recursive struct{ Next *recursive }
	cycle := &recursive{}
	cycle.Next = cycle
	if writeNativeSuppliedValue(&positive, reflect.ValueOf(cycle)) {
		t.Fatal("recursive projection escaped the finite depth bound")
	}
}
