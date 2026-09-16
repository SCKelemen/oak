package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/optir"
	"github.com/SCKelemen/oak/typechecker"
)

func TestNativeMaterializationKeyIsOrderIndependentAndComplete(t *testing.T) {
	firstFunction := nativeMaterializationFunction("f")
	secondFunction := nativeMaterializationFunction("g")
	lane := func(reverse bool) nativegen.Lane {
		result := nativegen.Lane{
			Arch:       asm.ArchArm64,
			GuardLines: map[int]bool{},
			Globals:    map[string]asm.Global{},
			Tables:     map[string]nativegen.GlobalArray{},
		}
		if reverse {
			result.GuardLines[9] = true
			result.GuardLines[3] = true
			result.Globals["z"] = asm.Global{Type: "u64", Bits: 64}
			result.Globals["a"] = asm.Global{Type: "u32", Bits: 32}
			result.Tables["z"] = nativegen.GlobalArray{Symbol: "data_z", Elem: "u8", Length: 8}
			result.Tables["a"] = nativegen.GlobalArray{Symbol: "data_a", Elem: "u32", Length: 4}
		} else {
			result.GuardLines[3] = true
			result.GuardLines[9] = true
			result.Globals["a"] = asm.Global{Type: "u32", Bits: 32}
			result.Globals["z"] = asm.Global{Type: "u64", Bits: 64}
			result.Tables["a"] = nativegen.GlobalArray{Symbol: "data_a", Elem: "u32", Length: 4}
			result.Tables["z"] = nativegen.GlobalArray{Symbol: "data_z", Elem: "u8", Length: 8}
		}
		return result
	}
	driver := func(reverse bool) *nativeDriver {
		functions := map[string]*ast.FunctionStatement{}
		constants := map[string]asm.Constant{}
		if reverse {
			functions["g"] = secondFunction
			functions["f"] = firstFunction
			constants["z"] = asm.Constant{Type: "u64", Value: 9}
			constants["a"] = asm.Constant{Type: "u32", Value: 3}
		} else {
			functions["f"] = firstFunction
			functions["g"] = secondFunction
			constants["a"] = asm.Constant{Type: "u32", Value: 3}
			constants["z"] = asm.Constant{Type: "u64", Value: 9}
		}
		return &nativeDriver{
			source:       firstFunction,
			functions:    functions,
			records:      map[string]*ast.RecordLiteral{},
			adts:         map[string]*ast.ADTType{},
			constants:    constants,
			tc:           typechecker.NewWithPlatformSizes(object.NewEnvironment(), 64, 64),
			declarations: "Thing: type = Value: u32\n",
		}
	}

	want, err := driver(false).MaterializationKey(opt.Identity(lane(false)))
	if err != nil {
		t.Fatal(err)
	}
	got, err := driver(true).MaterializationKey(opt.Identity(lane(true)))
	if err != nil {
		t.Fatal(err)
	}
	if got != want {
		t.Fatalf("map insertion order changed key: %s != %s", got, want)
	}

	changedLane := lane(false)
	changedLane.Strength = true
	changedDriver := driver(false)
	changedDeclarations := driver(false)
	changedDeclarations.declarations += "Other: type = OtherValue\n"
	changedChecker := driver(false)
	changedChecker.tc = typechecker.NewWithPlatformSizes(object.NewEnvironment(), 32, 32)
	changedSource := driver(false)
	changedSource.source = nativeMaterializationFunction("renamed")
	changedFunction := driver(false)
	changedFunction.functions["g"] = nativeMaterializationFunction("changed")
	changedConstant := driver(false)
	changedConstant.constants["z"] = asm.Constant{Type: "u64", Value: 10}
	changedGlobal := lane(false)
	changedGlobal.Globals["z"] = asm.Global{Type: "u64", Bits: 64, Aggregate: true, Size: 16}
	changedTable := lane(false)
	changedTable.Tables["z"] = nativegen.GlobalArray{Symbol: "data_z", Elem: "u8", Length: 9}
	changedOptIR := lane(false)
	changedOptIR.UseOptIR = true
	changedOptIR.OptIRFingerprint = "cfg-a"
	changedOptIR.OptIRChanges = 3
	changedOptIRFingerprint := changedOptIR
	changedOptIRFingerprint.OptIRFingerprint = "cfg-b"
	changedOptIRCount := changedOptIR
	changedOptIRCount.OptIRChanges = 4
	changedOptIRMemory := changedOptIR
	changedOptIRMemory.OptIRMemory = &optir.RegionMemoryMetadata{}
	changedOptIRBinding := changedOptIR
	changedOptIRBinding.OptIRRegionGlobals = map[optir.RegionID]nativegen.OptIRRegionGlobal{
		"region": {Symbol: "state", Global: asm.Global{Type: "u32", Bits: 32}},
	}
	changes := []struct {
		name      string
		driver    *nativeDriver
		candidate *opt.Candidate
	}{
		{"lane", changedDriver, opt.Identity(changedLane)},
		{"declarations", changedDeclarations, opt.Identity(lane(false))},
		{"checker", changedChecker, opt.Identity(lane(false))},
		{"source", changedSource, opt.Identity(lane(false))},
		{"function", changedFunction, opt.Identity(lane(false))},
		{"constant", changedConstant, opt.Identity(lane(false))},
		{"global", driver(false), opt.Identity(changedGlobal)},
		{"table", driver(false), opt.Identity(changedTable)},
		{"optir", driver(false), opt.Identity(changedOptIR)},
		{"optir-fingerprint", driver(false), opt.Identity(changedOptIRFingerprint)},
		{"optir-changes", driver(false), opt.Identity(changedOptIRCount)},
		{"optir-memory", driver(false), opt.Identity(changedOptIRMemory)},
		{"optir-region-binding", driver(false), opt.Identity(changedOptIRBinding)},
	}
	for _, change := range changes {
		t.Run(change.name, func(t *testing.T) {
			key, err := change.driver.MaterializationKey(change.candidate)
			if err != nil {
				t.Fatal(err)
			}
			if key == want {
				t.Fatalf("changed %s retained key %s", change.name, key)
			}
		})
	}

	// Every switch the registry can turn on has to reach the key: two
	// candidates the digest cannot tell apart would serve one's body for
	// the other out of the cache, which is the one way a cache can be
	// wrong. The loop is over the registry, so a transform added later
	// fails here until its flag is written into the lane's digest.
	plain := opt.Identity(nativegen.PlainLane(lane(false)))
	plainKey, err := driver(false).MaterializationKey(plain)
	if err != nil {
		t.Fatal(err)
	}
	for _, transform := range nativegen.Registry().Transforms() {
		next := transform.Apply(plain)
		if next == nil {
			continue
		}
		t.Run("switch/"+transform.Name(), func(t *testing.T) {
			key, err := driver(false).MaterializationKey(next)
			if err != nil {
				t.Fatal(err)
			}
			if key == plainKey {
				t.Fatalf("%s does not reach the materialization key", transform.Name())
			}
		})
	}
}

func TestNativeMaterializationKeyRejectsForeignConfiguration(t *testing.T) {
	driver := &nativeDriver{}
	if key, err := driver.MaterializationKey(opt.Identity("not a lane")); err == nil || key != "" {
		t.Fatalf("key = %q, error = %v", key, err)
	}
}

func nativeMaterializationFunction(name string) *ast.FunctionStatement {
	return &ast.FunctionStatement{
		Name: &ast.Identifier{Value: name},
		Body: &ast.BlockExpression{Block: &ast.BlockStatement{}},
	}
}
