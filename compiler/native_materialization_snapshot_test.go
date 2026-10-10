package compiler

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"sync"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/typechecker"
)

// Keep the pre-snapshot serialization order independent of the new suffix
// helper: these are the exact v33 bytes previously written on every key call.
func legacyNativeMaterializationRecipe(d *nativeDriver) []byte {
	var out bytes.Buffer
	if d.source == nil {
		writeNativeMaterializationPart(&out, "source:nil")
	} else {
		writeNativeMaterializationPart(&out, "source", d.source.String())
	}
	writeNativeFunctions(&out, d.functions)
	writeNativeRecords(&out, d.records)
	writeNativeADTs(&out, d.adts)
	writeNativeConstants(&out, d.constants)
	writeNativeMaterializationPart(&out, "declarations", d.declarations)
	fingerprint := d.tcFingerprint
	if fingerprint == "" {
		fingerprint = d.tc.NativeLoweringFingerprint()
	}
	writeNativeMaterializationPart(&out, "typechecker", fingerprint)
	return out.Bytes()
}

func legacyNativeMaterializationKey(d *nativeDriver, lane nativegen.Lane) string {
	digest := sha256.New()
	writeNativeMaterializationPart(digest, "oak.native.materialization.v33")
	writeNativeLane(digest, lane)
	_, _ = digest.Write(legacyNativeMaterializationRecipe(d))
	return hex.EncodeToString(digest.Sum(nil))
}

func nativeRecipeFixture() *nativeDriver {
	f, g := nativeMaterializationFunction("f"), nativeMaterializationFunction("g")
	f.Parameters = []*ast.FunctionParameter{{Name: &ast.Identifier{Value: "x"}, Type: &ast.Identifier{Value: "u32"}}}
	f.ReturnType = &ast.Identifier{Value: "u32"}
	f.Body.(*ast.BlockExpression).Block.Statements = []ast.Statement{
		&ast.ExpressionStatement{Expression: &ast.Identifier{Value: "x"}},
	}
	return &nativeDriver{
		source:    f,
		functions: map[string]*ast.FunctionStatement{"f": f, "g": g, "nil": nil},
		records: map[string]*ast.RecordLiteral{"R": {Fields: map[string]ast.Expression{
			"value": &ast.Identifier{Value: "u32"},
		}}, "nil": nil},
		adts: map[string]*ast.ADTType{"Choice": {
			Name:     &ast.Identifier{Value: "Choice"},
			Variants: []*ast.ADTVariant{{Name: &ast.Identifier{Value: "Some"}, Payload: &ast.Identifier{Value: "u32"}}},
		}, "nil": nil},
		constants:    map[string]asm.Constant{"C": {Type: "u32", Value: 7}},
		tc:           typechecker.NewWithPlatformSizes(object.NewEnvironment(), 64, 64),
		declarations: "Choice: type = Some(u32)\n",
	}
}

func TestNativeMaterializationRecipeMatchesLegacyBytes(t *testing.T) {
	explicit := nativeRecipeFixture()
	explicit.tcFingerprint = "explicit checked fingerprint\x00with framing"
	empty := &nativeDriver{functions: map[string]*ast.FunctionStatement{}, records: map[string]*ast.RecordLiteral{}, adts: map[string]*ast.ADTType{}, constants: map[string]asm.Constant{}}
	for _, d := range []*nativeDriver{{}, empty, nativeRecipeFixture(), explicit} {
		plain := nativegen.PlainLane(nativegen.Lane{Arch: asm.ArchArm64})
		candidates := []*opt.Candidate{opt.Identity(plain), opt.Identity(nativegen.Lane{Arch: asm.ArchRV64, SoftFloat: true})}
		for _, transform := range nativegen.Registry().Transforms() {
			if next := transform.Apply(candidates[0]); next != nil {
				candidates = append(candidates, next)
			}
		}
		_, err := d.withMaterializationRecipe(func() (*opt.Selection, error) {
			if want := legacyNativeMaterializationRecipe(d); !bytes.Equal(d.materializationRecipe, want) {
				t.Fatal("snapshot changed the old length-delimited recipe bytes")
			}
			for _, candidate := range candidates {
				lane := candidate.Config.(nativegen.Lane)
				got, err := d.MaterializationKey(candidate)
				if err != nil || got != legacyNativeMaterializationKey(d, lane) {
					t.Fatalf("%s: key %q, error %v differs from legacy", candidate.Name(), got, err)
				}
			}
			// Candidate-owned map aliases remain live throughout the scope.
			lane := plain
			lane.Globals = map[string]asm.Global{"cell": {Type: "u32", Bits: 32}}
			alias := lane.Globals
			for _, width := range []int{32, 64, 16} {
				alias["cell"] = asm.Global{Type: fmt.Sprintf("u%d", width), Bits: width}
				got, err := d.MaterializationKey(opt.Identity(lane))
				if err != nil || got != legacyNativeMaterializationKey(d, lane) {
					t.Fatalf("live candidate alias at width %d: %q, %v", width, got, err)
				}
			}
			return nil, nil
		})
		if err != nil || d.materializationRecipe != nil {
			t.Fatalf("scope retained recipe: %v", err)
		}
	}
}

func TestNativeMaterializationRecipeRebuildsAfterAliasedMutations(t *testing.T) {
	mutations := map[string]func(*nativeDriver){
		"source-name": func(d *nativeDriver) { d.source.Name.Value = "renamed" },
		"source-body": func(d *nativeDriver) {
			d.source.Body.(*ast.BlockExpression).Block.Statements[0].(*ast.ExpressionStatement).Expression.(*ast.Identifier).Value = "changed"
		},
		"callee-alias":         func(d *nativeDriver) { d.functions["g"].Name.Value = "changed" },
		"parameter-type-alias": func(d *nativeDriver) { d.source.Parameters[0].Type.(*ast.Identifier).Value = "u64" },
		"return-type-alias":    func(d *nativeDriver) { d.source.ReturnType.(*ast.Identifier).Value = "u64" },
		"forbids-alias": func(d *nativeDriver) {
			d.functions["g"].Forbids = []*ast.EffectName{{Namespace: "Memory", Name: "Allocate"}}
		},
		"function-map": func(d *nativeDriver) { d.functions["extra"] = nativeMaterializationFunction("extra") },
		"effect-alias": func(d *nativeDriver) {
			d.functions["g"].EffectsDeclared = true
			d.functions["g"].Effects = []*ast.EffectName{{Namespace: "Memory", Name: "Allocate"}}
		},
		"record-alias":             func(d *nativeDriver) { d.records["R"].Fields["value"].(*ast.Identifier).Value = "u64" },
		"adt-alias":                func(d *nativeDriver) { d.adts["Choice"].Variants[0].Payload.(*ast.Identifier).Value = "u64" },
		"constant-map":             func(d *nativeDriver) { d.constants["C"] = asm.Constant{Type: "u32", Value: 8} },
		"declarations":             func(d *nativeDriver) { d.declarations += "Other: type = Unit\n" },
		"type-context":             func(d *nativeDriver) { d.tc = typechecker.NewWithPlatformSizes(object.NewEnvironment(), 32, 32) },
		"type-context-alias":       func(d *nativeDriver) { d.tc.SetIntSize(32); d.tc.SetPtrSize(32) },
		"checked-type-fingerprint": func(d *nativeDriver) { d.tcFingerprint = "new-checked-type-context" },
	}
	for name, mutate := range mutations {
		t.Run(name, func(t *testing.T) {
			d := nativeRecipeFixture()
			candidate := opt.Identity(nativegen.Lane{Arch: asm.ArchArm64})
			var first string
			_, _ = d.withMaterializationRecipe(func() (*opt.Selection, error) { first, _ = d.MaterializationKey(candidate); return nil, nil })
			mutate(d)
			want := legacyNativeMaterializationKey(d, candidate.Config.(nativegen.Lane))
			if want == first {
				t.Fatal("mutation control did not change the legacy key")
			}
			if got, err := d.MaterializationKey(candidate); err != nil || got != want {
				t.Fatalf("outside scope reused stale bytes: %q, %v", got, err)
			}
			_, err := d.withMaterializationRecipe(func() (*opt.Selection, error) {
				if got, err := d.MaterializationKey(candidate); err != nil || got != want {
					t.Fatalf("next scope reused stale bytes: %q, %v", got, err)
				}
				return nil, nil
			})
			if err != nil || d.materializationRecipe != nil {
				t.Fatal("recipe escaped its search")
			}
		})
	}
}

func TestNativeMaterializationRecipeClearsOnEveryExit(t *testing.T) {
	d := nativeRecipeFixture()
	failure := errors.New("search stopped")
	if _, err := d.withMaterializationRecipe(func() (*opt.Selection, error) { return nil, failure }); !errors.Is(err, failure) || d.materializationRecipe != nil {
		t.Fatal("error return did not clear the recipe")
	}
	func() {
		defer func() {
			if recover() != failure {
				t.Error("search panic was not preserved")
			}
		}()
		_, _ = d.withMaterializationRecipe(func() (*opt.Selection, error) { panic(failure) })
	}()
	if d.materializationRecipe != nil {
		t.Fatal("panic retained the recipe")
	}
}

func TestNativeMaterializationRecipeIndependentSearches(t *testing.T) {
	shared := nativeRecipeFixture()
	var wait sync.WaitGroup
	for i := range 8 {
		wait.Add(1)
		go func() {
			defer wait.Done()
			// Immutable checked context can be read by distinct drivers; neither
			// a driver nor its mutable search/snapshot is shared between workers.
			d := *shared
			lane := nativegen.Lane{Arch: asm.ArchArm64, Strength: i%2 == 0}
			_, err := d.withMaterializationRecipe(func() (*opt.Selection, error) {
				got, err := d.MaterializationKey(opt.Identity(lane))
				if err != nil || got != legacyNativeMaterializationKey(&d, lane) {
					t.Errorf("worker %d: %q, %v", i, got, err)
				}
				return nil, nil
			})
			if err != nil || d.materializationRecipe != nil {
				t.Errorf("worker %d retained its recipe", i)
			}
		}()
	}
	wait.Wait()
	if shared.materializationRecipe != nil {
		t.Fatal("worker mutated the shared template")
	}
}

// Existing explicitly supplied fingerprints retain their original precedence;
// snapshot reuse must not silently broaden or narrow the old key contract.
func TestNativeMaterializationRecipePreservesExplicitFingerprint(t *testing.T) {
	d := nativeRecipeFixture()
	d.tcFingerprint = "fixed checked context"
	lane := nativegen.Lane{Arch: asm.ArchArm64}
	before := legacyNativeMaterializationKey(d, lane)
	d.tc.SetIntSize(32)
	_, err := d.withMaterializationRecipe(func() (*opt.Selection, error) {
		got, err := d.MaterializationKey(opt.Identity(lane))
		if err != nil || got != before || got != legacyNativeMaterializationKey(d, lane) {
			t.Fatalf("explicit fingerprint precedence changed: %q, %v", got, err)
		}
		return nil, nil
	})
	if err != nil {
		t.Fatal(err)
	}
}

func TestNativeMaterializationRecipeStableConcurrentReaders(t *testing.T) {
	d := nativeRecipeFixture()
	_, err := d.withMaterializationRecipe(func() (*opt.Selection, error) {
		var wait sync.WaitGroup
		for i := range 8 {
			wait.Add(1)
			go func() {
				defer wait.Done()
				lane := nativegen.Lane{Arch: asm.ArchArm64, Strength: i%2 == 0}
				got, err := d.MaterializationKey(opt.Identity(lane))
				if err != nil || got != legacyNativeMaterializationKey(d, lane) {
					t.Errorf("reader %d: %q, %v", i, got, err)
				}
			}()
		}
		wait.Wait() // Readers finish before the exclusive scope is cleared.
		return nil, nil
	})
	if err != nil || d.materializationRecipe != nil {
		t.Fatal("recipe escaped reader scope")
	}
}
