package typechecker

import (
	"testing"

	"github.com/SCKelemen/oak/token"
)

func TestNativeLoweringFingerprintIsOrderIndependentAndComplete(t *testing.T) {
	first := tokenKey{context: "m", line: 3, column: 7, literal: "["}
	second := tokenKey{context: "m", line: 9, column: 2, literal: "+"}
	checker := func(reverse bool) *TypeChecker {
		tc := &TypeChecker{
			intSize:            64,
			ptrSize:            64,
			provenIndices:      map[tokenKey]bool{},
			arithmeticTypes:    map[tokenKey]string{},
			shiftWidths:        map[tokenKey]int{},
			variantResolutions: map[tokenKey]string{},
			expressionTypes:    map[tokenKey]Type{},
		}
		keys := []tokenKey{first, second}
		if reverse {
			keys[0], keys[1] = keys[1], keys[0]
		}
		for _, key := range keys {
			tc.provenIndices[key] = key == first
			if key == first {
				tc.indexProofs = map[tokenKey]IndexProof{key: {
					ID: "proof", Proposition: "index-in-extent", Container: "items", Extent: 4,
					Scope: "m:3:7", Provenance: "checked", Witness: "Oak.Extents.indexUnder",
					Dependencies: []string{"i < len(items)"},
				}}
			}
			tc.arithmeticTypes[key] = map[tokenKey]string{first: "u32", second: "i64"}[key]
			tc.shiftWidths[key] = map[tokenKey]int{first: 32, second: 64}[key]
			tc.variantResolutions[key] = map[tokenKey]string{first: "Option_u32", second: "Result_i64"}[key]
			tc.expressionTypes[key] = map[tokenKey]Type{first: &PrimitiveType{Name: "u32"}, second: &PrimitiveType{Name: "i64"}}[key]
		}
		return tc
	}

	want := checker(false).NativeLoweringFingerprint()
	if got := checker(true).NativeLoweringFingerprint(); got != want {
		t.Fatalf("map insertion order changed fingerprint: %s != %s", got, want)
	}
	mutations := []struct {
		name   string
		mutate func(*TypeChecker)
	}{
		{"integer width", func(tc *TypeChecker) { tc.intSize = 32 }},
		{"pointer width", func(tc *TypeChecker) { tc.ptrSize = 32 }},
		{"proven index", func(tc *TypeChecker) { tc.provenIndices[first] = false }},
		{"index proof", func(tc *TypeChecker) {
			proof := tc.indexProofs[first]
			proof.Container = "other"
			tc.indexProofs[first] = proof
		}},
		{"arithmetic type", func(tc *TypeChecker) { tc.arithmeticTypes[first] = "u64" }},
		{"shift width", func(tc *TypeChecker) { tc.shiftWidths[first] = 16 }},
		{"variant resolution", func(tc *TypeChecker) { tc.variantResolutions[first] = "Option_u64" }},
		{"expression type", func(tc *TypeChecker) { tc.expressionTypes[first] = &PrimitiveType{Name: "u64"} }},
	}
	for _, mutation := range mutations {
		t.Run(mutation.name, func(t *testing.T) {
			changed := checker(false)
			mutation.mutate(changed)
			if got := changed.NativeLoweringFingerprint(); got == want {
				t.Fatalf("mutation did not change fingerprint %s", got)
			}
		})
	}
}

func TestCheckedIndexProofIdentityAndCopies(t *testing.T) {
	tok := token.Token{SemanticContext: "pkg", Line: 9, Column: 4, Literal: "["}
	tc := &TypeChecker{}
	tc.recordCheckedIndexProof(tok, "items", &ArrayType{Length: 8, ElementType: &PrimitiveType{Name: "u32"}}, "index-in-extent", "Oak.Extents.indexUnder", "i < 8")
	first, ok := tc.IndexProof(tok)
	if !ok || first.ID == "" || first.Extent != 8 || first.Container != "items" {
		t.Fatalf("checked proof = %#v, %v", first, ok)
	}
	first.Dependencies[0] = "mutated"
	second, _ := tc.IndexProof(tok)
	if second.Dependencies[0] != "i < 8" {
		t.Fatalf("caller mutated retained proof: %#v", second)
	}
	authority := tc.IndexProofs()
	authority[first.ID] = IndexProof{}
	third, _ := tc.IndexProof(tok)
	if third.ID != first.ID {
		t.Fatalf("caller mutated authority set: %#v", third)
	}
}

func TestNilNativeLoweringFingerprintIsStable(t *testing.T) {
	var checker *TypeChecker
	if first, second := checker.NativeLoweringFingerprint(), checker.NativeLoweringFingerprint(); first == "" || first != second {
		t.Fatalf("nil fingerprints = %q, %q", first, second)
	}
}

func TestNativeLoweringFingerprintIncludesScalarGlobalAuthority(t *testing.T) {
	firstKey := tokenKey{context: "pkg", line: 4, column: 2, literal: "first"}
	secondKey := tokenKey{context: "pkg", line: 7, column: 2, literal: "second"}
	checker := func(reverse bool) *TypeChecker {
		regions := []ScalarGlobalRegion{
			{ID: "region-first", Name: "first", Type: "u32", DeclarationScope: "pkg:1:1", Provenance: "checked", Witness: checkedScalarGlobalRegionProposition},
			{ID: "region-second", Name: "second", Type: "Bool", DeclarationScope: "pkg:2:1", Provenance: "checked", Witness: checkedScalarGlobalRegionProposition},
		}
		keys := []tokenKey{firstKey, secondKey}
		if reverse {
			regions[0], regions[1] = regions[1], regions[0]
			keys[0], keys[1] = keys[1], keys[0]
		}
		tc := &TypeChecker{
			intSize:                  64,
			ptrSize:                  64,
			scalarGlobalDeclarations: map[string]*scalarGlobalDeclaration{},
			scalarGlobalWrites:       map[tokenKey]ScalarGlobalWriteProof{},
		}
		for _, region := range regions {
			tc.scalarGlobalDeclarations[region.Name] = &scalarGlobalDeclaration{region: region, checked: true}
		}
		for _, key := range keys {
			region := regions[0]
			if key == secondKey {
				region = ScalarGlobalRegion{ID: "region-second", Name: "second", Type: "Bool"}
			} else {
				region = ScalarGlobalRegion{ID: "region-first", Name: "first", Type: "u32"}
			}
			id := "write-" + region.Name
			tc.scalarGlobalWrites[key] = ScalarGlobalWriteProof{
				ID: id, Proposition: checkedScalarGlobalWriteProposition,
				RegionID: region.ID, Global: region.Name, Type: region.Type,
				Scope: fmtScope(key), Provenance: "checked", Witness: checkedScalarGlobalWriteProposition,
				Dependencies: []string{"region=" + region.ID, "type=" + region.Type},
			}
		}
		return tc
	}

	want := checker(false).NativeLoweringFingerprint()
	if got := checker(true).NativeLoweringFingerprint(); got != want {
		t.Fatalf("scalar authority insertion order changed fingerprint: %s != %s", got, want)
	}
	mutations := []struct {
		name   string
		mutate func(*TypeChecker)
	}{
		{"region field", func(tc *TypeChecker) { tc.scalarGlobalDeclarations["first"].region.Witness = "changed" }},
		{"write field", func(tc *TypeChecker) {
			proof := tc.scalarGlobalWrites[firstKey]
			proof.Proposition = "changed"
			tc.scalarGlobalWrites[firstKey] = proof
		}},
		{"write dependency", func(tc *TypeChecker) {
			proof := tc.scalarGlobalWrites[firstKey]
			proof.Dependencies[0] = "changed"
			tc.scalarGlobalWrites[firstKey] = proof
		}},
	}
	for _, mutation := range mutations {
		t.Run(mutation.name, func(t *testing.T) {
			changed := checker(false)
			mutation.mutate(changed)
			if got := changed.NativeLoweringFingerprint(); got == want {
				t.Fatalf("scalar authority mutation did not change fingerprint %s", got)
			}
		})
	}
}
