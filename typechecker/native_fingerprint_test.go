package typechecker

import "testing"

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
		}
		keys := []tokenKey{first, second}
		if reverse {
			keys[0], keys[1] = keys[1], keys[0]
		}
		for _, key := range keys {
			tc.provenIndices[key] = key == first
			tc.arithmeticTypes[key] = map[tokenKey]string{first: "u32", second: "i64"}[key]
			tc.shiftWidths[key] = map[tokenKey]int{first: 32, second: 64}[key]
			tc.variantResolutions[key] = map[tokenKey]string{first: "Option_u32", second: "Result_i64"}[key]
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
		{"arithmetic type", func(tc *TypeChecker) { tc.arithmeticTypes[first] = "u64" }},
		{"shift width", func(tc *TypeChecker) { tc.shiftWidths[first] = 16 }},
		{"variant resolution", func(tc *TypeChecker) { tc.variantResolutions[first] = "Option_u64" }},
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

func TestNilNativeLoweringFingerprintIsStable(t *testing.T) {
	var checker *TypeChecker
	if first, second := checker.NativeLoweringFingerprint(), checker.NativeLoweringFingerprint(); first == "" || first != second {
		t.Fatalf("nil fingerprints = %q, %q", first, second)
	}
}
