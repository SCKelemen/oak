package main

import (
	"context"
	"os"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/prove"
)

// Exercise the real source-only solver route without supplying any Go-lowered
// variants that could win as a fallback. Native/shared-Go inferred typing does
// not authorize an independent source-syntax result or a certificate for it.
func TestInferredPrimitiveExternalSourceRemainsUnsupported(t *testing.T) {
	source, err := os.ReadFile("prove/testdata/inferred_primitive_source.oak")
	if err != nil {
		t.Fatal(err)
	}
	// Compile the real solver as required setup, outside the per-case decision
	// deadline. Cold builds under the race detector can exceed that deadline.
	if _, err := oakSolverBinary(); err != nil {
		t.Fatal(err)
	}
	for _, tc := range []struct {
		name, source string
		supported    bool
	}{
		{"explicit control", strings.Replace(string(source), "x :=", "x: u32 =", 1), true},
		{"inferred", string(source), false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			model, err := compiler.New().WithSyntaxRewrite(prove.Obligations).WithSource("inferred.oak", tc.source).Check().Get()
			if err != nil {
				t.Fatal(err)
			}
			if _, ok := prove.GoSyntax(model, "inferred"); ok != tc.supported {
				t.Fatalf("Go syntax admission=%v, want %v", ok, tc.supported)
			}
			ctx, cancel := context.WithTimeout(t.Context(), 2*time.Minute)
			defer cancel()
			verdicts, err := runOakSolverContext(ctx, []oakTheorem{{Name: "inferred"}}, [][]byte{[]byte(tc.source)}, 0, 65536)
			if err != nil {
				t.Fatal(err)
			}
			if len(verdicts) != 1 {
				t.Fatalf("verdict count=%d", len(verdicts))
			}
			v := verdicts[0]
			if tc.supported {
				if v.Status != 0 || !v.Lowered || v.Winner < 0 {
					t.Fatalf("explicit source control was not independently decided: %+v", v)
				}
			} else if v.Status != 3 || v.Lowered || v.Winner != -1 {
				t.Fatalf("unsupported inferred syntax acquired external source authority: %+v", v)
			}
		})
	}
}
