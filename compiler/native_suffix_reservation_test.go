package compiler

import (
	"errors"
	"strings"
	"testing"
)

func TestFrontendReservesNativeABISuffixes(t *testing.T) {
	for _, suffix := range []string{"_neon_abi", "_rvv_abi"} {
		t.Run(suffix, func(t *testing.T) {
			name := "user_function" + suffix
			source := name + ": (): u32 = u32(1)\nmain: (): u32 = " + name + "()\n"
			root := writeModule(t, map[string]string{
				"oak.mod":  helloManifest,
				"main.oak": "package main\n\n" + source,
			})
			for mode, compilation := range map[string]Compilation{
				"module":      New().WithPackageDir(root),
				"single file": New().WithSource("main.oak", source),
			} {
				t.Run(mode, func(t *testing.T) {
					_, err := compilation.SemanticModel().Get()
					if err == nil {
						t.Fatalf("source identifier ending in %q compiled", suffix)
					}
					var diagnostics *DiagnosticError
					if !errors.As(err, &diagnostics) {
						t.Fatalf("error = %T %v, want *DiagnosticError", err, err)
					}
					found := false
					for _, diagnostic := range diagnostics.Diagnostics {
						if diagnostic.Code == CodeReservedIdentifier && strings.Contains(diagnostic.Message, "ends in reserved native ABI suffix") {
							found = true
							if err := diagnostic.Validate(); err != nil {
								t.Fatalf("invalid diagnostic: %v", err)
							}
						}
					}
					if !found {
						t.Fatalf("diagnostics lack %s and reserved-suffix message: %v", CodeReservedIdentifier, err)
					}
				})
			}
		})
	}
}

func TestFrontendAllowsNearbyUnreservedNativeName(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  helloManifest,
		"main.oak": "package main\n\nuser_function_neon_api: (): u32 = u32(1)\nmain: (): u32 = user_function_neon_api()\n",
	})
	if _, err := New().WithPackageDir(root).SemanticModel().Get(); err != nil {
		t.Fatalf("nearby unreserved identifier was rejected: %v", err)
	}
}

func TestFrontendReservesNativeABISuffixImportAliases(t *testing.T) {
	for _, suffix := range []string{"_neon_abi", "_rvv_abi"} {
		t.Run(suffix, func(t *testing.T) {
			alias := "dep" + suffix
			root := writeModule(t, map[string]string{
				"oak.mod": helloManifest,
				"dep/dep.oak": `package dep

pub answer: (): u32 = u32(42)
`,
				"main.oak": "package main\n\n" + alias + " := import(\"example.com/hello/dep\")\n\nmain: (): u32 = " + alias + ".answer()\n",
			})
			_, err := New().WithPackageDir(root).SemanticModel().Get()
			if err == nil {
				t.Fatalf("import alias ending in %q compiled", suffix)
			}
			var diagnostics *DiagnosticError
			if !errors.As(err, &diagnostics) {
				t.Fatalf("error = %T %v, want *DiagnosticError", err, err)
			}
			for _, diagnostic := range diagnostics.Diagnostics {
				if diagnostic.Code == CodeReservedIdentifier && strings.Contains(diagnostic.Message, "import alias") {
					return
				}
			}
			t.Fatalf("diagnostics lack reserved import-alias error: %v", err)
		})
	}
}
