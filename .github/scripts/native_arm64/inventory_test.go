package main

import (
	"os"
	"path/filepath"
	"reflect"
	"testing"
)

func fixture(t *testing.T, files map[string]string) string {
	t.Helper()
	root := t.TempDir()
	for name, source := range files {
		path := filepath.Join(root, name)
		if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(source), 0644); err != nil {
			t.Fatal(err)
		}
	}
	return root
}

func TestDiscoverTransitiveHostGuards(t *testing.T) {
	root := fixture(t, map[string]string{
		"compiler/host_test.go": `package compiler
import ( rt "runtime"; "testing" )
func requireARM(t *testing.T) { if rt.GOARCH != "arm64" { t.Skip("native ARM") } }
func helper(t *testing.T) { requireARM(t) }
func cycle(t *testing.T) { helper(t); other(t) }
func other(t *testing.T) { cycle(t) }
func TestNewNativeRoot(t *testing.T) { cycle(t) }
func TestLocalAlias(t *testing.T) { check := requireARM; check(t) }
var literalCheck = func(t *testing.T) { if rt.GOARCH != "arm64" { t.Skip("literal ARM") } }
func TestGlobalLiteral(t *testing.T) { literalCheck(t) }
var globalCheck = requireARM
var callbacks = []func(*testing.T){globalCheck}
func TestGlobalAlias(t *testing.T) { callbacks[0](t) }
type helperObject struct{}
func (h helperObject) requireMethod(t *testing.T) { if rt.GOARCH != "arm64" { t.Skip("method ARM") } }
func TestMethod(t *testing.T) { var h helperObject; h.requireMethod(t) }
func TestMethodValue(t *testing.T) { var h helperObject; check := h.requireMethod; check(t) }
func TestDirect(t *testing.T) { if rt.GOARCH != "arm64" { t.Skipf("native %s", "ARM") } }
func TestOrdinary(t *testing.T) { t.Log("requireARM(t)") /* requireARM(t) */ }
func TestX86(t *testing.T) { if rt.GOARCH != "amd64" { t.Skip("x86") } }
`,
		"asm/asm_arm64_test.go":    "package asm\nimport \"testing\"\nfunc TestArchitectureFile(t *testing.T) {}",
		"asm/constrained_test.go":  "//go:build linux && arm64\n\npackage asm\nimport \"testing\"\nfunc TestConstrained(t *testing.T) {}",
		"testdata/ignored_test.go": "not Go syntax",
	})
	got, err := discover(root)
	if err != nil {
		t.Fatal(err)
	}
	want := []Root{
		{"./asm", "TestArchitectureFile", "asm/asm_arm64_test.go"},
		{"./asm", "TestConstrained", "asm/constrained_test.go"},
		{"./compiler", "TestDirect", "compiler/host_test.go"},
		{"./compiler", "TestGlobalAlias", "compiler/host_test.go"},
		{"./compiler", "TestGlobalLiteral", "compiler/host_test.go"},
		{"./compiler", "TestLocalAlias", "compiler/host_test.go"},
		{"./compiler", "TestMethod", "compiler/host_test.go"},
		{"./compiler", "TestMethodValue", "compiler/host_test.go"},
		{"./compiler", "TestNewNativeRoot", "compiler/host_test.go"},
	}
	if !reflect.DeepEqual(got.Roots, want) {
		t.Fatalf("roots = %#v, want %#v", got.Roots, want)
	}
	if len(got.Skips) != 5 {
		t.Fatalf("skip-site inventory = %#v", got.Skips)
	}
}

func TestSkipSitesCatchNonCanonicalFutureGuard(t *testing.T) {
	root := fixture(t, map[string]string{"x_test.go": `package x
import "testing"
func host() bool { return false }
func TestFuture(t *testing.T) { if !host() { t.Skip("native instruction unavailable") } }
`})
	got, err := discover(root)
	if err != nil {
		t.Fatal(err)
	}
	if len(got.Skips) != 1 || got.Skips[0].Call != `t.Skip("native instruction unavailable")` {
		t.Fatalf("noncanonical new host skip must change the reviewed source inventory: %#v", got)
	}
}

func TestSourceSyntaxErrorFailsClosed(t *testing.T) {
	root := fixture(t, map[string]string{"x_test.go": "package x\nfunc TestBroken("})
	if _, err := discover(root); err == nil {
		t.Fatal("invalid test source accepted")
	}
}

func TestMethodAndInitDoNotCollideWithHelpers(t *testing.T) {
	root := fixture(t, map[string]string{"x_test.go": `package x
func init() {}
func init() {}
type A struct{}
type B struct{}
func (a A) helper() {}
func (b B) helper() {}
`})
	if _, err := discover(root); err != nil {
		t.Fatal(err)
	}
}
