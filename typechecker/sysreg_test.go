package typechecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func checkSysRegSource(t *testing.T, source string) []string {
	t.Helper()
	p := parser.New(scanner.New(source))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("parser errors: %v", errs)
	}
	tc := New(object.NewEnvironment())
	tc.CheckProgram(program)
	return tc.Errors()
}

func requireSysRegError(t *testing.T, errs []string, fragment string) {
	t.Helper()
	for _, err := range errs {
		if strings.Contains(err, fragment) {
			return
		}
	}
	t.Fatalf("errors %v do not contain %q", errs, fragment)
}

func TestSysRegReadWriteSurfaceTypes(t *testing.T) {
	errs := checkSysRegSource(t, `
package main
fn configure(value: u64) -> u64 {
  arm64.write_hcr_el2(value)
  arm64.read_hcr_el2()
}
`)
	if len(errs) != 0 {
		t.Fatalf("valid system-register program rejected: %v", errs)
	}
}

func TestSysRegReadOnlyRegisterHasNoWriteMember(t *testing.T) {
	errs := checkSysRegSource(t, `
package main
fn bad(value: u64) -> ()
  arm64.write_esr_el2(value)
`)
	requireSysRegError(t, errs, "no instruction function arm64.write_esr_el2")
}

func TestSysRegWriteRequiresU64(t *testing.T) {
	errs := checkSysRegSource(t, `
package main
fn bad(value: u32) -> ()
  arm64.write_hcr_el2(value)
`)
	requireSysRegError(t, errs, "expects u64")
}

func TestSysRegReadIsNullary(t *testing.T) {
	errs := checkSysRegSource(t, `
package main
fn bad(value: u64) -> u64
  arm64.read_hcr_el2(value)
`)
	requireSysRegError(t, errs, "takes 0 argument(s), got 1")
}
