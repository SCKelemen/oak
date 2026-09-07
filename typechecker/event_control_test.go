package typechecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func checkEventControlSource(t *testing.T, source string) []string {
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

func TestArm64EventControlOperationsAreNullaryUnit(t *testing.T) {
	errs := checkEventControlSource(t, `
package main
fn control() -> () {
  arm64.daifset_irq()
  arm64.daifclr_irq()
  arm64.wfi()
  arm64.wfe()
  arm64.sev()
}
`)
	if len(errs) != 0 {
		t.Fatalf("valid event-control program rejected: %v", errs)
	}
}

func TestArm64EventControlRejectsOperands(t *testing.T) {
	errs := checkEventControlSource(t, `
package main
fn bad(value: u64) -> ()
  arm64.wfi(value)
`)
	for _, err := range errs {
		if strings.Contains(err, "takes 0 argument(s), got 1") {
			return
		}
	}
	t.Fatalf("wrong failure: %v", errs)
}
