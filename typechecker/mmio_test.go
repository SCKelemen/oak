package typechecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func checkMmioSource(t *testing.T, source string) []string {
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

func requireMmioError(t *testing.T, errs []string, fragment string) {
	t.Helper()
	for _, err := range errs {
		if strings.Contains(err, fragment) {
			return
		}
	}
	t.Fatalf("errors %v do not contain %q", errs, fragment)
}

func TestMmioTypedReadWriteSurface(t *testing.T) {
	errs := checkMmioSource(t, `
package main
fn load(addr: u64) -> u32
  arm64.mmio_read_rw_u32(arm64.mmio_unsafe_rw_u32(addr))
fn store(addr: u64, value: u32) -> ()
  arm64.mmio_write_rw_u32(arm64.mmio_unsafe_rw_u32(addr), value)
`)
	if len(errs) != 0 {
		t.Fatalf("valid typed MMIO rejected: %v", errs)
	}
}

func TestMmioRejectsWrongAuthority(t *testing.T) {
	errs := checkMmioSource(t, `
package main
fn bad_read(addr: u64) -> u32
  arm64.mmio_read_rw_u32(arm64.mmio_unsafe_wo_u32(addr))
fn bad_write(addr: u64, value: u32) -> ()
  arm64.mmio_write_rw_u32(arm64.mmio_unsafe_ro_u32(addr), value)
`)
	requireMmioError(t, errs, "expects arm64.MMIO[u32,read-write]")
}

func TestMmioRejectsWrongWidth(t *testing.T) {
	errs := checkMmioSource(t, `
package main
fn bad(addr: u64) -> u32
  arm64.mmio_read_rw_u32(arm64.mmio_unsafe_rw_u64(addr))
`)
	requireMmioError(t, errs, "expects arm64.MMIO[u32,read-write]")
}

func TestMmioWriteValueMustMatchWidth(t *testing.T) {
	errs := checkMmioSource(t, `
package main
fn bad(addr: u64, value: u64) -> ()
  arm64.mmio_write_rw_u32(arm64.mmio_unsafe_rw_u32(addr), value)
`)
	requireMmioError(t, errs, "expects u32")
}
