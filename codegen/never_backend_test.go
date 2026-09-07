package codegen

import (
	"strings"
	"testing"
)

func TestNeverBackendSpellingIsPackageIndependent(t *testing.T) {
	generated := generateSourceC(t, `
package hypervisor
fn stop() -> never
  arm64.eret()
`)
	if !strings.Contains(generated, "oak_never oak_hypervisor_stop(") {
		t.Fatalf("package function did not use global never backend spelling:\n%s", generated)
	}
	if strings.Contains(generated, "oak_hypervisor_never") {
		t.Fatalf("builtin never was incorrectly package-mangled:\n%s", generated)
	}
	if got := strings.Count(generated, "typedef u8 oak_never;"); got != 1 {
		t.Fatalf("global never backend carrier emitted %d times, want exactly 1:\n%s", got, generated)
	}
}

func TestNeverBackendCarrierIsPayForUse(t *testing.T) {
	generated := generateSourceC(t, `
package ordinary
fn answer() -> u64
  42
`)
	if strings.Contains(generated, "oak_never") {
		t.Fatalf("ordinary program paid for unused never backend support:\n%s", generated)
	}
}
