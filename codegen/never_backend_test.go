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
}
