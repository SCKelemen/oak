package gpu

import (
	"context"
	"testing"
)

// The runner builds from the system C compiler and the Metal framework and
// finds a device; a source that does not compile is reported with the
// driver's message.
func TestRunnerProbeAndCheck(t *testing.T) {
	if reason := Available(); reason != "" {
		t.Skip(reason)
	}
	name, err := Device()
	if err != nil || name == "" {
		t.Fatalf("device: %q %v", name, err)
	}
	ctx := context.Background()
	good := "#include <metal_stdlib>\nusing namespace metal;\nkernel void k(device float* y [[buffer(0)]], uint gid [[thread_position_in_grid]]) { y[gid] = 1.0f; }\n"
	if err := Check(ctx, good); err != nil {
		t.Fatalf("a valid kernel must compile on the device: %v", err)
	}
	bad := "#include <metal_stdlib>\nkernel void k(device float* y [[buffer(0)]]) { y[0] = undefined_symbol; }\n"
	if err := Check(ctx, bad); err == nil {
		t.Fatal("an invalid kernel must be reported")
	}
}
