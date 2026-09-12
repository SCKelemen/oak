package testrunner

import (
	"encoding/binary"
	"math"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/codegen/metal/gpu"
)

// Launch targets (docs/spec/110-testing.md, "Launch targets"): test_launch
// runs the kernel on the host and records the launch; the runner replays
// it on the device and compares, or says why it skipped.
func TestLaunchTargets(t *testing.T) {
	files := map[string]string{
		"kernels.oak": `package main
clamp_relu: (x: f32): f32 = x < 0.0 ? 0.0 | x
kernel relu: (gid: u32, x: []f32, y: [*]f32): () = {
  gid < len(y) ? { y[gid] = clamp_relu(x[gid]) }
}
kernel axpy: (gid: u32, a: f32, x: []f32, y: [*]f32, tile: u32): () = {
  base: u32 = gid * tile
  k: u32 = 0
  while k < tile {
    i: u32 = base + k
    i < len(y) ? { y[i] = a * x[i] + y[i] }
    k = k + 1
  }
}
main: (): i32 = 0
`,
		"a_test.oak": `package main
import(testing)
LaunchRelu: (): () {
  x: [4]f32 = [-1.0, 2.0, -3.0, 4.0]
  y: [4]f32 = [0.0, 0.0, 0.0, 0.0]
  test_launch(relu, 4, view(&x), span(&y))
  test_check(y[0] == 0.0 && y[1] == 2.0 && y[2] == 0.0 && y[3] == 4.0, u32(1))
  a: f32 = 2.0
  test_launch(axpy, 2, a, view(&x), span(&y), u32(2))
  test_check(y[1] == 6.0 && y[3] == 12.0, u32(2))
}
TestPlain: (): () { test_check(true, u32(3)) }
`,
		"oak.mod": "module example.com/launch\noak 0.1.0\n",
	}
	dir := fixture(t, files)
	code, results, stderr := runCLI(t, "-run", "LaunchRelu", dir)
	if code != 0 || len(results) != 1 || results[0].Status != "pass" || results[0].Kind != "launch" || results[0].Launches != 2 {
		t.Fatalf("launch target: %d %+v %s", code, results, stderr)
	}
	if reason := gpu.Available(); reason == "" {
		if strings.HasPrefix(results[0].Device, "skipped") || results[0].Device == "" {
			t.Fatalf("with a device the launches replay on it: %+v", results[0])
		}
	} else if !strings.HasPrefix(results[0].Device, "skipped: ") {
		t.Fatalf("without a device the result says why: %+v", results[0])
	}
	// -device=false records and counts but does not replay.
	code, results, stderr = runCLI(t, "-device=false", "-run", "LaunchRelu", dir)
	if code != 0 || len(results) != 1 || results[0].Launches != 2 || results[0].Device != "skipped: -device=false" {
		t.Fatalf("launch target without device: %d %+v %s", code, results, stderr)
	}
	// A plain test in the same package records no launches.
	code, results, _ = runCLI(t, "-run", "TestPlain", dir)
	if code != 0 || len(results) != 1 || results[0].Launches != 0 || results[0].Device != "" {
		t.Fatalf("plain test: %d %+v", code, results)
	}
}

// The divergence text names the launch, the span, and the first differing
// element in the element's type.
func TestLaunchDivergenceText(t *testing.T) {
	host := make([]byte, 8)
	device := make([]byte, 8)
	binary.LittleEndian.PutUint32(host[0:], math.Float32bits(1))
	binary.LittleEndian.PutUint32(host[4:], math.Float32bits(2.5))
	binary.LittleEndian.PutUint32(device[0:], math.Float32bits(1))
	binary.LittleEndian.PutUint32(device[4:], math.Float32bits(2.75))
	text := describeDivergence(3, "axpy", launchArg{Name: "y", Kind: "span", Element: "f32", Out: host}, device)
	if text != "launch 3 of axpy: span y element 1: device 2.75, host 2.5" {
		t.Fatalf("divergence text: %q", text)
	}
}
