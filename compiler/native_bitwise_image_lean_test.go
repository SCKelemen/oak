package compiler

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"
)

// TestNativeBitwiseImageLean regenerates complete images from current production
// source/object emission and asm.WriteExecutable. The Go ELF reader only proposes
// writer input; the independent Lean recognizer decodes the final name, address,
// extent and load bytes. No extracted final address is a trusted checker input.
func TestNativeBitwiseImageLean(t *testing.T) {
	if findLake() == "" {
		if os.Getenv("OAK_REQUIRE_NATIVE_IMAGE_LEAN") == "1" {
			t.Fatal("OAK_REQUIRE_NATIVE_IMAGE_LEAN=1 requires lake")
		}
		t.Skip("lake unavailable; formal CI requires complete native-image kernel checks")
	}
	python, err := exec.LookPath("python3")
	if err != nil {
		t.Fatal("native-image fixture gate requires python3")
	}
	root, err := filepath.Abs("..")
	if err != nil {
		t.Fatal(err)
	}
	directory := t.TempDir()
	fresh := filepath.Join(directory, "FreshNativeImages.lean")
	run := func(limit time.Duration, program string, args ...string) {
		t.Helper()
		ctx, cancel := context.WithTimeout(t.Context(), limit)
		defer cancel()
		cmd := exec.CommandContext(ctx, program, args...)
		cmd.Dir = root
		cmd.WaitDelay = 5 * time.Second
		start := time.Now()
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("%s %v failed after %s (context %v): %v\n%s", program, args, time.Since(start), ctx.Err(), err, out)
		}
		t.Logf("%s %v completed in %s\n%s", program, args, time.Since(start), out)
	}
	// Pins make current-writer drift a visible failure requiring profile review;
	// never silently rewrite expected bytes during this regression test.
	run(3*time.Minute, "go", "run", "-p=2", "./tools/native_image_fixtures", "-out", directory, "-verify-pins")
	run(time.Minute, python, "tools/native_image_fixtures/render_lean_fixtures.py", directory, "--output", fresh, "--fresh")
	// This builds only the image recognizer dependency closure. The checker uses
	// bounded single-thread shards, audits exact theorem inventories and rejects
	// any closure outside the same standard-three-axiom allowlist as the model.
	run(22*time.Minute, python, "tools/native_image_fixtures/check.py", "--fixture-source", fresh, "--fresh")
}
