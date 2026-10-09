package asm

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func TestLLVMMCDiscovery(t *testing.T) {
	dir := t.TempDir()
	pathDir, fallbackDir := filepath.Join(dir, "path"), filepath.Join(dir, "homebrew")
	for _, directory := range []string{pathDir, fallbackDir} {
		if err := os.Mkdir(directory, 0o755); err != nil {
			t.Fatal(err)
		}
	}
	pathTool := filepath.Join(pathDir, "llvm-mc")
	fallbackTool := filepath.Join(fallbackDir, "llvm-mc")
	for _, tool := range []string{pathTool, fallbackTool} {
		if err := os.WriteFile(tool, []byte("test fixture, never executed\n"), 0o755); err != nil {
			t.Fatal(err)
		}
	}
	t.Setenv("PATH", pathDir)
	if got := lookupLLVMMC([]string{fallbackTool}); got != pathTool {
		t.Fatalf("PATH must take precedence: got %q, want %q", got, pathTool)
	}
	t.Setenv("PATH", t.TempDir())
	if got := lookupLLVMMC([]string{filepath.Join(dir, "missing"), fallbackTool}); got != fallbackTool {
		t.Fatalf("Homebrew fallback: got %q, want %q", got, fallbackTool)
	}
	if err := os.Chmod(fallbackTool, 0o644); err != nil {
		t.Fatal(err)
	}
	if got := lookupLLVMMC([]string{fallbackTool, fallbackDir}); got != "" {
		t.Fatalf("non-executable file or directory accepted: %q", got)
	}
	t.Setenv("PATH", ".")
	t.Setenv("GODEBUG", "execerrdot=1")
	t.Chdir(pathDir)
	if got := lookupLLVMMC(nil); got != "" {
		t.Fatalf("implicit current-directory tool accepted: %q", got)
	}
}

func TestLLVMMCRequiredMode(t *testing.T) {
	if os.Getenv("OAK_TEST_LLVM_MISSING") == "1" {
		llvmMCCandidates = nil
		findLLVMMC(t)
		t.Fatal("missing tool unexpectedly found")
	}
	executable, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	for _, required := range []bool{false, true} {
		t.Run(map[bool]string{false: "optional", true: "required"}[required], func(t *testing.T) {
			t.Setenv("PATH", t.TempDir())
			t.Setenv("OAK_TEST_LLVM_MISSING", "1")
			t.Setenv("OAK_REQUIRE_ORACLES", map[bool]string{false: "", true: "1"}[required])
			out, err := exec.Command(executable, "-test.run=^TestLLVMMCRequiredMode$", "-test.v").CombinedOutput()
			if required {
				if err == nil || !strings.Contains(string(out), "oracle required by OAK_REQUIRE_ORACLES") {
					t.Fatalf("missing required oracle must fail: %v\n%s", err, out)
				}
			} else if err != nil || !strings.Contains(string(out), "--- SKIP:") {
				t.Fatalf("missing optional oracle must skip: %v\n%s", err, out)
			}
		})
	}
}
