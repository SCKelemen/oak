package compiler

import (
	"context"
	"errors"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func TestAddressTakenCallableCCompilers(t *testing.T) {
	const source = `identity: (x: i32): i32 = x
apply: (f: (i32) -> i32): i32 = f(42)
direct_only: (x: i32): i32 = x + 1
main: (): i32 { g := apply; assert(direct_only(1) == 2); g(identity) }`
	generated, err := New().WithSource("callable_inline.oak", source).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"identity", "apply"} {
		if strings.Contains(generated, "OAK_INLINE i32 oak_"+name+"(") {
			t.Fatalf("address-taken %s forced inline", name)
		}
	}
	if !strings.Contains(generated, "OAK_INLINE i32 oak_direct_only(") {
		t.Fatal("direct-only helper lost forced inlining")
	}
	for _, compiler := range []string{"gcc", "clang"} {
		t.Run(compiler, func(t *testing.T) {
			cc, err := exec.LookPath(compiler)
			if err != nil {
				t.Skipf("%s is not installed", compiler)
			}
			for _, level := range []string{"-O0", "-O1", "-O2"} {
				t.Run(level, func(t *testing.T) {
					dir := t.TempDir()
					input := filepath.Join(dir, "program.c")
					output := filepath.Join(dir, "program")
					if err := os.WriteFile(input, []byte(generated), 0600); err != nil {
						t.Fatal(err)
					}
					ctx, cancel := context.WithTimeout(context.Background(), 20*time.Second)
					defer cancel()
					if log, err := exec.CommandContext(ctx, cc, "-std=c99", "-Werror", level, input, "-o", output).CombinedOutput(); err != nil {
						t.Fatalf("%s %s: %v\n%s", compiler, level, err, log)
					}
					err := exec.CommandContext(ctx, output).Run()
					var status *exec.ExitError
					if !errors.As(err, &status) || status.ExitCode() != 42 {
						t.Fatalf("want exit 42, got %v", err)
					}
				})
			}
		})
	}
}
