package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestFmtRejectsMissingOperandWithoutPanic(t *testing.T) {
	for name, input := range map[string]string{"pipeline": "fn f(): i32 { x: i32 = 1 |> ; x }", "infix": "x := 1 + ; y := 7", "prefix": "x := -; y := 7"} {
		for _, mode := range []string{"stdout", "-l", "-w"} {
			t.Run(name+"/"+mode, func(t *testing.T) {
				file := filepath.Join(t.TempDir(), name+".oak")
				if err := os.WriteFile(file, []byte(input), 0600); err != nil {
					t.Fatal(err)
				}
				args := []string{file}
				if mode != "stdout" {
					args = append([]string{mode}, args...)
				}
				var panicked any
				safeFmt := func(args []string) (code int) {
					defer func() {
						if r := recover(); r != nil {
							panicked = r
							code = -1
						}
					}()
					return fmtCommand(args)
				}
				code, out := runCLI(t, safeFmt, args)
				if panicked != nil {
					t.Errorf("formatter panicked: %v", panicked)
				}
				if code != 1 || !strings.Contains(out, "does not parse") || !strings.Contains(out, "expected operand after") {
					t.Errorf("missing operand must fail the syntax guard: code=%d output=%q", code, out)
				}
				if got, err := os.ReadFile(file); err != nil || string(got) != input {
					t.Fatalf("invalid input changed: %q, %v", got, err)
				}
			})
		}
	}
}
