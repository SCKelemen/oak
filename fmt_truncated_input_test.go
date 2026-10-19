package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestFmtRefusesTruncatedInput(t *testing.T) {
	for name, input := range map[string]string{
		"block":    "fn bad6(): i32 = {\n    x: i32 = 10",
		"string":   `bad14: string = "hello`,
		"operator": "bad10: i32 = 5 ** 3",
	} {
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
				if code, out := runCLI(t, fmtCommand, args); code != 1 || !strings.Contains(out, "does not parse") {
					t.Fatalf("invalid input must fail the syntax guard: code=%d output=%q", code, out)
				}
				if got, err := os.ReadFile(file); err != nil || string(got) != input {
					t.Fatalf("invalid input was changed: %q, %v", got, err)
				}
			})
		}
	}
}
