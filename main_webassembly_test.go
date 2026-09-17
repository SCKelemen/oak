package main

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/SCKelemen/oak/wasm/check"
)

func TestBuildWasm(t *testing.T) {
	t.Setenv("OAKOPT", os.Getenv("OAKOPT"))
	root := writeTree(t, map[string]string{"main.oak": "main: (): i32 = 42", "other/main.oak": "main: (): i32 = 7"})
	output := filepath.Join(root, "main.wasm")
	if code := buildPackage([]string{"-target", "core/wasm32", "-o", output, filepath.Join(root, "main.oak")}); code != 0 {
		t.Fatalf("exit=%d", code)
	}
	bytes, err := os.ReadFile(output)
	if err != nil || len(bytes) < 8 || string(bytes[:4]) != "\x00asm" {
		t.Fatal("no Wasm binary", err)
	}
	if _, err := check.Validate(bytes); err != nil {
		t.Fatal("CLI wrote invalid Wasm bytes", err)
	}
	for _, args := range [][]string{{"-verified"}, {"-native"}, {"-emit-c"}, {"-cpu", "m4"}, {"-asm", "native"}, {"-opt", "3"}, {"-link", "oak"}} {
		badOutput := filepath.Join(root, "refused.wasm")
		all := append([]string{"-target", "core/wasm32", "-o", badOutput}, args...)
		all = append(all, filepath.Join(root, "main.oak"))
		if code := buildPackage(all); code != 2 {
			t.Errorf("%v exit=%d", args, code)
		}
		if _, err := os.Stat(badOutput); !os.IsNotExist(err) {
			t.Fatal("refused build wrote an artifact")
		}
	}
	if code := buildPackage([]string{"-target", "core/wasm32", filepath.Join(root, "main.oak"), filepath.Join(root, "other/main.oak")}); code != 2 {
		t.Fatalf("multiple Wasm inputs: exit=%d", code)
	}
}
