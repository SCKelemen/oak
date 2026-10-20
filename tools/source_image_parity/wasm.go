// Source-image composition fixtures: produce complete Wasm for the exact saved
// production-image source inputs. This helper is regression evidence, not proof
// authority, and does not change the admitted grammar or add main.
package main

import (
	"fmt"
	"os"
	"path/filepath"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/target"
)

func main() {
	if len(os.Args) != 3 {
		fmt.Fprintln(os.Stderr, "usage: source_image_parity FIXTURE_DIRECTORY OUTPUT_DIRECTORY")
		os.Exit(2)
	}
	for _, id := range []string{"mix_and", "mix_or", "mix_xor", "Mix9_and"} {
		path := filepath.Join(os.Args[1], "arm64_"+id+".oak")
		source, err := os.ReadFile(path)
		if err != nil {
			panic(err)
		}
		wasm, err := compiler.New().WithSource(path, string(source)).
			WithTarget(target.Target{OS: target.OSCore, Arch: target.ArchWasm32}).EmitWasm().Get()
		if err != nil {
			panic(err)
		}
		if err := os.MkdirAll(os.Args[2], 0755); err != nil {
			panic(err)
		}
		if err := os.WriteFile(filepath.Join(os.Args[2], id+".wasm"), wasm.Bytes, 0644); err != nil {
			panic(err)
		}
		fmt.Printf("%s: %d original source bytes, %d complete Wasm bytes\n", id, len(source), len(wasm.Bytes))
	}
}
