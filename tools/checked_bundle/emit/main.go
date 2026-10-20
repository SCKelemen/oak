// Command emit records real production outputs for the fixed audit regression.
// It is a fixture producer, not a source of verification authority.
package main

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"path/filepath"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/target"
)

func main() {
	out := flag.String("output", "", "fixture directory")
	flag.Parse()
	if *out == "" {
		panic("--output is required")
	}
	if err := os.MkdirAll(*out, 0755); err != nil {
		panic(err)
	}
	source := []byte("bitwise: (x: u32, y: u32): u32 = x & y\n")
	comp := compiler.New().WithSource("canonical.oak", string(source))
	wasm, err := comp.EmitWasm().Get()
	if err != nil {
		panic(err)
	}
	arm, err := comp.WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchArm64}).EmitNativeObject(asm.ELF).Get()
	if err != nil {
		panic(err)
	}
	rv, err := comp.WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchRiscv64}).EmitNativeObject(asm.ELF).Get()
	if err != nil {
		panic(err)
	}
	manifest := map[string]any{"scope": "Diagnostic production bytes; hashes are not proof authority.", "base_proof_commit": "698f6a7b013df508a831d391fe425f4f27cf4581"}
	for name, data := range map[string][]byte{"source.oak": source, "module.wasm": wasm.Bytes, "arm.o": arm, "rv.o": rv} {
		if err := os.WriteFile(filepath.Join(*out, name), data, 0644); err != nil {
			panic(err)
		}
		hash := sha256.Sum256(data)
		manifest[name] = map[string]any{"length": len(data), "sha256": hex.EncodeToString(hash[:])}
	}
	data, err := json.MarshalIndent(manifest, "", "  ")
	if err != nil {
		panic(err)
	}
	if err := os.WriteFile(filepath.Join(*out, "manifest.json"), append(data, '\n'), 0644); err != nil {
		panic(err)
	}
	fmt.Println(string(data))
}
