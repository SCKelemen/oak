// Command emit writes the C and the native companion object of one Oak
// source, or of a whole package directory (its module resolved as
// `oak build` resolves it), through the native backend
// (compiler.EmitNative), the way the end-to-end tests build native
// programs; `oak build -emit-c -native` writes the C alone. Usage:
// go run ./benchmarks/native/emit in.oak|dir out (writes out.c and out.o).
package main

import (
	"fmt"
	"os"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/diagnostic"
)

func main() {
	if len(os.Args) != 3 {
		fmt.Fprintln(os.Stderr, "usage: emit in.oak|dir out")
		os.Exit(2)
	}
	comp := compiler.New()
	if info, err := os.Stat(os.Args[1]); err == nil && info.IsDir() {
		comp = comp.WithPackageDir(os.Args[1])
	} else {
		src, err := os.ReadFile(os.Args[1])
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		comp = comp.WithSource(os.Args[1], string(src))
	}
	comp = comp.WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			fmt.Fprintln(os.Stderr, d.Message)
		}
	})
	native, err := comp.EmitNative(compiler.HostObjectFormat()).Get()
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err := os.WriteFile(os.Args[2]+".c", []byte(native.C), 0o644); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err := os.WriteFile(os.Args[2]+".o", native.Object, 0o644); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
