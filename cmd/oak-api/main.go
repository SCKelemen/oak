package main

import (
	"encoding/json"
	"fmt"
	"os"

	"github.com/SCKelemen/oak/compiler"
)

func main() {
	if len(os.Args) != 4 {
		fmt.Fprintln(os.Stderr, "usage: oak-api PACKAGE VERSION SOURCE.oak|PACKAGE_DIR")
		os.Exit(2)
	}
	comp := compiler.New().WithPackageName(os.Args[1])
	if info, err := os.Stat(os.Args[3]); err == nil && info.IsDir() {
		// A package directory is built through the module loader
		// (docs/spec/83-modules.md); the snapshot covers the root package only.
		comp = comp.WithPackageDir(os.Args[3])
	} else {
		source, err := os.ReadFile(os.Args[3])
		if err != nil {
			fmt.Fprintf(os.Stderr, "read source: %v\n", err)
			os.Exit(2)
		}
		comp = comp.WithSource(os.Args[3], string(source))
	}
	snapshot, err := comp.APISnapshot(os.Args[2]).Get()
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	encoder := json.NewEncoder(os.Stdout)
	encoder.SetEscapeHTML(false)
	encoder.SetIndent("", "  ")
	if err := encoder.Encode(snapshot); err != nil {
		fmt.Fprintf(os.Stderr, "encode snapshot: %v\n", err)
		os.Exit(2)
	}
}
