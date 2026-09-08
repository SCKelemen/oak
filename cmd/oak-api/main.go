package main

import (
	"encoding/json"
	"fmt"
	"os"

	"github.com/SCKelemen/oak/compiler"
)

func main() {
	if len(os.Args) != 4 {
		fmt.Fprintln(os.Stderr, "usage: oak-api PACKAGE VERSION SOURCE.oak")
		os.Exit(2)
	}
	source, err := os.ReadFile(os.Args[3])
	if err != nil {
		fmt.Fprintf(os.Stderr, "read source: %v\n", err)
		os.Exit(2)
	}
	snapshot, err := compiler.New().
		WithPackageName(os.Args[1]).
		WithSource(os.Args[3], string(source)).
		APISnapshot(os.Args[2]).
		Get()
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
