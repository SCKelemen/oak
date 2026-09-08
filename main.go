package main

import (
	"fmt"
	"os"
	"os/user"
	"path/filepath"
	"strings"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/repl"
	"github.com/SCKelemen/oak/testrunner"
)

func main() {
	if len(os.Args) > 1 && os.Args[1] == "test" {
		os.Exit(testrunner.Main(os.Args[2:], os.Stdout, os.Stderr))
	}
	if len(os.Args) > 1 && os.Args[1] == "build" {
		os.Exit(buildPackage(os.Args[2:]))
	}

	if len(os.Args) > 1 {
		// Compile mode: oak file.oak
		filename := os.Args[1]
		if !strings.HasSuffix(filename, ".oak") {
			fmt.Printf("Error: expected .oak file, got %s\n", filename)
			os.Exit(1)
		}

		source, err := os.ReadFile(filename)
		if err != nil {
			fmt.Printf("Error reading file: %v\n", err)
			os.Exit(1)
		}

		output, err := compiler.New().
			WithSource(filename, string(source)).
			EmitC().
			Get()
		if err != nil {
			fmt.Printf("Compilation error: %v\n", err)
			os.Exit(1)
		}

		baseName := strings.TrimSuffix(filename, ".oak")
		outputFile := baseName + ".c"
		if err := os.WriteFile(outputFile, []byte(output), 0644); err != nil {
			fmt.Printf("Error writing output file: %v\n", err)
			os.Exit(1)
		}

		fmt.Printf("Compiled %s -> %s\n", filename, outputFile)
		return
	}

	// REPL mode
	usr, err := user.Current()
	if err != nil {
		panic(err)
	}

	fmt.Printf("Hello %s, welcome to Oak 🌳\n", usr.Username)
	fmt.Printf("Type Oak code or 'exit' to quit\n")
	repl.Start(os.Stdin, os.Stdout)
}

// buildPackage implements `oak build [-o out.c] [dir]`: the package at dir
// (default ".") and everything it imports, resolved through the enclosing
// module's oak.mod (docs/spec/83-modules.md), compile to one C translation
// unit written to out.c (default <dir-name>.c in the current directory).
func buildPackage(args []string) int {
	dir := "."
	output := ""
	for i := 0; i < len(args); i++ {
		switch {
		case args[i] == "-o" && i+1 < len(args):
			output = args[i+1]
			i++
		case strings.HasPrefix(args[i], "-"):
			fmt.Fprintf(os.Stderr, "oak build: unknown flag %s\nusage: oak build [-o out.c] [dir]\n", args[i])
			return 2
		default:
			dir = args[i]
		}
	}
	code, err := compiler.New().WithPackageDir(dir).EmitC().Get()
	if err != nil {
		fmt.Fprintf(os.Stderr, "%v\n", err)
		return 1
	}
	if output == "" {
		abs, err := filepath.Abs(dir)
		if err != nil {
			fmt.Fprintf(os.Stderr, "oak build: %v\n", err)
			return 1
		}
		output = filepath.Base(abs) + ".c"
	}
	if err := os.WriteFile(output, []byte(code), 0o644); err != nil {
		fmt.Fprintf(os.Stderr, "oak build: %v\n", err)
		return 1
	}
	fmt.Printf("Built %s -> %s\n", dir, output)
	return 0
}
