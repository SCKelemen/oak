package main

import (
	"fmt"
	"os"
	"os/user"
	"strings"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/repl"
	"github.com/SCKelemen/oak/testrunner"
)

func main() {
	if len(os.Args) > 1 && os.Args[1] == "test" {
		os.Exit(testrunner.Main(os.Args[2:], os.Stdout, os.Stderr))
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

