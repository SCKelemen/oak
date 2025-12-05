package main

import (
	"fmt"
	"io/ioutil"
	"os"
	"os/user"
	"strings"

	"github.com/SCKelemen/oak/codegen"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/repl"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

func main() {
	if len(os.Args) > 1 {
		// Compile mode: oak file.oak
		filename := os.Args[1]
		if !strings.HasSuffix(filename, ".oak") {
			fmt.Printf("Error: expected .oak file, got %s\n", filename)
			os.Exit(1)
		}

		// Read source file
		source, err := ioutil.ReadFile(filename)
		if err != nil {
			fmt.Printf("Error reading file: %v\n", err)
			os.Exit(1)
		}

		// Parse
		l := scanner.New(string(source))
		p := parser.New(l)
		program := p.ParseProgram()

		if len(p.Errors()) > 0 {
			fmt.Printf("Parser errors:\n")
			for _, err := range p.Errors() {
				fmt.Printf("  %s\n", err)
			}
			os.Exit(1)
		}

		// Type check
		env := object.NewEnvironment()
		tc := typechecker.New(env)
		tc.CheckProgram(program)

		if len(tc.Errors()) > 0 {
			fmt.Printf("Type errors:\n")
			for _, err := range tc.Errors() {
				fmt.Printf("  %s\n", err)
			}
			os.Exit(1)
		}

		// Generate C code
		cg := codegen.New("main", tc)
		cg.SetSourceFile(filename)
		cg.SetSourceText(string(source))
		output, err := cg.Generate(program, tc)
		if err != nil {
			fmt.Printf("Code generation error: %v\n", err)
			os.Exit(1)
		}

		// Write output file
		baseName := strings.TrimSuffix(filename, ".oak")
		outputFile := baseName + ".c"
		err = ioutil.WriteFile(outputFile, []byte(output), 0644)
		if err != nil {
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
