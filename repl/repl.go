package repl

import (
	"bufio"
	"fmt"
	"io"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

const PROMPT = "🌳> "

func Start(in io.Reader, out io.Writer) {
	scnr := bufio.NewScanner(in)
	env := object.NewEnvironment()
	// Create a single TypeChecker that persists across REPL inputs
	// This allows variables declared in previous inputs to be available
	typeChecker := typechecker.New(env)

	for {
		fmt.Printf(PROMPT)
		scanned := scnr.Scan()
		if !scanned {
			return
		}

		ln := scnr.Text()
		if ln == "" {
			continue
		}

		lxr := scanner.New(ln)
		p := parser.New(lxr)

		program := p.ParseProgram()
		if len(p.Errors()) != 0 {
			printParserErrors(out, p.Errors())
			continue
		}

		// Check for REPL commands in the parsed program
		// REPL commands are now part of the language syntax
		if len(program.Statements) > 0 {
			if replCmd, ok := program.Statements[0].(*ast.REPLCommand); ok {
				switch replCmd.Name {
				case "exit", "quit":
					fmt.Fprintf(out, "Goodbye!\n")
					return
				case "help":
					fmt.Fprintf(out, "Oak REPL Commands:\n")
					fmt.Fprintf(out, "  :exit, :quit  - Exit the REPL\n")
					fmt.Fprintf(out, "  :help         - Show this help message\n")
					fmt.Fprintf(out, "  :clear         - Clear the screen\n")
					fmt.Fprintf(out, "  :reset         - Reset the environment (clear all variables)\n")
					fmt.Fprintf(out, "  :typeof(expr)  - Show the type of an expression\n")
					continue
				case "clear":
					// ANSI escape code to clear screen and move cursor to top-left
					fmt.Fprintf(out, "\033[2J\033[H")
					continue
				case "reset":
					// Reset environment and type checker
					env = object.NewEnvironment()
					typeChecker = typechecker.New(env)
					fmt.Fprintf(out, "Environment reset.\n")
					continue
				case "typeof":
					// Type check and display the type of an expression or type
					if len(replCmd.Args) == 0 {
						fmt.Fprintf(out, "Usage: :typeof(expression)\n")
						continue
					}
					expr := replCmd.Args[0]
					typeChecker.ClearErrors()

					// typeof() can accept both type expressions (like []i32, [10]Byte) and value expressions
					// Try parsing as type expression first
					var exprType typechecker.Type
					exprType = typeChecker.ParseTypeExpression(expr)

					// If that didn't work, try as value expression
					if exprType == nil {
						typeChecker.ClearErrors()
						exprType = typeChecker.CheckExpression(expr)
					}

					if len(typeChecker.Errors()) > 0 {
						fmt.Fprintf(out, "Type errors:\n")
						for _, err := range typeChecker.Errors() {
							fmt.Fprintf(out, "  %s\n", err)
						}
					} else if exprType != nil {
						fmt.Fprintf(out, "%s\n", exprType.String())
					} else {
						fmt.Fprintf(out, "unknown type\n")
					}
					continue
				}
			}
		}

		// Clear previous errors before type checking
		typeChecker.ClearErrors()
		// Type check the program (reusing the same TypeChecker)
		typeChecker.CheckProgram(program)
		if len(typeChecker.Errors()) != 0 {
			for _, msg := range typeChecker.Errors() {
				io.WriteString(out, "\t[type error] "+msg+"\n")
			}
			// Skip evaluation on type errors
			continue
		}

		val := evaluator.Eval(program, env)
		if val != nil {
			if val.Type() == object.ERROR_OBJ {
				io.WriteString(out, val.Inspect())
				io.WriteString(out, "\n")
			} else if val.Type() != object.NULL_OBJ {
				io.WriteString(out, val.Inspect())
				io.WriteString(out, "\n")
			}
		}
	}

}

func printParserErrors(out io.Writer, errors []string) {
	for _, msg := range errors {
		io.WriteString(out, "\t"+msg+"\n")
	}
}
