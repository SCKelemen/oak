package repl

import (
	"bufio"
	"fmt"
	"io"

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

		// Type check the program
		typeChecker := typechecker.New(env)
		typeChecker.CheckProgram(program)
		if len(typeChecker.Errors()) != 0 {
			for _, msg := range typeChecker.Errors() {
				io.WriteString(out, "\t[type error] "+msg+"\n")
			}
			// Continue to evaluation anyway for now
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
