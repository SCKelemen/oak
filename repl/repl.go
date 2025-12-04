package repl

import (
	"bufio"
	"fmt"
	"io"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
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
