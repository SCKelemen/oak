package repl

import (
	"bufio"
	"fmt"
	"io"

	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
)

const PROMPT = "🌳>"

func Start(in io.Reader, out io.Writer) {
	scnr := bufio.NewScanner(in)

	for {
		fmt.Printf(PROMPT)
		scanned := scnr.Scan()
		if !scanned {
			return
		}

		ln := scnr.Text()
		lxr := scanner.New(ln)

		for tok := lxr.NextToken(); tok.TokenKind != token.EOF; tok = lxr.NextToken() {
			fmt.Printf("%+v\n", tok)
		}
	}
}
