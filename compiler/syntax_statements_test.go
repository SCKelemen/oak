package compiler

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var statementCaseToken = regexp.MustCompile(`case token\.([A-Z_]+):`)

var syntaxStatementWitnesses = map[string]string{
	"PACKAGE": "packages/package.parse.oak",
	"IMPORT": "packages/import.parse.oak",
	"TYPE": "adts/type_keyword_legacy.parse.oak",
	"INTERFACE": "interfaces/keyword_legacy.parse.oak",
	"FN": "functions/fn_form.exit42.oak",
	"WHILE": "functions/variadic.exit42.oak",
	"UNSAFE": "unsafe/block.check.oak",
	"IDENT": "declarations/typed.exit42.oak",
	"SEMI": "declarations/semicolon_block.exit42.oak",
	"COLON": "repl/exit.parse.oak",
}

func TestEveryStatementEntryPointHasCorpusEvidence(t *testing.T) {
	source, err := os.ReadFile(filepath.Join("..", "parser", "parser.go"))
	if err != nil {
		t.Fatal(err)
	}
	text := string(source)
	start := strings.Index(text, "func (p *Parser) parseStatement() ast.Statement")
	if start < 0 {
		t.Fatal("parseStatement entry point not found")
	}
	endRel := strings.Index(text[start:], "func (p *Parser) parseExpressionStatement")
	if endRel < 0 {
		t.Fatal("parseStatement end marker not found")
	}
	body := text[start : start+endRel]
	seen := make(map[string]bool)
	for _, match := range statementCaseToken.FindAllStringSubmatch(body, -1) {
		tokenName := match[1]
		seen[tokenName] = true
		witness, ok := syntaxStatementWitnesses[tokenName]
		if !ok {
			t.Errorf("statement token %s has no syntax-corpus witness", tokenName)
			continue
		}
		if _, ok := syntaxContracts[witness]; !ok {
			t.Errorf("statement token %s points at uncontracted witness %s", tokenName, witness)
		}
	}
	for _, special := range []struct {
		token string
		needle string
	}{
		{"SEMI", "p.currentTokenIs(token.SEMI)"},
		{"COLON", "p.currentTokenIs(token.COLON) && p.peekTokenIs(token.IDENT)"},
	} {
		if strings.Contains(body, special.needle) {
			seen[special.token] = true
			if _, ok := syntaxStatementWitnesses[special.token]; !ok {
				t.Errorf("special statement route %s has no syntax-corpus witness", special.token)
			}
		}
	}
	for tokenName, witness := range syntaxStatementWitnesses {
		if !seen[tokenName] {
			t.Errorf("stale statement witness %s -> %s: parseStatement no longer exposes that route", tokenName, witness)
		}
	}
}
