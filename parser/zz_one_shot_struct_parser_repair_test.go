package parser

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// TestOneShotStructTypeParserRepair is a temporary repository-maintenance test.
// It runs only under GitHub Actions, patches the two historical type-declaration
// routers to delegate record/struct products to the type parser, commits the
// result, and removes itself. The next CI run verifies the resulting tree.
func TestOneShotStructTypeParserRepair(t *testing.T) {
	if os.Getenv("GITHUB_ACTIONS") != "true" {
		t.Skip("one-shot repository repair only runs in GitHub Actions")
	}

	wd, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	repo := filepath.Dir(wd)
	parserPath := filepath.Join(repo, "parser", "parser.go")

	data, err := os.ReadFile(parserPath)
	if err != nil {
		t.Fatal(err)
	}
	text := string(data)

	oldLegacy := `	// Check if this is a record type definition or record composition
	// Record type: { field: Type, ... }
	// Record composition: TypeName & { field: Type, ... } or TypeName & TypeName
	if p.currentTokenIs(token.LBRACE) {
		// This is a record type definition
		recordLit := p.parseRecordLiteral()
		if recordLit == nil {
			return nil
		}
		// Store as a single variant with record literal
		variant := &ast.ADTVariant{
			Token:   p.currentToken,
			Name:    adt.Name, // Use ADT name as variant name for record types
			Literal: recordLit,
		}
		adt.Variants = []*ast.ADTVariant{variant}
`
	newLegacy := `	// Check if this is a semantic record, concrete struct, or record composition.
	// Both product forms go through the type parser; struct carries a distinct
	// STRUCT token so later semantic projection can select representation.
	if p.currentTokenIs(token.LBRACE) || p.currentTokenIs(token.STRUCT) {
		recordType := p.parseTypePrimary()
		if recordType == nil {
			return nil
		}
		variant := &ast.ADTVariant{
			Token:   p.currentToken,
			Name:    adt.Name,
			Literal: recordType,
		}
		adt.Variants = []*ast.ADTVariant{variant}
`
	if strings.Count(text, oldLegacy) != 1 {
		t.Fatalf("legacy record router match count = %d, want 1", strings.Count(text, oldLegacy))
	}
	text = strings.Replace(text, oldLegacy, newLegacy, 1)

	oldNamed := `	} else if p.currentTokenIs(token.LBRACE) {
		// This is a record type definition: Name: type = { field: Type, ... }
		// Use parseRecordType() which handles type annotations (field: Type)
		// instead of parseRecordLiteral() which handles values (field: value)
		recordType := p.parseRecordType()
		if recordType == nil {
			return nil
		}
		// parseRecordType() leaves currentToken at the closing brace '}'
		// This is the last token of the ADT definition, so we leave it here
		// ParseProgram will call p.nextToken() to advance from '}' to the start of the next statement
		// Store as a single variant with record type
		variant := &ast.ADTVariant{
			Token:   p.currentToken,
			Name:    adt.Name,   // Use ADT name as variant name for record types
			Literal: recordType, // For record types, we store the type as the "literal"
		}
		adt.Variants = []*ast.ADTVariant{variant}
		// After parseRecordType(), currentToken is at the closing brace '}'
		// This is the last token of the ADT definition
		// ParseProgram will call p.nextToken() to advance to the next statement
`
	newNamed := `	} else if p.currentTokenIs(token.LBRACE) || p.currentTokenIs(token.STRUCT) {
		// Semantic records and concrete structs share product-type parsing. The
		// RecordLiteral AST retains the opening token: LBRACE means semantic shape;
		// STRUCT means a concrete representation policy was explicitly selected.
		recordType := p.parseTypePrimary()
		if recordType == nil {
			return nil
		}
		variant := &ast.ADTVariant{
			Token:   p.currentToken,
			Name:    adt.Name,
			Literal: recordType,
		}
		adt.Variants = []*ast.ADTVariant{variant}
`
	if strings.Count(text, oldNamed) != 1 {
		t.Fatalf("named record router match count = %d, want 1", strings.Count(text, oldNamed))
	}
	text = strings.Replace(text, oldNamed, newNamed, 1)

	if err := os.WriteFile(parserPath, []byte(text), 0o644); err != nil {
		t.Fatal(err)
	}

	run := func(name string, args ...string) {
		t.Helper()
		cmd := exec.Command(name, args...)
		cmd.Dir = repo
		cmd.Stdout = os.Stdout
		cmd.Stderr = os.Stderr
		if err := cmd.Run(); err != nil {
			t.Fatalf("%s %v: %v", name, args, err)
		}
	}

	run("gofmt", "-w", "parser/parser.go")
	run("git", "config", "user.name", "github-actions[bot]")
	run("git", "config", "user.email", "41898282+github-actions[bot]@users.noreply.github.com")
	run("git", "add", "parser/parser.go")
	run("git", "rm", "parser/zz_one_shot_struct_parser_repair_test.go")
	run("git", "commit", "-m", "Parse semantic records and concrete structs as type forms")
	run("git", "push", "origin", "HEAD:feat/record-layout")
}
