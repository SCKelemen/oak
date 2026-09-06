package serialize

import (
	"fmt"
	"os"
	"path/filepath"

	"github.com/SCKelemen/oak/codegen"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/lowering"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// PipelineOutputs contains paths to all serialized outputs
type PipelineOutputs struct {
	Tokens     string
	AST        string
	LoweredAST string
	Codegen    string
}

// SerializePipeline runs the full compilation pipeline and serializes each stage to JSONL.
func SerializePipeline(sourceCode string, outputDir string, tc *typechecker.TypeChecker) (*PipelineOutputs, error) {
	if err := os.MkdirAll(outputDir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create output directory: %w", err)
	}

	outputs := &PipelineOutputs{
		Tokens:     filepath.Join(outputDir, "tokens.jsonl"),
		AST:        filepath.Join(outputDir, "ast.jsonl"),
		LoweredAST: filepath.Join(outputDir, "lowered_ast.jsonl"),
		Codegen:    filepath.Join(outputDir, "codegen.jsonl"),
	}

	// Stage 1: raw scanner tokens. Golden lexer output intentionally remains
	// pre-layout so it records exactly what appeared in source text.
	scnr := scanner.New(sourceCode)
	var tokens []token.Token
	for {
		tok := scnr.NextToken()
		tokens = append(tokens, tok)
		if tok.TokenKind == token.EOF {
			break
		}
	}

	if err := SerializeTokens(tokens, outputs.Tokens); err != nil {
		return nil, fmt.Errorf("failed to serialize tokens: %w", err)
	}

	// Stage 2: canonical parser input is layout-normalized. Explicit and
	// indentation-delimited block syntax therefore serialize to the same AST
	// semantics while lexer goldens retain source fidelity.
	p := parser.NewSource(layout.New(scanner.New(sourceCode)))
	program := p.ParseProgram()

	if len(p.Errors()) > 0 {
		return nil, fmt.Errorf("parse errors: %v", p.Errors())
	}

	if err := SerializeAST(program, outputs.AST); err != nil {
		return nil, fmt.Errorf("failed to serialize AST: %w", err)
	}

	// Stage 3: Lowering -> Lowered AST
	// Note: Lowering requires a type checker, so we need to typecheck first
	if tc == nil {
		objEnv := object.NewEnvironment()
		tc = typechecker.New(objEnv)
		tc.CheckProgram(program)
	}

	loweredProgram := lowering.LowerProgram(program, tc)
	if err := SerializeAST(loweredProgram, outputs.LoweredAST); err != nil {
		return nil, fmt.Errorf("failed to serialize lowered AST: %w", err)
	}

	// Stage 4: Codegen -> C code
	cg := codegen.New("main", tc)
	cCode, err := cg.Generate(loweredProgram, tc)
	if err != nil {
		return nil, fmt.Errorf("failed to generate code: %w", err)
	}

	if err := SerializeCodegen(cCode, outputs.Codegen); err != nil {
		return nil, fmt.Errorf("failed to serialize codegen: %w", err)
	}

	return outputs, nil
}
