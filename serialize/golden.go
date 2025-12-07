package serialize

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strconv"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/borrowchecker"
	"github.com/SCKelemen/oak/codegen"
	"github.com/SCKelemen/oak/lowering"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// GoldenOutputs contains paths to all golden files
type GoldenOutputs struct {
	Source        string
	Lexer         string
	Parser        string
	AST           string
	Typechecker   string
	Lowering      string
	BorrowChecker string
	Codegen       string
}

// SerializeToGolden runs the full compilation pipeline and serializes each stage
// to the golden directory using the naming convention: {name}_{stage_num}_{stage}.{ext}
func SerializeToGolden(name string, stageNum int, sourceCode string, tc *typechecker.TypeChecker) (*GoldenOutputs, error) {
	goldenDir := "golden"
	if err := os.MkdirAll(goldenDir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create golden directory: %w", err)
	}

	outputs := &GoldenOutputs{
		Source:        filepath.Join(goldenDir, fmt.Sprintf("%s_%d_source.oak", name, stageNum)),
		Lexer:         filepath.Join(goldenDir, fmt.Sprintf("%s_%d_lexer.jsonl", name, stageNum)),
		Parser:        filepath.Join(goldenDir, fmt.Sprintf("%s_%d_parser.jsonl", name, stageNum)),
		AST:           filepath.Join(goldenDir, fmt.Sprintf("%s_%d_ast.json", name, stageNum)),
		Typechecker:   filepath.Join(goldenDir, fmt.Sprintf("%s_%d_typechecker.jsonl", name, stageNum)),
		Lowering:      filepath.Join(goldenDir, fmt.Sprintf("%s_%d_lowering.json", name, stageNum)),
		BorrowChecker: filepath.Join(goldenDir, fmt.Sprintf("%s_%d_borrowchecker.jsonl", name, stageNum)),
		Codegen:       filepath.Join(goldenDir, fmt.Sprintf("%s_%d_codegen.c", name, stageNum)),
	}

	// Write source file
	if err := os.WriteFile(outputs.Source, []byte(sourceCode), 0644); err != nil {
		return nil, fmt.Errorf("failed to write source file: %w", err)
	}

	// Stage 1: Scanner -> Tokens
	scnr := scanner.New(sourceCode)
	var tokens []token.Token
	for {
		tok := scnr.NextToken()
		tokens = append(tokens, tok)
		if tok.TokenKind == token.EOF {
			break
		}
	}

	if err := SerializeTokens(tokens, outputs.Lexer); err != nil {
		return nil, fmt.Errorf("failed to serialize tokens: %w", err)
	}

	// Stage 2: Parser -> AST
	p := parser.New(scanner.New(sourceCode))
	program := p.ParseProgram()

	// Serialize parser errors (even if there are errors, we still want to capture them)
	parserErrors := p.Errors()
	if len(parserErrors) > 0 {
		// Serialize errors to parser.jsonl
		if err := SerializeErrors(parserErrors, outputs.Parser); err != nil {
			return nil, fmt.Errorf("failed to serialize parser errors: %w", err)
		}
		// Still try to serialize AST if program is not nil (partial parse)
		if program != nil {
			if err := SerializeASTToJSON(program, outputs.AST); err != nil {
				// If AST serialization fails, write an error note
				errorNote := fmt.Sprintf(`{"error": "Failed to serialize AST: %v"}`, err)
				if writeErr := os.WriteFile(outputs.AST, []byte(errorNote), 0644); writeErr != nil {
					return nil, fmt.Errorf("failed to write AST error: %w", writeErr)
				}
			}
		} else {
			// Program is nil, write error note
			errorNote := `{"error": "Parser failed, no AST generated"}`
			if err := os.WriteFile(outputs.AST, []byte(errorNote), 0644); err != nil {
				return nil, fmt.Errorf("failed to write AST error note: %w", err)
			}
		}
	} else {
		// If no errors, serialize the AST structure
		if err := SerializeASTToJSON(program, outputs.AST); err != nil {
			return nil, fmt.Errorf("failed to serialize AST: %w", err)
		}
		// Also write to parser.jsonl for consistency (success marker)
		writer, err := NewJSONLWriter(outputs.Parser)
		if err != nil {
			return nil, fmt.Errorf("failed to create parser writer: %w", err)
		}
		successEntry := map[string]interface{}{
			"type":    "success",
			"message": "Parsing succeeded",
		}
		if err := writer.WriteLine(successEntry); err != nil {
			writer.Close()
			return nil, fmt.Errorf("failed to write parser success: %w", err)
		}
		writer.Close()
	}

	// Stage 3: Typechecker
	if tc == nil {
		objEnv := object.NewEnvironment()
		tc = typechecker.New(objEnv)
	}
	tc.CheckProgram(program)

	// Serialize typechecker output (including errors)
	if err := SerializeTypechecker(tc, outputs.Typechecker); err != nil {
		return nil, fmt.Errorf("failed to serialize typechecker: %w", err)
	}

	// Stage 4: Lowering -> Lowered AST
	loweredProgram := lowering.LowerProgram(program, tc)
	if err := SerializeASTToJSON(loweredProgram, outputs.Lowering); err != nil {
		return nil, fmt.Errorf("failed to serialize lowered AST: %w", err)
	}

	// Stage 5: Borrow Checker
	bc := borrowchecker.New()
	bc.CheckProgram(program, tc.Env())

	// Serialize borrow checker output (including errors)
	if err := SerializeBorrowChecker(bc, outputs.BorrowChecker); err != nil {
		return nil, fmt.Errorf("failed to serialize borrow checker: %w", err)
	}

	// Stage 6: Codegen -> C code
	// Only generate code if there are no errors
	typecheckerErrors := tc.Errors()
	borrowErrors := bc.Errors()
	if len(typecheckerErrors) == 0 && len(borrowErrors) == 0 {
		cg := codegen.New("main", tc)
		cCode, err := cg.Generate(loweredProgram, tc)
		if err != nil {
			// Write error to codegen file
			if writeErr := os.WriteFile(outputs.Codegen, []byte(fmt.Sprintf("// Codegen error: %v\n", err)), 0644); writeErr != nil {
				return nil, fmt.Errorf("failed to write codegen error: %w", writeErr)
			}
		} else {
			if err := os.WriteFile(outputs.Codegen, []byte(cCode), 0644); err != nil {
				return nil, fmt.Errorf("failed to write codegen output: %w", err)
			}
		}
	} else {
		// Write placeholder indicating errors prevented codegen
		errorMsg := fmt.Sprintf("// Codegen skipped due to errors\n// Typechecker errors: %d\n// Borrow checker errors: %d\n",
			len(typecheckerErrors), len(borrowErrors))
		if err := os.WriteFile(outputs.Codegen, []byte(errorMsg), 0644); err != nil {
			return nil, fmt.Errorf("failed to write codegen placeholder: %w", err)
		}
	}

	return outputs, nil
}

// SerializeASTToJSON serializes an AST to a single JSON file (not JSONL, since it's a tree)
func SerializeASTToJSON(program *ast.Program, outputPath string) error {
	// Create directory if needed
	dir := filepath.Dir(outputPath)
	if err := os.MkdirAll(dir, 0755); err != nil {
		return fmt.Errorf("failed to create directory: %w", err)
	}

	// Serialize program to JSON structure
	programJSON := map[string]interface{}{
		"type":     "Program",
		"statements": make([]interface{}, 0, len(program.Statements)),
	}

	statements := make([]interface{}, 0, len(program.Statements))
	for _, stmt := range program.Statements {
		nodeJSON, err := serializeNode(stmt)
		if err != nil {
			return fmt.Errorf("failed to serialize statement: %w", err)
		}
		statements = append(statements, nodeJSON)
	}
	programJSON["statements"] = statements

	// Write as pretty-printed JSON
	data, err := json.MarshalIndent(programJSON, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal JSON: %w", err)
	}

	if err := os.WriteFile(outputPath, data, 0644); err != nil {
		return fmt.Errorf("failed to write JSON file: %w", err)
	}

	return nil
}

// SerializeErrors writes errors to a JSONL file
func SerializeErrors(errors []string, outputPath string) error {
	writer, err := NewJSONLWriter(outputPath)
	if err != nil {
		return err
	}
	defer writer.Close()

	for i, errMsg := range errors {
		errorEntry := map[string]interface{}{
			"error_index": i,
			"message":     errMsg,
		}
		if err := writer.WriteLine(errorEntry); err != nil {
			return fmt.Errorf("failed to write error: %w", err)
		}
	}

	return nil
}

// LoadGolden loads a golden file set for comparison
func LoadGolden(name string, stageNum int) (*GoldenOutputs, error) {
	goldenDir := "golden"
	outputs := &GoldenOutputs{
		Source:        filepath.Join(goldenDir, fmt.Sprintf("%s_%d_source.oak", name, stageNum)),
		Lexer:         filepath.Join(goldenDir, fmt.Sprintf("%s_%d_lexer.jsonl", name, stageNum)),
		Parser:        filepath.Join(goldenDir, fmt.Sprintf("%s_%d_parser.jsonl", name, stageNum)),
		AST:           filepath.Join(goldenDir, fmt.Sprintf("%s_%d_ast.json", name, stageNum)),
		Typechecker:   filepath.Join(goldenDir, fmt.Sprintf("%s_%d_typechecker.jsonl", name, stageNum)),
		Lowering:      filepath.Join(goldenDir, fmt.Sprintf("%s_%d_lowering.json", name, stageNum)),
		BorrowChecker: filepath.Join(goldenDir, fmt.Sprintf("%s_%d_borrowchecker.jsonl", name, stageNum)),
		Codegen:       filepath.Join(goldenDir, fmt.Sprintf("%s_%d_codegen.c", name, stageNum)),
	}

	// Verify all files exist
	for _, path := range []string{
		outputs.Source,
		outputs.Lexer,
		outputs.Parser,
		outputs.AST,
		outputs.Typechecker,
		outputs.Lowering,
		outputs.BorrowChecker,
		outputs.Codegen,
	} {
		if _, err := os.Stat(path); os.IsNotExist(err) {
			return nil, fmt.Errorf("golden file does not exist: %s", path)
		}
	}

	return outputs, nil
}
