package serialize

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"

	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/typechecker"
)

// LoadGoldenDir is LoadGolden with an explicit corpus directory.
func LoadGoldenDir(name string, baseStageNum int, goldenDir string) (*GoldenOutputs, error) {
	outputs := &GoldenOutputs{
		Source:        filepath.Join(goldenDir, fmt.Sprintf("%s_%d_source.oak", name, baseStageNum+0)),
		Lexer:         filepath.Join(goldenDir, fmt.Sprintf("%s_%d_lexer.jsonl", name, baseStageNum+1)),
		Parser:        filepath.Join(goldenDir, fmt.Sprintf("%s_%d_parser.jsonl", name, baseStageNum+2)),
		AST:           filepath.Join(goldenDir, fmt.Sprintf("%s_%d_ast.json", name, baseStageNum+3)),
		Typechecker:   filepath.Join(goldenDir, fmt.Sprintf("%s_%d_typechecker.jsonl", name, baseStageNum+4)),
		Lowering:      filepath.Join(goldenDir, fmt.Sprintf("%s_%d_lowering.json", name, baseStageNum+5)),
		BorrowChecker: filepath.Join(goldenDir, fmt.Sprintf("%s_%d_borrowchecker.jsonl", name, baseStageNum+6)),
		Codegen:       filepath.Join(goldenDir, fmt.Sprintf("%s_%d_codegen.c", name, baseStageNum+7)),
	}

	for _, path := range []string{
		outputs.Source, outputs.Lexer, outputs.Parser, outputs.AST,
		outputs.Typechecker, outputs.Lowering, outputs.BorrowChecker, outputs.Codegen,
	} {
		if _, err := os.Stat(path); os.IsNotExist(err) {
			return nil, fmt.Errorf("golden file does not exist: %s", path)
		}
	}
	return outputs, nil
}

// VerifyGoldenCase regenerates one corpus case into scratchDir and compares
// every stage against the recorded corpus in expectedDir. It returns one
// human-readable line per mismatching stage; an empty slice means the case
// matches exactly.
func VerifyGoldenCase(tc GoldenCase, expectedDir, scratchDir string) ([]string, error) {
	expected, err := LoadGoldenDir(tc.Name, 0, expectedDir)
	if err != nil {
		return nil, err
	}

	objEnv := object.NewEnvironment()
	tcTypeChecker := typechecker.New(objEnv)
	actual, err := SerializeToGoldenDir(tc.Name, 0, tc.SourceCode, tcTypeChecker, scratchDir)
	if err != nil {
		return nil, fmt.Errorf("regenerating %s: %w", tc.Name, err)
	}

	var mismatches []string

	jsonlStages := []struct{ name, expected, actual string }{
		{"lexer", expected.Lexer, actual.Lexer},
		{"parser", expected.Parser, actual.Parser},
		{"typechecker", expected.Typechecker, actual.Typechecker},
		{"borrowchecker", expected.BorrowChecker, actual.BorrowChecker},
	}
	for _, stage := range jsonlStages {
		equal, line1, line2, desc, err := CompareJSONLFiles(stage.expected, stage.actual)
		if err != nil {
			mismatches = append(mismatches, fmt.Sprintf("%s/%s: comparison failed: %v", tc.Name, stage.name, err))
			continue
		}
		if !equal {
			mismatches = append(mismatches, fmt.Sprintf("%s/%s: differs at line %d/%d: %s", tc.Name, stage.name, line1, line2, desc))
		}
	}

	jsonStages := []struct{ name, expected, actual string }{
		{"ast", expected.AST, actual.AST},
		{"lowering", expected.Lowering, actual.Lowering},
	}
	for _, stage := range jsonStages {
		same, err := jsonFilesEqual(stage.expected, stage.actual)
		if err != nil {
			mismatches = append(mismatches, fmt.Sprintf("%s/%s: comparison failed: %v", tc.Name, stage.name, err))
			continue
		}
		if !same {
			mismatches = append(mismatches, fmt.Sprintf("%s/%s: JSON differs", tc.Name, stage.name))
		}
	}

	expectedCode, err := os.ReadFile(expected.Codegen)
	if err != nil {
		return nil, fmt.Errorf("reading expected C: %w", err)
	}
	actualCode, err := os.ReadFile(actual.Codegen)
	if err != nil {
		return nil, fmt.Errorf("reading regenerated C: %w", err)
	}
	if string(expectedCode) != string(actualCode) {
		mismatches = append(mismatches, fmt.Sprintf("%s/codegen: C output differs", tc.Name))
	}

	return mismatches, nil
}

func jsonFilesEqual(expectedPath, actualPath string) (bool, error) {
	expectedData, err := os.ReadFile(expectedPath)
	if err != nil {
		return false, err
	}
	actualData, err := os.ReadFile(actualPath)
	if err != nil {
		return false, err
	}
	var expectedJSON, actualJSON interface{}
	if err := json.Unmarshal(expectedData, &expectedJSON); err != nil {
		return false, fmt.Errorf("expected JSON invalid: %w", err)
	}
	if err := json.Unmarshal(actualData, &actualJSON); err != nil {
		return false, fmt.Errorf("actual JSON invalid: %w", err)
	}
	expectedNormalized, err := json.Marshal(expectedJSON)
	if err != nil {
		return false, err
	}
	actualNormalized, err := json.Marshal(actualJSON)
	if err != nil {
		return false, err
	}
	return string(expectedNormalized) == string(actualNormalized), nil
}
