package compiler

import (
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var stableDiagnosticDeclaration = regexp.MustCompile("\\b(Code[A-Za-z0-9_]*)\\s*(?:diagnostic\\.Code\\s*)?=\\s*\"(OAK-[A-Z][0-9]{4})\"")

type diagnosticDeclaration struct {
	Name string
	Code string
	Path string
}

func stableDiagnosticDeclarations(t *testing.T) []diagnosticDeclaration {
	t.Helper()
	var out []diagnosticDeclaration
	for _, root := range []string{
		".",
		filepath.Join("..", "typechecker"),
		filepath.Join("..", "borrowchecker"),
		filepath.Join("..", "discipline"),
		filepath.Join("..", "modules"),
	} {
		err := filepath.WalkDir(root, func(path string, entry fs.DirEntry, walkErr error) error {
			if walkErr != nil {
				return walkErr
			}
			if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".go") || strings.HasSuffix(entry.Name(), "_test.go") {
				return nil
			}
			data, err := os.ReadFile(path)
			if err != nil {
				return err
			}
			for _, match := range stableDiagnosticDeclaration.FindAllStringSubmatch(string(data), -1) {
				out = append(out, diagnosticDeclaration{Name: match[1], Code: match[2], Path: path})
			}
			return nil
		})
		if err != nil {
			t.Fatal(err)
		}
	}
	return out
}

func compilerTestCorpus(t *testing.T) string {
	t.Helper()
	var corpus strings.Builder
	err := filepath.WalkDir(".", func(path string, entry fs.DirEntry, walkErr error) error {
		if walkErr != nil {
			return walkErr
		}
		if entry.IsDir() || !strings.HasSuffix(entry.Name(), "_test.go") || entry.Name() == "diagnostic_contract_test.go" {
			return nil
		}
		data, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		corpus.Write(data)
		corpus.WriteByte('\n')
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	return corpus.String()
}

func TestStableLanguageDiagnosticsHaveCompilerWitnesses(t *testing.T) {
	declarations := stableDiagnosticDeclarations(t)
	if len(declarations) == 0 {
		t.Fatal("no stable diagnostic declarations discovered")
	}
	corpus := compilerTestCorpus(t)
	excluded := map[string]string{
		"OAK-B0000": "generic migration fallback; source-facing borrow failures must use a specific B01xx code",
	}
	seen := make(map[string]bool)
	for _, declaration := range declarations {
		key := declaration.Code
		if seen[key] {
			continue
		}
		seen[key] = true
		if reason, ok := excluded[key]; ok {
			if reason == "" {
				t.Errorf("%s exclusion has no reason", key)
			}
			continue
		}
		if !strings.Contains(corpus, declaration.Code) && !strings.Contains(corpus, declaration.Name) {
			t.Errorf("%s (%s, declared in %s) has no compiler-level test witness", declaration.Code, declaration.Name, declaration.Path)
		}
	}
	for code, reason := range excluded {
		if reason == "" {
			t.Errorf("%s exclusion has no reason", code)
		}
		if !seen[code] {
			t.Errorf("stale diagnostic exclusion %s", code)
		}
	}
}
