package compiler

import (
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

type diagnosticEvidence struct {
	File   string
	Reason string
}

var sourceDiagnosticDeclaration = regexp.MustCompile(`\bCode[A-Za-z0-9_]+[^=\n]*=\s*"(OAK-[A-Z][0-9]{4})"`)

var diagnosticEvidenceOutsideCorpus = map[string]diagnosticEvidence{
	"OAK-B0000": {Reason: "generic migration fallback; specific stable borrow diagnostics are required for user-facing semantics"},
	"OAK-B0111": {File: "compiler/resource_function_type_contracts_test.go"},
	"OAK-B0112": {File: "compiler/resource_call_exclusivity_test.go"},
	"OAK-B0113": {File: "compiler/e2e_region_returns_test.go"},
	"OAK-B0114": {File: "compiler/resource_callee_authority_test.go"},
	"OAK-B0115": {File: "compiler/resource_callable_boundaries_test.go"},
	"OAK-B0116": {File: "compiler/resource_function_type_contracts_test.go"},
	"OAK-B0117": {File: "compiler/resource_result_contracts_test.go"},
	"OAK-B0118": {File: "compiler/resource_borrowed_results_test.go"},
	"OAK-B0119": {File: "compiler/resource_mutable_reborrows_test.go"},
	"OAK-B0120": {File: "compiler/resource_terminal_obligations_test.go"},
	"OAK-B0121": {File: "compiler/e2e_typestate_test.go"},
	"OAK-B0122": {File: "compiler/e2e_ffi_fnptr_test.go"},
	"OAK-F0104": {File: "compiler/e2e_ffi_spans_test.go"},
	"OAK-F0105": {File: "compiler/e2e_ffi_spans_test.go"},
	"OAK-F0106": {File: "compiler/e2e_ffi_cstrings_test.go"},
	"OAK-F0107": {File: "compiler/e2e_ffi_inbound_test.go"},
	"OAK-F0108": {File: "compiler/e2e_c_exports_test.go"},
	"OAK-F0109": {File: "compiler/e2e_c_exports_test.go"},
	"OAK-F0110": {File: "compiler/e2e_ffi_inbound_test.go"},
	"OAK-F0111": {File: "compiler/e2e_ffi_inbound_test.go"},
	"OAK-F0112": {File: "compiler/e2e_ffi_inbound_test.go"},
	"OAK-F0113": {File: "compiler/e2e_ffi_fnptr_test.go"},
	"OAK-F0114": {File: "compiler/e2e_ffi_const_test.go"},
	"OAK-F0115": {File: "compiler/e2e_ffi_objc_test.go"},
	"OAK-T0502": {File: "compiler/e2e_measured_test.go"},
	"OAK-T0601": {File: "compiler/e2e_assert_values_test.go"},
	"OAK-T0701": {File: "compiler/e2e_guard_wrap_test.go", Reason: "information-severity vet finding; neither default nor strict compilation rejects it"},
}

func diagnosticCorpusCodes(t *testing.T) map[string]bool {
	t.Helper()
	entries, err := os.ReadDir(filepath.Join("testdata", "diagnostics"))
	if err != nil {
		t.Fatal(err)
	}
	covered := make(map[string]bool)
	for _, entry := range entries {
		match := diagnosticCorpusName.FindStringSubmatch(entry.Name())
		if match == nil {
			continue
		}
		for i, name := range diagnosticCorpusName.SubexpNames() {
			if name == "code" {
				covered[match[i]] = true
			}
		}
	}
	return covered
}

func TestEveryDeclaredSemanticDiagnosticHasEvidence(t *testing.T) {
	direct := diagnosticCorpusCodes(t)
	declared := make(map[string][]string)
	for _, dir := range []string{"typechecker", "borrowchecker", "discipline"} {
		root := filepath.Join("..", dir)
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
			for _, match := range sourceDiagnosticDeclaration.FindAllStringSubmatch(string(data), -1) {
				code := match[1]
				rel, _ := filepath.Rel("..", path)
				declared[code] = append(declared[code], filepath.ToSlash(rel))
			}
			return nil
		})
		if err != nil {
			t.Fatal(err)
		}
	}
	if len(declared) == 0 {
		t.Fatal("no semantic diagnostic declarations discovered")
	}
	for code, locations := range declared {
		if direct[code] {
			continue
		}
		ev, ok := diagnosticEvidenceOutsideCorpus[code]
		if !ok {
			t.Errorf("declared source-facing diagnostic %s (%s) has neither a public-pipeline corpus case nor an explicit evidence disposition", code, strings.Join(locations, ", "))
			continue
		}
		if ev.File == "" && ev.Reason == "" {
			t.Errorf("diagnostic %s has an empty evidence disposition", code)
			continue
		}
		if ev.File != "" {
			if _, err := os.Stat(filepath.Join("..", filepath.FromSlash(ev.File))); err != nil {
				t.Errorf("diagnostic %s evidence file %s is missing: %v", code, ev.File, err)
			}
		}
	}
	for code, ev := range diagnosticEvidenceOutsideCorpus {
		if _, ok := declared[code]; !ok {
			t.Errorf("stale diagnostic disposition %s -> %+v: no declaration remains", code, ev)
		}
		if direct[code] {
			t.Errorf("diagnostic %s has a public-pipeline corpus witness and should be removed from the secondary evidence map", code)
		}
	}
}
