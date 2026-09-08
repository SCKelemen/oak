package compiler

import (
	"errors"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/borrowchecker"
	"github.com/SCKelemen/oak/typechecker"
)

var diagnosticCorpusName = regexp.MustCompile(`^(?P<name>.+?)(?P<strict>\.strict)?\.error\.(?P<phase>typecheck|borrowcheck|discipline)\.(?P<code>OAK-[A-Z][0-9]{4})\.oak$`)

func TestDiagnosticCorpus(t *testing.T) {
	root := filepath.Join("testdata", "diagnostics")
	entries, err := os.ReadDir(root)
	if err != nil {
		t.Fatal(err)
	}
	seen := 0
	for _, entry := range entries {
		if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".oak") {
			continue
		}
		match := diagnosticCorpusName.FindStringSubmatch(entry.Name())
		if match == nil {
			t.Errorf("diagnostic corpus file %q does not follow the naming contract", entry.Name())
			continue
		}
		seen++
		fields := map[string]string{}
		for i, name := range diagnosticCorpusName.SubexpNames() {
			if i != 0 && name != "" {
				fields[name] = match[i]
			}
		}
		name := entry.Name()
		t.Run(strings.TrimSuffix(name, ".oak"), func(t *testing.T) {
			source, err := os.ReadFile(filepath.Join(root, name))
			if err != nil {
				t.Fatal(err)
			}
			comp := New().WithSource(filepath.ToSlash(filepath.Join("testdata", "diagnostics", name)), string(source)).WithPackageName("diagnostic")
			if fields["strict"] != "" {
				comp = comp.WithProfile("strict")
			}
			generated, err := comp.EmitC().Get()
			if err == nil {
				t.Fatalf("expected %s/%s rejection, compilation succeeded", fields["phase"], fields["code"])
			}
			if generated != "" {
				t.Fatalf("compiler emitted C for rejected source:\n%s", generated)
			}
			var diagnosticErr *DiagnosticError
			if !errors.As(err, &diagnosticErr) {
				t.Fatalf("expected DiagnosticError, got %T: %v", err, err)
			}
			if diagnosticErr.Phase != fields["phase"] {
				t.Fatalf("phase = %q, want %q", diagnosticErr.Phase, fields["phase"])
			}
			for _, diagnostic := range diagnosticErr.Diagnostics {
				if diagnostic != nil && diagnostic.Code == fields["code"] {
					return
				}
			}
			t.Fatalf("missing diagnostic code %s in %#v", fields["code"], diagnosticErr.Diagnostics)
		})
	}
	if seen == 0 {
		t.Fatal("diagnostic corpus is empty")
	}
}

func TestDiagnosticCorpusCoversStableSourceDiagnostics(t *testing.T) {
	root := filepath.Join("testdata", "diagnostics")
	entries, err := os.ReadDir(root)
	if err != nil {
		t.Fatal(err)
	}
	covered := make(map[string]bool)
	for _, entry := range entries {
		if match := diagnosticCorpusName.FindStringSubmatch(entry.Name()); match != nil {
			for i, name := range diagnosticCorpusName.SubexpNames() {
				if name == "code" {
					covered[match[i]] = true
				}
			}
		}
	}
	stable := []string{
		typechecker.CodeConstraintRequirementMissing,
		typechecker.CodeConstraintRequirementInvalid,
		typechecker.CodeConstraintInferenceFailed,
		typechecker.CodeConstraintUnsatisfied,
		typechecker.CodeMatchNonExhaustive,
		typechecker.CodeMatchRedundantArm,
		typechecker.CodeMatchImpossibleArm,
		typechecker.CodeGADTResultInvalid,
		typechecker.CodeGADTResultMismatch,
		typechecker.CodeClosureCaptureStorage,
		typechecker.CodeExternSignatureNotC,
		typechecker.CodeExternSymbolInvalid,
		typechecker.CodeExternOutsideDefinition,
		string(borrowchecker.CodeBorrowReassign),
		string(borrowchecker.CodeOwnerUsedDuringSpan),
		string(borrowchecker.CodeOwnerWrittenDuringView),
		string(borrowchecker.CodeViewConflictsWithSpan),
		string(borrowchecker.CodeSpanConflictsWithView),
		string(borrowchecker.CodeSpanOverlap),
		string(borrowchecker.CodeBorrowSuspended),
		string(borrowchecker.CodeReborrowOverlap),
		string(borrowchecker.CodeBorrowEscape),
		string(borrowchecker.CodeUnsafeAssumption),
	}
	for _, code := range stable {
		if !covered[code] {
			t.Errorf("stable source-facing diagnostic %s has no public-pipeline corpus witness", code)
		}
	}

	// These codes are intentionally outside the public source contract today.
	// Keeping the reasons here prevents them from becoming silent coverage gaps.
	nonSource := map[string]string{
		string(borrowchecker.CodeBorrowGeneric): "migration fallback for borrow checks that do not yet have a specific stable semantic code",
		typechecker.CodeResourceUsedAfterConsume: "resource flow requires CheckProgramWithResources and a ResourceModel; Compilation does not expose a source opt-in until resource syntax is frozen",
	}
	for code, reason := range nonSource {
		if reason == "" {
			t.Errorf("non-source diagnostic %s lacks an explicit exclusion reason", code)
		}
		if covered[code] {
			t.Errorf("diagnostic %s is marked non-source but also has a public source corpus witness", code)
		}
	}
}
