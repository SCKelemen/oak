package main

import (
	"encoding/json"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/stdlib"
)

func nativeReportFixture() (compiler.NativeBuildReport, compiler.NativeBuildInventory) {
	inputs := []compiler.NativeBuildInput{}
	rows := []compiler.NativeBuildFunction{}
	for _, status := range []string{"proven", "witnessed", "trusted", "c-fallback"} {
		input := compiler.NativeBuildInput{Name: status, SourceSHA256: strings.Repeat("1", 64)}
		inputs = append(inputs, input)
		candidate := compiler.NativeBuildCandidate{Name: "identity", BodySHA256: strings.Repeat("2", 64), RecipeSHA256: strings.Repeat("3", 64), Outcome: status, Message: "actual verifier verdict"}
		row := compiler.NativeBuildFunction{Input: input, Status: status, Reason: "actual completion reason", Callees: []string{}, Considered: 1, Materialized: 1, Selected: &candidate, Validations: []compiler.NativeBuildCandidate{candidate}}
		if status == "c-fallback" {
			row.Materialized = 0
			row.Selected = nil
			row.Validations = []compiler.NativeBuildCandidate{}
		}
		rows = append(rows, row)
	}
	expected := compiler.NativeBuildInventory{Eligible: inputs, Externs: []compiler.NativeBuildInput{{Name: "external", ExternSymbol: "write", SourceSHA256: strings.Repeat("4", 64)}}}
	return compiler.NativeBuildReport{SchemaVersion: 1, Inventory: expected, Functions: rows}, expected
}

func TestNativeProverReportPreservesHybridVerdicts(t *testing.T) {
	report, expected := nativeReportFixture()
	if err := nativeValidateReport(report, expected); err != nil {
		t.Fatal(err)
	}
	// A rejected alternative is not the selected body and does not change search
	// policy. Final vector demotion retains the genuine selected verdict.
	alternative := report.Functions[0].Validations[0]
	alternative.Name = "alternative"
	alternative.Outcome = "mismatch"
	report.Functions[0].Validations = append(report.Functions[0].Validations, alternative)
	report.Functions[0].Considered, report.Functions[0].Materialized = 2, 2
	demoted := report.Functions[3]
	demoted.Selected = report.Functions[0].Selected
	demoted.Validations = report.Functions[0].Validations
	demoted.Considered, demoted.Materialized = 2, 2
	report.Functions[3] = demoted
	if err := nativeValidateReport(report, expected); err != nil {
		t.Fatal(err)
	}
}

func TestNativeProverReportRejectsIncompleteOrForgedCompletion(t *testing.T) {
	cases := map[string]func(*compiler.NativeBuildReport){
		"missing":          func(r *compiler.NativeBuildReport) { r.Functions = r.Functions[:3] },
		"duplicate":        func(r *compiler.NativeBuildReport) { r.Functions[1] = r.Functions[0] },
		"reordered":        func(r *compiler.NativeBuildReport) { r.Functions[0], r.Functions[1] = r.Functions[1], r.Functions[0] },
		"source":           func(r *compiler.NativeBuildReport) { r.Functions[0].Input.SourceSHA256 = strings.Repeat("9", 64) },
		"unfinished":       func(r *compiler.NativeBuildReport) { r.Functions[0].Status = "unfinished" },
		"error":            func(r *compiler.NativeBuildReport) { r.Functions[0].Status = "error" },
		"unselected-trust": func(r *compiler.NativeBuildReport) { r.Functions[2].Selected = nil },
		"unvalidated":      func(r *compiler.NativeBuildReport) { r.Functions[0].Validations = nil },
		"duplicate-validation": func(r *compiler.NativeBuildReport) {
			r.Functions[0].Validations = append(r.Functions[0].Validations, r.Functions[0].Validations[0])
		},
		"cached":           func(r *compiler.NativeBuildReport) { r.Functions[0].Validations[0].Cached = true },
		"wrong-verdict":    func(r *compiler.NativeBuildReport) { r.Functions[0].Selected.Outcome = "trusted" },
		"bad-recipe":       func(r *compiler.NativeBuildReport) { r.Functions[0].Validations[0].RecipeSHA256 = "mtime" },
		"no-reason":        func(r *compiler.NativeBuildReport) { r.Functions[3].Reason = "" },
		"unknown-callee":   func(r *compiler.NativeBuildReport) { r.Functions[0].Callees = []string{"missing"} },
		"duplicate-callee": func(r *compiler.NativeBuildReport) { r.Functions[0].Callees = []string{"external", "external"} },
		"C-only": func(r *compiler.NativeBuildReport) {
			for i := range r.Functions {
				r.Functions[i].Status = "c-fallback"
				r.Functions[i].Selected = nil
				r.Functions[i].Validations = nil
			}
		},
	}
	for name, mutate := range cases {
		t.Run(name, func(t *testing.T) {
			report, expected := nativeReportFixture()
			mutate(&report)
			if err := nativeValidateReport(report, expected); err == nil {
				t.Fatal("invalid native report accepted")
			}
		})
	}
}

func TestNativeProverReceiptJSONFailsClosed(t *testing.T) {
	valid := `{"schema_version":1,"recipe_sha256":"r","report_sha256":"v","program_sha256":"c","object_sha256":"o","solver_sha256":"s","link_command":[],"runtime_files":{}}`
	var receipt nativeProverSuccess
	if err := nativeDecode([]byte(valid), &receipt); err != nil {
		t.Fatal(err)
	}
	invalid := []string{
		valid[:len(valid)-1], valid + ` {}`, strings.Replace(valid, `"schema_version":1`, `"schema_version":1,"schema_version":1`, 1),
		strings.Replace(valid, `"runtime_files":{}`, `"runtime_files":{"x":"1","x":"2"}`, 1),
		strings.Replace(valid, `"schema_version":1,`, "", 1), strings.Replace(valid, `"schema_version":1`, `"schema_version":1,"unknown":true`, 1),
		strings.Replace(valid, `"schema_version":1`, `"Schema_version":1`, 1), strings.Replace(valid, `"schema_version":1`, `"schema_version":NaN`, 1),
	}
	for i, text := range invalid {
		if err := nativeDecode([]byte(text), &receipt); err == nil {
			t.Fatalf("invalid receipt %d accepted", i)
		}
	}
}

func TestNativeProverArtifactNeverRebuildsInvalidPrerequisite(t *testing.T) {
	t.Setenv("OAK_NATIVE_PREREQUISITE", filepath.Join(t.TempDir(), "absent"))
	t.Setenv("OAK_SOLVER_NATIVE", "1")
	if binary, err := oakSolverBinary(); err == nil || binary != "" {
		t.Fatalf("missing mandatory prerequisite became %q, %v", binary, err)
	}
	directory := t.TempDir()
	t.Setenv("OAK_NATIVE_PREREQUISITE", directory)
	if err := os.WriteFile(filepath.Join(directory, "solver"), []byte("leftover binary"), 0700); err != nil {
		t.Fatal(err)
	}
	if binary, err := oakSolverBinary(); err == nil || binary != "" {
		t.Fatalf("unfinished artifact became %q, %v", binary, err)
	}
}

func TestNativeProverEvidenceRejectsSymlinksAndMutation(t *testing.T) {
	directory := t.TempDir()
	file := filepath.Join(directory, "receipt.json")
	if err := os.WriteFile(file, []byte("first"), 0600); err != nil {
		t.Fatal(err)
	}
	before, err := nativeFileDigest(file)
	if err != nil {
		t.Fatal(err)
	}
	info, err := os.Stat(file)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(file, []byte("other"), 0600); err != nil {
		t.Fatal(err)
	}
	if err := os.Chtimes(file, info.ModTime(), info.ModTime()); err != nil {
		t.Fatal(err)
	}
	after, err := nativeFileDigest(file)
	if err != nil || before == after {
		t.Fatal("same-size/mtime byte mutation was not detected")
	}
	link := filepath.Join(directory, "linked.json")
	if err := os.Symlink(file, link); err != nil {
		t.Fatal(err)
	}
	if _, err := nativeRegular(link); err == nil {
		t.Fatal("symlink file accepted")
	}
	ancestor := filepath.Join(t.TempDir(), "alias")
	if err := os.Symlink(directory, ancestor); err != nil {
		t.Fatal(err)
	}
	if _, err := nativeRegular(filepath.Join(ancestor, "receipt.json")); err == nil {
		t.Fatal("symlink ancestor accepted")
	}
}

// This independent declaration reconciliation prevents the producer and fresh
// frontend inventory helper from agreeing on the same accidentally omitted
// function. It parses the exact16 prover units and core prelude without using
// the native eligibility/report helper. Generic prelude declarations have no
// solver instantiations. Sixteen core prelude and four imported host bodies
// join the solver declarations; the host's extern is a fifteenth dependency.
func TestNativeProverReviewedInventoryReconcilesDeclarations(t *testing.T) {
	var expected compiler.NativeBuildInventory
	if err := nativeDecode(nativeProverInventoryJSON, &expected); err != nil {
		t.Fatal(err)
	}
	names, externs := map[string]bool{}, map[string]string{}
	parse := func(path, text, pkg string) {
		tree, err := compiler.New().WithSource(path, text).Parse().Get()
		if err != nil {
			t.Fatal(err)
		}
		for _, statement := range tree.Root.Statements {
			fn, ok := statement.(*ast.FunctionStatement)
			if !ok || fn.Name == nil || len(fn.TypeParams) != 0 {
				continue
			}
			name := fn.Name.Value
			if pkg != "" {
				name = modules.Mangle(pkg, name)
			}
			if fn.ExternSymbol != "" {
				externs[name] = fn.ExternSymbol
				continue
			}
			if fn.Body != nil {
				if names[name] {
					t.Fatalf("duplicate raw declaration %s", name)
				}
				names[name] = true
			}
		}
	}
	for name, text := range oakSolverSources() {
		if strings.HasSuffix(name, ".oak") {
			parse(name, text, "")
		}
	}
	before := len(names)
	if len(externs) != 14 {
		t.Fatalf("expected original14 solver externs, got %d", len(externs))
	}
	parse("stdlib.oak", stdlib.Prelude, "")
	if len(names)-before != 16 {
		t.Fatalf("expected16 core prelude bodies, got %d", len(names)-before)
	}
	parse("host.oak", stdlib.Packages["host"], "host")
	if before != 1067 || len(names)-before != 20 || len(externs) != nativeProverExterns {
		t.Fatalf("source/prelude/extern reconciliation changed: %d + %d and %d externs", before, len(names)-before, len(externs))
	}
	recorded := map[string]bool{}
	for _, input := range expected.Eligible {
		recorded[input.Name] = true
	}
	if len(expected.Eligible) != nativeProverEligible || !reflect.DeepEqual(recorded, names) {
		t.Fatal("reviewed inventory differs from independent source/prelude declaration set")
	}
	recordedExterns := map[string]string{}
	for _, input := range expected.Externs {
		recordedExterns[input.Name] = input.ExternSymbol
	}
	if !reflect.DeepEqual(recordedExterns, externs) {
		t.Fatal("reviewed extern dependencies differ from parsed declarations")
	}
	encoded, err := json.Marshal(expected)
	if err != nil || len(encoded) == 0 {
		t.Fatal(err)
	}
}

func TestNativeProverFrontendMemoBindsImmutableRecipe(t *testing.T) {
	recipe := nativeProverRecipe{SchemaVersion: 1, RecipeVersion: nativeProverRecipeVersion, HarnessSHA256: "compiler-1", Sources: map[string]string{"main.oak": "source-1"}, SupportSources: map[string]string{"stdlib/host.oak": "host-1"}, Platform: "linux/arm64", CC: nativeProverCC{SHA256: "cc-1"}, ToolchainFiles: map[string]string{"/lib/libc.so.6": "libc-1"}}
	_, inventory := nativeReportFixture()
	memo := nativeInventoryMemo{}
	calls := 0
	derive := func() (compiler.NativeBuildInventory, error) { calls++; return inventory, nil }
	key, err := nativeInventoryRecipeKey(recipe)
	if err != nil {
		t.Fatal(err)
	}
	first, err := memo.get(key, derive)
	if err != nil {
		t.Fatal(err)
	}
	first.Eligible[0].Name = "caller mutation"
	again, err := memo.get(key, derive)
	if err != nil || again.Eligible[0].Name == "caller mutation" || calls != 1 {
		t.Fatal("memo reused mutable data or reran unchanged frontend")
	}
	changes := []func(){func() { recipe.HarnessSHA256 = "compiler-2" }, func() { recipe.Sources["main.oak"] = "source-2" }, func() { recipe.SupportSources["stdlib/host.oak"] = "host-2" }, func() { recipe.RecipeVersion += "changed" }, func() { recipe.CC.SHA256 = "cc-2" }, func() { recipe.ToolchainFiles["/lib/libc.so.6"] = "libc-2" }, func() { recipe.Context.RunAttempt = "2" }, func() { recipe.Platform = "other" }}
	for i, change := range changes {
		change()
		key, err = nativeInventoryRecipeKey(recipe)
		if err != nil {
			t.Fatal(err)
		}
		if _, err := memo.get(key, derive); err != nil {
			t.Fatal(err)
		}
		if calls != i+2 {
			t.Fatalf("recipe mutation %d did not invalidate preparation", i)
		}
	}
	failures := 0
	reject := func() (compiler.NativeBuildInventory, error) {
		failures++
		return compiler.NativeBuildInventory{}, os.ErrInvalid
	}
	for i := 0; i < 2; i++ {
		if _, err := memo.get("failed", reject); err == nil {
			t.Fatal("failed frontend became a success")
		}
	}
	if failures != 2 {
		t.Fatal("failed frontend was cached")
	}
}

func TestNativeProverReviewedLinkInputs(t *testing.T) {
	directory := filepath.Join(t.TempDir(), "source")
	if err := nativeWriteSources(directory); err != nil {
		t.Fatal(err)
	}
	inputs, err := compiler.New().WithPackageDir(directory).LinkInputs()
	if err != nil {
		t.Fatal(err)
	}
	if len(inputs) != 0 {
		t.Fatalf("host shim should be inside emitted program.c; external link inputs need review: %+v", inputs)
	}
}

func TestNativeProverRejectsUnreviewedVerificationAndRaceControls(t *testing.T) {
	for _, entry := range os.Environ() {
		name, _, _ := strings.Cut(entry, "=")
		if strings.HasPrefix(name, "OAK") || name == "GORACE" || name == "GOFLAGS" {
			t.Setenv(name, "")
		}
	}
	for name, value := range map[string]string{"GORACE": "exitcode=0", "OAK_VERIFY_ONLY": "one_function", "OAK_VERIFY_OFF": "loop", "OAK_NATIVE_ONLY": "one_function", "OAK_OPT_SKIP": "all", "OAK_OPT_BEAM": "1", "OAKOPT": "0"} {
		t.Run(name, func(t *testing.T) {
			t.Setenv(name, value)
			if err := nativeCheckEnvironmentControls(); err == nil || !strings.Contains(err.Error(), name) {
				t.Fatalf("unreviewed %s was not identified: %v", name, err)
			}
		})
	}
}
