package main

import (
	"bytes"
	"errors"
	"io"
	"os"
	"path/filepath"
	"runtime/debug"
	"strings"
	"sync"
	"testing"

	"github.com/SCKelemen/oak/compiler"
)

func scalarLockedForTest(t *testing.T) scalarProfileInputs {
	t.Helper()
	var locked scalarProfileInputs
	if err := nativeDecode(scalarProfileInputsJSON, &locked); err != nil {
		t.Fatal(err)
	}
	return locked
}

type scalarFailWriter struct {
	n   int
	err error
}

func (w scalarFailWriter) Write(p []byte) (int, error) { return w.n, w.err }

func TestScalarProfileWriterLimits(t *testing.T) {
	t.Run("exact_capacity", func(t *testing.T) {
		var b bytes.Buffer
		w := &scalarProfileWriter{w: &b, remaining: 4, notify: make(chan struct{}, 1)}
		if n, err := w.Write([]byte("abcd")); n != 4 || err != nil || b.String() != "abcd" || w.failure() != nil {
			t.Fatalf("write: %d %v %q", n, err, b.String())
		}
	})
	t.Run("overflow_preserves_prefix", func(t *testing.T) {
		var b bytes.Buffer
		w := &scalarProfileWriter{w: &b, remaining: 4, notify: make(chan struct{}, 1)}
		_, _ = w.Write([]byte("abc"))
		if n, err := w.Write([]byte("de")); n != 0 || err == nil || b.String() != "abc" {
			t.Fatal("overflow admitted")
		}
		if len(w.notify) != 1 {
			t.Fatal("coordinator not notified")
		}
	})
	t.Run("short_write", func(t *testing.T) {
		w := &scalarProfileWriter{w: scalarFailWriter{1, nil}, remaining: 4, notify: make(chan struct{}, 1)}
		if n, err := w.Write([]byte("ab")); n != 1 || !errors.Is(err, io.ErrShortWrite) || w.remaining != 3 {
			t.Fatal("short write not preserved")
		}
	})
	t.Run("write_error", func(t *testing.T) {
		want := errors.New("storage failure")
		w := &scalarProfileWriter{w: scalarFailWriter{0, want}, remaining: 4, notify: make(chan struct{}, 1)}
		if _, err := w.Write([]byte("ab")); !errors.Is(err, want) {
			t.Fatal("write error dropped")
		}
	})
	t.Run("sticky_failure", func(t *testing.T) {
		var b bytes.Buffer
		w := &scalarProfileWriter{w: &b, remaining: 1, notify: make(chan struct{}, 1)}
		_, first := w.Write([]byte("ab"))
		_, next := w.Write([]byte("a"))
		if first == nil || next != first || b.Len() != 0 || len(w.notify) != 1 {
			t.Fatal("failure was not sticky")
		}
	})
	t.Run("concurrent_capacity", func(t *testing.T) {
		var b bytes.Buffer
		w := &scalarProfileWriter{w: &b, remaining: 8, notify: make(chan struct{}, 1)}
		var wg sync.WaitGroup
		for i := 0; i < 16; i++ {
			wg.Add(1)
			go func() { defer wg.Done(); _, _ = w.Write([]byte("x")) }()
		}
		wg.Wait()
		if b.Len() != 8 || w.remaining != 0 || w.failure() == nil || len(w.notify) != 1 {
			t.Fatal("concurrent capacity escaped")
		}
	})
}

func TestScalarProfileInputIdentity(t *testing.T) {
	for _, name := range []string{"exact", "changed", "extra", "missing"} {
		t.Run(name, func(t *testing.T) {
			directory := filepath.Join(t.TempDir(), "source")
			if err := nativeWriteSources(directory); err != nil {
				t.Fatal(err)
			}
			switch name {
			case "changed":
				if err := os.WriteFile(filepath.Join(directory, "main.oak"), []byte("changed"), 0600); err != nil {
					t.Fatal(err)
				}
			case "extra":
				if err := os.WriteFile(filepath.Join(directory, "extra.oak"), nil, 0600); err != nil {
					t.Fatal(err)
				}
			case "missing":
				if err := os.Remove(filepath.Join(directory, "main.oak")); err != nil {
					t.Fatal(err)
				}
			}
			err := scalarProfileCheckSources(directory, scalarLockedForTest(t))
			if (err == nil) != (name == "exact") {
				t.Fatalf("unexpected identity result: %v", err)
			}
		})
	}
}

func TestScalarProfileBuildIdentity(t *testing.T) {
	for _, name := range []string{"exact", "version", "main", "dependency", "race", "arch", "duplicate"} {
		t.Run(name, func(t *testing.T) {
			locked := scalarLockedForTest(t)
			b := &debug.BuildInfo{GoVersion: locked.GoBuild.Version, Main: locked.GoBuild.Main, Deps: locked.GoBuild.Dependencies}
			for k, v := range locked.GoBuild.Settings {
				b.Settings = append(b.Settings, debug.BuildSetting{Key: k, Value: v})
			}
			switch name {
			case "version":
				b.GoVersion = "go1.0"
			case "main":
				b.Main.Path = "wrong"
			case "dependency":
				b.Deps = nil
			case "race":
				for i := range b.Settings {
					if b.Settings[i].Key == "-race" {
						b.Settings[i].Value = "false"
					}
				}
			case "arch":
				for i := range b.Settings {
					if b.Settings[i].Key == "GOARCH" {
						b.Settings[i].Value = "amd64"
					}
				}
			case "duplicate":
				b.Settings = append(b.Settings, b.Settings[0])
			}
			err := scalarProfileCheckBuild(b, locked.GoBuild)
			if (err == nil) != (name == "exact") {
				t.Fatalf("unexpected build result: %v", err)
			}
		})
	}
}

func scalarReportForTest(t *testing.T, locked scalarProfileInputs) (compiler.NativeBuildReport, int) {
	t.Helper()
	var inventory compiler.NativeBuildInventory
	if err := nativeDecode(nativeProverInventoryJSON, &inventory); err != nil {
		t.Fatal(err)
	}
	r := compiler.NativeBuildReport{SchemaVersion: 2, Inventory: inventory}
	at := -1
	for i, input := range inventory.Eligible {
		row := compiler.NativeBuildFunction{Input: input, Status: "c-fallback", Reason: "selector excludes this function", Validations: []compiler.NativeBuildCandidate{}}
		if input.Name == "scalar_text" {
			at = i
			row.Status = "trusted"
			row.Reason = "fixture"
			row.Considered = 3
			row.Materialized = 3
			for _, name := range locked.CandidateNames {
				row.Validations = append(row.Validations, compiler.NativeBuildCandidate{Name: name, BodySHA256: strings.Repeat("a", 64), RecipeSHA256: strings.Repeat("b", 64), Outcome: "trusted"})
			}
			chosen := row.Validations[0]
			row.Selected = &chosen
		}
		r.Functions = append(r.Functions, row)
	}
	for _, input := range inventory.Supplied {
		r.Supplied = append(r.Supplied, compiler.NativeBuildSupplied{Input: input.Input, Arch: input.Arch, BodySHA256: input.BodySHA256, Status: "trusted", Reason: "fixture"})
	}
	if at < 0 {
		t.Fatal("locked frontend lacks scalar_text")
	}
	return r, at
}

func TestScalarProfileReportContract(t *testing.T) {
	for _, name := range []string{"exact", "missing_function", "duplicate_function", "other_selected", "missing_candidate", "extra_candidate", "candidate_order", "cached", "bad_digest", "bad_outcome", "missing_selection", "selection_not_validated", "wrong_inventory", "missing_supplied", "unfinished_supplied"} {
		t.Run(name, func(t *testing.T) {
			locked := scalarLockedForTest(t)
			r, at := scalarReportForTest(t, locked)
			switch name {
			case "missing_function":
				r.Functions = append(r.Functions[:at], r.Functions[at+1:]...)
			case "duplicate_function":
				r.Functions[0] = r.Functions[at]
			case "other_selected":
				r.Functions[0].Selected = r.Functions[at].Selected
			case "missing_candidate":
				r.Functions[at].Validations = r.Functions[at].Validations[:2]
			case "extra_candidate":
				r.Functions[at].Validations = append(r.Functions[at].Validations, r.Functions[at].Validations[0])
			case "candidate_order":
				r.Functions[at].Validations[0], r.Functions[at].Validations[1] = r.Functions[at].Validations[1], r.Functions[at].Validations[0]
			case "cached":
				r.Functions[at].Validations[0].Cached = true
			case "bad_digest":
				r.Functions[at].Validations[0].BodySHA256 = "bad"
			case "bad_outcome":
				r.Functions[at].Validations[0].Outcome = "unknown"
			case "missing_selection":
				r.Functions[at].Selected = nil
			case "selection_not_validated":
				r.Functions[at].Selected.Name = "invented"
			case "wrong_inventory":
				r.Inventory.Eligible = nil
			case "missing_supplied":
				r.Supplied = r.Supplied[:1]
			case "unfinished_supplied":
				r.Supplied[0].Status = "unfinished"
			}
			err := scalarProfileCheckReport(r, locked)
			if (err == nil) != (name == "exact") {
				t.Fatalf("unexpected report result: %v", err)
			}
		})
	}
}

func scalarCleanEnvironment(t *testing.T) {
	t.Helper()
	for _, entry := range os.Environ() {
		name, _, _ := strings.Cut(entry, "=")
		if strings.HasPrefix(name, "OAK_") || name == "OAKOPT" || name == "OAKCPU" || name == "OAKCACHE" || name == "OAKMODCACHE" {
			t.Setenv(name, "")
		}
	}
	for _, name := range []string{"CPATH", "C_INCLUDE_PATH", "CPLUS_INCLUDE_PATH", "LIBRARY_PATH", "COMPILER_PATH", "GCC_EXEC_PREFIX", "LD_PRELOAD", "LD_LIBRARY_PATH", "LD_RUN_PATH", "LDEMULATION", "GOFLAGS", "GOEXPERIMENT", "GORACE", "CGO_CFLAGS", "CGO_CPPFLAGS", "CGO_CXXFLAGS", "CGO_LDFLAGS"} {
		t.Setenv(name, "")
	}
}

func TestScalarProfileSelectorIsolation(t *testing.T) {
	t.Run("mode_missing_argument", func(t *testing.T) {
		if scalarTextProfileMain(nil) != 2 {
			t.Fatal("missing output argument accepted")
		}
	})
	t.Run("mode_extra_argument", func(t *testing.T) {
		if scalarTextProfileMain([]string{"output", "other_selector"}) != 2 {
			t.Fatal("extra selector argument accepted")
		}
	})
	for _, name := range []string{"fixed_selector", "restore_absent", "callback_failure", "reject_selector", "production_refuses_selector"} {
		t.Run(name, func(t *testing.T) {
			scalarCleanEnvironment(t)
			t.Setenv("OAK_NATIVE_ONLY", "")
			if name == "restore_absent" {
				if err := os.Unsetenv("OAK_NATIVE_ONLY"); err != nil {
					t.Fatal(err)
				}
			}
			if name == "reject_selector" || name == "production_refuses_selector" {
				t.Setenv("OAK_NATIVE_ONLY", "scalar_text")
			}
			if name == "production_refuses_selector" {
				if nativeCheckEnvironmentControls() == nil {
					t.Fatal("production accepted selector")
				}
				return
			}
			called := false
			want := errors.New("callback failure")
			err := scalarProfileSelector(func() error {
				called = true
				if os.Getenv("OAK_NATIVE_ONLY") != "scalar_text" {
					t.Error("selector not literal")
				}
				if name == "callback_failure" {
					return want
				}
				return nil
			})
			if name == "reject_selector" {
				if err == nil || called {
					t.Fatal("inherited selector accepted")
				}
				return
			}
			if name == "restore_absent" {
				if _, exists := os.LookupEnv("OAK_NATIVE_ONLY"); exists {
					t.Fatal("absent selector was not restored")
				}
			}
			if !called || os.Getenv("OAK_NATIVE_ONLY") != "" {
				t.Fatal("selector not restored")
			}
			if name == "callback_failure" {
				if !errors.Is(err, want) {
					t.Fatal("callback failure lost")
				}
			} else if err != nil {
				t.Fatal(err)
			}
		})
	}
}

func TestScalarProfileJSONLimits(t *testing.T) {
	for _, name := range []string{"exact", "overflow", "preexisting", "marshal_failure"} {
		t.Run(name, func(t *testing.T) {
			path := filepath.Join(t.TempDir(), "record.json")
			remaining := int64(3)
			var value any = 0
			if name == "exact" {
				remaining = 2
			}
			if name == "overflow" {
				remaining = 1
			}
			if name == "preexisting" {
				if err := os.WriteFile(path, []byte("old"), 0600); err != nil {
					t.Fatal(err)
				}
			}
			if name == "marshal_failure" {
				value = make(chan int)
			}
			err := scalarProfileWriteJSON(path, value, &remaining)
			if (err == nil) != (name == "exact") {
				t.Fatalf("unexpected JSON result: %v", err)
			}
			if name == "preexisting" {
				b, _ := os.ReadFile(path)
				if string(b) != "old" {
					t.Fatal("existing file overwritten")
				}
			}
		})
	}
}

func TestScalarProfileBoundedRead(t *testing.T) {
	for _, name := range []string{"exact", "overflow", "directory", "missing"} {
		t.Run(name, func(t *testing.T) {
			dir := t.TempDir()
			path := filepath.Join(dir, "input")
			limit := int64(4)
			if name == "directory" {
				path = dir
			} else if name != "missing" {
				if err := os.WriteFile(path, []byte("data"), 0600); err != nil {
					t.Fatal(err)
				}
			}
			if name == "overflow" {
				limit = 3
			}
			b, err := scalarProfileRead(path, limit)
			if (err == nil) != (name == "exact") {
				t.Fatalf("unexpected read result: %v", err)
			}
			if name == "exact" && string(b) != "data" {
				t.Fatal("bytes changed")
			}
		})
	}
}
