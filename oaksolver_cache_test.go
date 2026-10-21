package main

import (
	"errors"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"testing"
)

func TestOakSolverCacheIntegrity(t *testing.T) {
	for _, fault := range []string{"unchanged", "modified", "truncated", "missing", "symlink", "not-executable", "missing-manifest", "malformed-manifest", "wrong-key", "path-digest"} {
		t.Run(fault, func(t *testing.T) {
			dir := filepath.Join(t.TempDir(), "cache")
			builds := 0
			build := func(work, binary string) error {
				builds++
				if work == dir {
					t.Fatal("build shares published cache directory")
				}
				return os.WriteFile(binary, []byte("original executable"), 0o700)
			}
			binary, err := oakSolverCachedBinary(dir, "key", build)
			if err != nil {
				t.Fatal(err)
			}
			check := func(err error) {
				t.Helper()
				if err != nil {
					t.Fatal(err)
				}
			}
			manifest := filepath.Join(dir, "manifest.json")
			switch fault {
			case "modified":
				check(os.WriteFile(binary, []byte("replaced executable"), 0o700))
			case "truncated":
				check(os.Truncate(binary, 0))
			case "missing":
				check(os.Remove(binary))
			case "symlink":
				target := filepath.Join(t.TempDir(), "target")
				check(os.WriteFile(target, []byte("original executable"), 0o700))
				check(os.Remove(binary))
				check(os.Symlink(target, binary))
			case "not-executable":
				check(os.Chmod(binary, 0o600))
			case "missing-manifest":
				check(os.Remove(manifest))
			case "malformed-manifest":
				check(os.WriteFile(manifest, []byte("{"), 0o600))
			case "wrong-key":
				data, err := os.ReadFile(manifest)
				check(err)
				check(os.WriteFile(manifest, []byte(strings.Replace(string(data), `"key":"key"`, `"key":"other"`, 1)), 0o600))
			case "path-digest":
				check(os.WriteFile(manifest, []byte(`{"key":"key","sha256":"../../outside"}`), 0o600))
			}
			rebuilt, err := oakSolverCachedBinary(dir, "key", build)
			check(err)
			want := 2
			if fault == "unchanged" {
				want = 1
			}
			if builds != want {
				t.Fatalf("build count %d, want %d", builds, want)
			}
			data, err := os.ReadFile(rebuilt)
			check(err)
			if string(data) != "original executable" {
				t.Fatalf("returned corrupt executable: %q", data)
			}
		})
	}
}

func TestOakSolverCacheFailedBuild(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "cache")
	failed := errors.New("compiler failed")
	path, err := oakSolverCachedBinary(dir, "key", func(work, binary string) error {
		if err := os.WriteFile(binary, []byte("partial"), 0o700); err != nil {
			return err
		}
		return failed
	})
	if !errors.Is(err, failed) || path != "" {
		t.Fatalf("got %q, %v", path, err)
	}
	entries, err := os.ReadDir(dir)
	if err != nil {
		t.Fatal(err)
	}
	if len(entries) != 0 {
		t.Fatalf("failed build left published or staging files: %v", entries)
	}
}

func TestOakSolverCacheConcurrent(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "cache")
	builds := 0
	var wg sync.WaitGroup
	for range 8 {
		wg.Go(func() {
			_, err := oakSolverCachedBinary(dir, "key", func(_, binary string) error {
				builds++
				return os.WriteFile(binary, []byte("executable"), 0o700)
			})
			if err != nil {
				t.Error(err)
			}
		})
	}
	wg.Wait()
	if builds != 1 {
		t.Fatalf("built %d times", builds)
	}
}

func TestOakSolverCompilerContentIdentity(t *testing.T) {
	path := filepath.Join(t.TempDir(), "compiler")
	if err := os.WriteFile(path, []byte("first"), 0o700); err != nil {
		t.Fatal(err)
	}
	info, err := os.Stat(path)
	if err != nil {
		t.Fatal(err)
	}
	first, err := oakSolverFileDigest(path)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, []byte("other"), 0o700); err != nil {
		t.Fatal(err)
	}
	if err := os.Chtimes(path, info.ModTime(), info.ModTime()); err != nil {
		t.Fatal(err)
	}
	second, err := oakSolverFileDigest(path)
	if err != nil {
		t.Fatal(err)
	}
	if first == second {
		t.Fatal("same-sized compiler replacement preserving mtime reused identity")
	}
}
