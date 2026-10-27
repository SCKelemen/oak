package buildcache

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"testing"
)

func TestLookupIntegrity(t *testing.T) {
	for _, fault := range []string{"modified", "truncated", "missing", "symlink", "not-executable", "missing-manifest", "malformed-manifest", "wrong-key", "invalid-digest", "legacy"} {
		t.Run(fault, func(t *testing.T) {
			t.Setenv("OAKCACHE", t.TempDir())
			key := Key("inputs")
			source := filepath.Join(t.TempDir(), "source")
			check := func(err error) {
				t.Helper()
				if err != nil {
					t.Fatal(err)
				}
			}
			check(os.WriteFile(source, []byte("original executable"), 0700))
			check(Store(key, source))
			cached, ok := Lookup(key)
			if !ok {
				t.Fatal("new entry missed")
			}
			path, err := entryPath(key)
			check(err)
			switch fault {
			case "modified":
				check(os.WriteFile(cached, []byte("replaced executable"), 0755))
			case "truncated":
				check(os.Truncate(cached, 0))
			case "missing":
				check(os.Remove(cached))
			case "symlink":
				check(os.Remove(cached))
				check(os.Symlink(source, cached))
			case "not-executable":
				check(os.Chmod(cached, 0600))
			case "missing-manifest":
				check(os.Remove(path + ".json"))
			case "malformed-manifest":
				check(os.WriteFile(path+".json", []byte("{"), 0600))
			case "wrong-key", "invalid-digest":
				data, err := os.ReadFile(path + ".json")
				check(err)
				var m manifest
				check(json.Unmarshal(data, &m))
				if fault == "wrong-key" {
					m.Key = Key("other")
				} else {
					m.Digest = "../../outside"
				}
				data, err = json.Marshal(m)
				check(err)
				check(os.WriteFile(path+".json", data, 0600))
			case "legacy":
				check(os.Remove(path + ".json"))
				check(os.WriteFile(path, []byte("old unchecked binary"), 0755))
			}
			if got, ok := Lookup(key); ok || got != "" {
				t.Fatalf("corrupt entry accepted: %q", got)
			}
			check(Store(key, source))
			restored, ok := Lookup(key)
			if !ok {
				t.Fatal("replacement missed")
			}
			data, err := os.ReadFile(restored)
			check(err)
			if string(data) != "original executable" {
				t.Fatalf("wrong replacement %q", data)
			}
		})
	}
}

func TestCompilerContentIdentity(t *testing.T) {
	path := filepath.Join(t.TempDir(), "cc")
	if err := os.WriteFile(path, []byte("first"), 0700); err != nil {
		t.Fatal(err)
	}
	before, err := os.Stat(path)
	if err != nil {
		t.Fatal(err)
	}
	first, err := CompilerIdentity(path)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, []byte("other"), 0700); err != nil {
		t.Fatal(err)
	}
	if err := os.Chtimes(path, before.ModTime(), before.ModTime()); err != nil {
		t.Fatal(err)
	}
	second, err := CompilerIdentity(path)
	if err != nil {
		t.Fatal(err)
	}
	if first == second {
		t.Fatal("equal-size/equal-mtime compiler replacement reused identity")
	}
	alias := path + "-alias"
	if err := os.Symlink(path, alias); err != nil {
		t.Fatal(err)
	}
	linked, err := CompilerIdentity(alias)
	if err != nil {
		t.Fatal(err)
	}
	if linked != second {
		t.Fatal("resolved alias should identify same compiler")
	}
}

func TestConcurrentPublication(t *testing.T) {
	t.Setenv("OAKCACHE", t.TempDir())
	key := Key("concurrent")
	sources := make([]string, 4)
	valid := make(map[string]bool)
	for i := range sources {
		sources[i] = filepath.Join(t.TempDir(), "source")
		content := strings.Repeat(string(rune('a'+i)), 1<<16)
		valid[content] = true
		if err := os.WriteFile(sources[i], []byte(content), 0700); err != nil {
			t.Fatal(err)
		}
	}
	var wg sync.WaitGroup
	for _, source := range sources {
		wg.Go(func() {
			for range 12 {
				if err := Store(key, source); err != nil {
					t.Error(err)
					return
				}
				if path, ok := Lookup(key); ok {
					data, err := os.ReadFile(path)
					if err != nil || !valid[string(data)] {
						t.Errorf("partial publication: %v, %d bytes", err, len(data))
						return
					}
				}
			}
		})
	}
	wg.Wait()
	if _, ok := Lookup(key); !ok {
		t.Fatal("completed concurrent store missed")
	}
}

func TestInvalidKeysAndFailedStore(t *testing.T) {
	t.Setenv("OAKCACHE", t.TempDir())
	for _, key := range []string{"", "abcd", strings.Repeat("g", 64), strings.Repeat("A", 64), "../../outside"} {
		if _, ok := Lookup(key); ok {
			t.Fatalf("accepted invalid key %q", key)
		}
		if err := Store(key, "missing"); err == nil {
			t.Fatalf("stored invalid key %q", key)
		}
	}
	key := Key("failed")
	path, err := entryPath(key)
	if err != nil {
		t.Fatal(err)
	}
	if err := Store(key, filepath.Join(t.TempDir(), "missing")); err == nil {
		t.Fatal("missing source succeeded")
	}
	entries, err := os.ReadDir(filepath.Dir(path))
	if err != nil {
		t.Fatal(err)
	}
	if len(entries) != 0 {
		t.Fatalf("failed copy leaked staging: %v", entries)
	}
}
