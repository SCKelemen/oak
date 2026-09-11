package buildcache

import (
	"os"
	"path/filepath"
	"testing"
)

func TestKeyStoreLookupClean(t *testing.T) {
	t.Setenv("OAKCACHE", t.TempDir())
	a, b := Key("int main(){}", "", "cc|1|2", "-O1"), Key("int main(){return 1;}", "", "cc|1|2", "-O1")
	if a == b || len(a) != 64 {
		t.Fatalf("keys must differ and be hex digests: %s %s", a, b)
	}
	if Key("a", "b") == Key("ab", "") {
		t.Fatal("key must be injective over part boundaries")
	}
	if _, ok := Lookup(a); ok {
		t.Fatal("empty cache must miss")
	}
	binary := filepath.Join(t.TempDir(), "prog")
	if err := os.WriteFile(binary, []byte("#!/bin/sh\nexit 0\n"), 0o700); err != nil {
		t.Fatal(err)
	}
	if err := Store(a, binary); err != nil {
		t.Fatal(err)
	}
	cached, ok := Lookup(a)
	if !ok {
		t.Fatal("stored entry must hit")
	}
	if info, err := os.Stat(cached); err != nil || info.Mode()&0o111 == 0 {
		t.Fatalf("cached entry must be executable: %v", err)
	}
	out := filepath.Join(t.TempDir(), "copy")
	if err := Copy(cached, out); err != nil {
		t.Fatal(err)
	}
	if data, _ := os.ReadFile(out); string(data) != "#!/bin/sh\nexit 0\n" {
		t.Fatalf("copy = %q", data)
	}
	if _, err := Clean(); err != nil {
		t.Fatal(err)
	}
	if _, ok := Lookup(a); ok {
		t.Fatal("clean must empty the cache")
	}
	t.Setenv("OAKCACHE", "off")
	if _, err := Dir(); err != ErrDisabled {
		t.Fatalf("OAKCACHE=off must disable: %v", err)
	}
	if _, ok := Lookup(a); ok {
		t.Fatal("disabled cache must miss")
	}
}
