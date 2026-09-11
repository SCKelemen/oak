package testrunner

import (
	"encoding/binary"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
)

// `oak test` links the manifest's native inputs (`link`, `framework`;
// docs/spec/83-modules.md section 4.6) into the test binary, so a module's
// tests can call the native code the module declares, in unit and Table
// targets alike.
func TestLinkedNativeLibraryInTests(t *testing.T) {
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("requires cc")
	}
	ar, err := exec.LookPath("ar")
	if err != nil {
		t.Skip("requires ar")
	}
	row := func(x, want uint32) string {
		var b [8]byte
		binary.LittleEndian.PutUint32(b[0:], x)
		binary.LittleEndian.PutUint32(b[4:], want)
		return string(b[:])
	}
	dir := fixture(t, map[string]string{
		"oak.mod":         "module example.com/app\nlink native/libtwice.a\n",
		"native/twice.c":  "unsigned int oak_test_twice(unsigned int x) { return 2u * x; }\n",
		"hello/hello.oak": "package hello\n\ntwice_native: (x: c.UInt): c.UInt = c.extern(\"oak_test_twice\")\n\npub twice: (x: u32): u32 {\n  doubled: c.UInt = twice_native(c.UInt(x))\n  u32(doubled)\n}\n",
		"hello/hello_test.oak": `package hello

import(testing)

TestTwice: (): () {
  test_check(twice(u32(21)) == u32(42), u32(1))
}

TableTwice: (row: []u8): () {
  x: u32 = test_row_u32(row, u32(0))
  want: u32 = test_row_u32(row, u32(4))
  test_check(twice(x) == want, u32(2))
}
`,
		"hello/testdata/oak/TableTwice/rows/001-one.bin":  row(1, 2),
		"hello/testdata/oak/TableTwice/rows/002-big.bin":  row(1000, 2000),
		"hello/testdata/oak/TableTwice/rows/003-zero.bin": row(0, 0),
	})
	object := filepath.Join(dir, "native", "twice.o")
	if out, err := exec.Command(cc, "-std=c99", "-c", "-o", object, filepath.Join(dir, "native", "twice.c")).CombinedOutput(); err != nil {
		t.Fatalf("cc -c: %v\n%s", err, out)
	}
	if out, err := exec.Command(ar, "rcs", filepath.Join(dir, "native", "libtwice.a"), object).CombinedOutput(); err != nil {
		t.Fatalf("ar: %v\n%s", err, out)
	}
	code, results, stderr := runCLI(t, filepath.Join(dir, "hello"))
	if code != 0 || len(results) != 2 {
		t.Fatalf("exit %d results %+v: %s", code, results, stderr)
	}
	for _, result := range results {
		if result.Status != "pass" {
			t.Fatalf("%s: %+v", result.Name, result)
		}
		if result.Name == "TableTwice" && result.Cases != 3 {
			t.Fatalf("table cases = %d", result.Cases)
		}
	}
	// Without the archive the manifest fails before any native build.
	if err := os.Remove(filepath.Join(dir, "native", "libtwice.a")); err != nil {
		t.Fatal(err)
	}
	code, _, stderr = runCLI(t, filepath.Join(dir, "hello"))
	if code == 0 {
		t.Fatalf("missing archive must fail: %s", stderr)
	}
}
