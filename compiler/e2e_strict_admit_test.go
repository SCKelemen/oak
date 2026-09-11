package compiler

// `admit <code>` in oak.mod (docs/spec/85-discipline.md section 7, ml
// finding F22): a strict module states which recorded assumptions it
// accepts. The assumption stays recorded and audited; it stops rejecting the
// module's own packages. Admissions are per module, like profiles.

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A strict program that borrows runtime memory (92-ffi.md section 2.7).
// Before the directive, the OAK-B0110 contract warning made tier 4 unusable
// under strict.
const strictBorrowMain = `package main

table_ptr: (): c.Ptr = c.extern("oak_probe_table")

sum_table: (): u32 {
  total: u32 = 0
  p: c.Ptr = table_ptr()
  unsafe {
    v: []u32 = c.borrow[u32](p, u32(8))
    total = v[0] + v[7]
  }
  total
}

main: (): i32 { i32_bits_u32(sum_table()) }
`

func TestStrictModuleRejectsForeignBorrowWithoutAdmission(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\noak 0.1.0\nprofile strict\n",
		"main.oak": strictBorrowMain,
	})
	_, err := New().WithPackageDir(root).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-B0110") {
		t.Fatalf("a strict module without an admission must still reject the foreign-buffer contract, got %v", err)
	}
}

func TestStrictModuleAdmitsForeignBorrow(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\noak 0.1.0\nprofile strict\nadmit OAK-B0110\n",
		"main.oak": strictBorrowMain,
	})
	var recorded []*diagnostic.Diagnostic
	comp := New().WithPackageDir(root).WithDiagnosticSink(func(d *diagnostic.Diagnostic) { recorded = append(recorded, d) })
	if _, err := comp.EmitC().Get(); err != nil {
		t.Fatalf("admit OAK-B0110 must let the strict module borrow: %v", err)
	}
	// The assumption is still recorded, and says the manifest admitted it.
	found := false
	for _, d := range recorded {
		if d.Code != "OAK-B0110" {
			continue
		}
		found = true
		if d.Severity != diagnostic.SeverityWarning {
			t.Fatalf("an admitted assumption keeps its severity, got %v", d.Severity)
		}
		if !strings.Contains(d.PlainText(), "admitted by oak.mod (`admit OAK-B0110`)") {
			t.Fatalf("an admitted assumption names the directive that admitted it:\n%s", d.PlainText())
		}
	}
	if !found {
		t.Fatal("the OAK-B0110 assumption must remain recorded after admission")
	}
	// The admission does not widen: another recorded assumption still rejects.
	root = writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\noak 0.1.0\nprofile strict\nadmit OAK-B0110\n",
		"main.oak": "main: (): i32 { i32_bits_u32(spin(u32(3))) }\n" + unboundedLoop,
	})
	_, err := New().WithPackageDir(root).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-D0103") {
		t.Fatalf("admitting OAK-B0110 must not admit OAK-D0103, got %v", err)
	}
	// The command-line profile flag grants no admission a manifest lacks.
	root = writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\noak 0.1.0\n",
		"main.oak": strictBorrowMain,
	})
	_, err = New().WithPackageDir(root).WithProfile("strict").EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-B0110") {
		t.Fatalf("-profile strict without a manifest admission must reject, got %v", err)
	}
}

// A dependency's manifest speaks for its own packages: its admission covers
// its assumptions and nothing of the root's.
func TestStrictDependencyAdmitsItsOwnAssumption(t *testing.T) {
	files := map[string]string{
		"app/oak.mod": "module example.com/app\noak 0.1.0\nrequire example.com/lib 1.0.0\nreplace example.com/lib => ../lib\n",
		"app/main.oak": `package main
import("example.com/lib")

main: (): i32 {
  i32_bits_u32(lib.spin(u32(3)))
}
`,
		"lib/oak.mod": "module example.com/lib\noak 0.1.0\nprofile strict\nadmit OAK-D0103\n",
		"lib/lib.oak": "package lib\n" + unboundedLoop,
	}
	root := writeModule(t, files)
	if _, err := New().WithPackageDir(root + "/app").EmitC().Get(); err != nil {
		t.Fatalf("a strict dependency that admits OAK-D0103 compiles: %v", err)
	}
	// The root does not inherit the dependency's admission.
	files["app/oak.mod"] = "module example.com/app\noak 0.1.0\nprofile strict\nrequire example.com/lib 1.0.0\nreplace example.com/lib => ../lib\n"
	files["app/main.oak"] = "package main\nimport(\"example.com/lib\")\n\nmain: (): i32 { i32_bits_u32(spin(u32(3)) + lib.spin(u32(1))) }\n" + unboundedLoop
	root = writeModule(t, files)
	_, err := New().WithPackageDir(root + "/app").EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-D0103") {
		t.Fatalf("the root's own OAK-D0103 is not covered by the dependency's admission, got %v", err)
	}
}
