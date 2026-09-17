package asm

import (
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func verifyTableView(t *testing.T, decl, source, machine string, tables map[string]Table) Verdict {
	t.Helper()
	return verifyTableViewOn(t, "table_view.oakasm", decl, source, machine, tables)
}

func verifyTableViewOn(t *testing.T, file, decl, source, machine string, tables map[string]Table) Verdict {
	t.Helper()
	unit, errs := ParseUnit(file, decl+" = {\n"+machine+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	fn := unit.Functions[0]
	fn.Tables = tables
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	if findings := Check(fn, sig, nil); len(findings) != 0 {
		t.Fatalf("checker: %v", findings)
	}
	spec, err := parseSignatureWithBody(decl + " = {\n" + source + "\n}")
	if err != nil {
		t.Fatal(err)
	}
	return Verify(fn, sig, spec.Body)
}

func TestRV64VerifyConstantTableViews(t *testing.T) {
	tables := map[string]Table{"data_T": {Size: 16, Elem: 4}}
	for _, tc := range []struct {
		name, source, machine string
		want                  VerdictKind
	}{
		{"read", "t: []u32 = view(&T)\nt[1]", "  clobber t0\n  la t0, data_T\n  lwu a0, 4(t0)\n  ret", VerdictProven},
		{"wrong offset", "t: []u32 = view(&T)\nt[1]", "  clobber t0\n  la t0, data_T\n  lwu a0, 0(t0)\n  ret", VerdictMismatch},
		{"length", "t: []u32 = view(&T)\ns: []u32 = subslice(t, u32(1), u32(2))\nlen(s)", "  li a0, 2\n  ret", VerdictProven},
		{"wrong length", "t: []u32 = view(&T)\ns: []u32 = subslice(t, u32(1), u32(2))\nlen(s)", "  li a0, 4\n  ret", VerdictMismatch},
	} {
		t.Run(tc.name, func(t *testing.T) {
			v := verifyTableViewOn(t, "table_view.rv64.oakasm", "get: () -> u32", tc.source, tc.machine, tables)
			if v.Kind != tc.want {
				t.Fatalf("%s: %s, want %s", v.Kind, v.Message, tc.want)
			}
		})
	}
}

func TestVerifyConstantTableViews(t *testing.T) {
	tables := map[string]Table{"data_T": {Size: 16, Elem: 4}, "data_U": {Size: 16, Elem: 4}}
	load := "  bind w0 = i\n  clobber x9\n  cmp w0, #4\n  b.hs empty\n  adrl x9, data_T\n  ldr w0, [x9, w0, uxtw #2]\n  ret\nempty:\n  mov w0, #0\n  ret"
	for _, tc := range []struct {
		name, source, machine string
		want                  VerdictKind
	}{
		{"read", "t: []u32 = view(&T)\ni < len(t) ? t[i] | u32(0)", load, VerdictProven},
		{"alias", "t: []u32 = view(&T)\nu: []u32 = t\ni < len(u) ? u[i] | u32(0)", load, VerdictProven},
		{"wrong root", "t: []u32 = view(&U)\ni < len(t) ? t[i] | u32(0)", load, VerdictMismatch},
		{"length", "t: []u32 = view(&T)\nlen(t)", "  bind w0 = i\n  mov w0, #4\n  ret", VerdictProven},
		{"wrong length", "t: []u32 = view(&T)\nlen(t)", "  bind w0 = i\n  mov w0, #3\n  ret", VerdictMismatch},
		{"subslice length", "t: []u32 = view(&T)\nu: []u32 = subslice(t, u32(1), u32(2))\nlen(u)", "  bind w0 = i\n  mov w0, #2\n  ret", VerdictProven},
		{"subslice wrong length", "t: []u32 = view(&T)\nu: []u32 = subslice(t, u32(1), u32(2))\nlen(u)", "  bind w0 = i\n  mov w0, #4\n  ret", VerdictMismatch},
		{"subslice read", "t: []u32 = view(&T)\nu: []u32 = subslice(t, u32(1), u32(2))\nu[0]", "  bind w0 = i\n  clobber x9\n  adrl x9, data_T\n  ldr w0, [x9, #4]\n  ret", VerdictProven},
		{"subslice wrong offset", "t: []u32 = view(&T)\nu: []u32 = subslice(t, u32(1), u32(2))\nu[0]", "  bind w0 = i\n  clobber x9\n  adrl x9, data_T\n  ldr w0, [x9]\n  ret", VerdictMismatch},
	} {
		t.Run(tc.name, func(t *testing.T) {
			v := verifyTableView(t, "get: (i: u32) -> u32", tc.source, tc.machine, tables)
			if v.Kind != tc.want {
				t.Fatalf("got %s: %s, want %s", v.Kind, v.Message, tc.want)
			}
		})
	}
	// Signed table elements retain sign extension through the alias.
	v := verifyTableView(t, "get: () -> i64", "t: []i8 = view(&S)\ni64(t[0])",
		"  clobber x9\n  adrl x9, data_S\n  ldrsb x0, [x9]\n  ret", map[string]Table{"data_S": {Size: 4, Elem: 1, Signed: true}})
	if v.Kind != VerdictProven {
		t.Fatalf("signed table view: %s: %s", v.Kind, v.Message)
	}
}

// Even without a view constructor, an existing derived span must use its
// own length, not the length of the table at its root.
func TestVerifyTableSubsliceLength(t *testing.T) {
	tables := map[string]Table{"data_T": {Size: 16, Elem: 4}}
	source := "t: []u32 = subslice(T, u32(1), u32(2))\nlen(t)"
	for _, tc := range []struct {
		machine string
		want    VerdictKind
	}{
		{"  mov w0, #2\n  ret", VerdictProven},
		{"  mov w0, #4\n  ret", VerdictMismatch},
	} {
		v := verifyTableView(t, "length: () -> u32", source, tc.machine, tables)
		if v.Kind != tc.want {
			t.Fatalf("%s: got %s: %s, want %s", tc.machine, v.Kind, v.Message, tc.want)
		}
	}
}

func TestDeclareConstantTableViewRefusals(t *testing.T) {
	for _, tc := range []struct {
		name, param, source string
		globals             map[string]Global
	}{
		{"unknown", "", "t: []u32 = view(&U)", nil},
		{"wrong width", "", "t: []u64 = view(&T)", nil},
		{"mutable type", "", "t: [*]u32 = view(&T)", nil},
		{"mutable constructor", "", "t: []u32 = span(&T)", nil},
		{"scalar shadow", "T: u32", "t: []u32 = view(&T)", nil},
		{"local shadow", "", "T: u32 = u32(4)\nt: []u32 = view(&T)", nil},
		{"span shadow", "T: []u32", "t: []u32 = view(&T)", nil},
		{"mutable global", "", "t: []u32 = view(&G)", map[string]Global{"G": {Type: "(u32[4])", Size: 16, Aggregate: true}}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			sig, err := parseSignatureWithBody("f: (" + tc.param + ") -> u32 = {\n" + tc.source + "\nu32(0)\n}")
			if err != nil {
				t.Fatal(err)
			}
			lo := prepareLowering(&Function{Tables: map[string]Table{"data_T": {Size: 16, Elem: 4}}, Globals: tc.globals}, sig, nil)
			statements := sig.Body.(*ast.BlockExpression).Block.Statements
			for _, statement := range statements[:len(statements)-2] {
				if reason, ok := lo.declareLocal(statement.(*ast.VariableDeclaration)); !ok {
					t.Fatal(reason)
				}
			}
			decl := statements[len(statements)-2].(*ast.VariableDeclaration)
			if reason, ok := lo.declareLocal(decl); ok {
				t.Fatalf("unsupported table view accepted: %s", reason)
			}
		})
	}
}
