package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/packageapi"
	"github.com/SCKelemen/oak/typechecker"
)

func indexedAPISnapshot(t *testing.T, source, version string) packageapi.Snapshot {
	t.Helper()
	snapshot, err := New().WithPackageName("example/indexed").WithSource("api.oak", source).APISnapshot(version).Get()
	if err != nil {
		t.Fatalf("API snapshot failed: %v", err)
	}
	return snapshot
}

func TestAPISnapshotPreservesIndexedTypeContracts(t *testing.T) {
	cases := []struct {
		name, source, export, want string
	}{
		{"view", `pub take: (value: [align 64]u8): u32 = len(value)`, "take", "fn([align 64]u8)->u32"},
		{"span", `pub take: (value: [* align 64]u8): u32 = len(value)`, "take", "fn([*align 64]u8)->u32"},
		{"view return", `pub identity: (value: [align 64]u8): [align 64]u8 = value`, "identity", "fn([align 64]u8)->[align 64]u8"},
		{"span return", `pub identity: (value: [* align 64]u8): [* align 64]u8 = value`, "identity", "fn([*align 64]u8)->[*align 64]u8"},
		{"nested view", `pub Buffer: type = { data: [4][align 64]u8 }`, "Buffer", "record{data:[4][align 64]u8}"},
		{"view of arrays", `pub take: (value: [align 64][4]u8): u32 = 0`, "take", "fn([align 64][4]u8)->u32"},
		{"span of arrays", `pub take: (value: [* align 64][4]u8): u32 = 0`, "take", "fn([*align 64][4]u8)->u32"},
		{"function parameter", `pub take: (callback: ([align 64]u8) -> u32): u32 = 0`, "take", "fn(fn([align 64]u8)->u32)->u32"},
		{"generic function", `pub take[N: u32]: (value: [N+1]u8): u32 = N`, "take", "forall[N:u32].fn([N+1]u8)->u32"},
		{"view field", `pub Buffer: type = { data: [align 64]u8 }`, "Buffer", "record{data:[align 64]u8}"},
		{"span field", `pub Buffer: type = { data: [* align 64]u8 }`, "Buffer", "record{data:[*align 64]u8}"},
		{"symbolic array", `pub Buffer[T, N: u32]: type = { data: [N]T }`, "Buffer", "record[T,N:u32]{data:[N]T}"},
		{"unary extent", `pub Buffer[T, N: u32]: type = { data: [(-N)]T }`, "Buffer", "record[T,N:u32]{data:[(-N)]T}"},
		{"arithmetic array", `pub Buffer[T, N: u32]: type = { data: [N+1]T }`, "Buffer", "record[T,N:u32]{data:[N+1]T}"},
		{"const generic", `Ring[T, N: u32]: type = { data: [N]T }
pub Buffer: type = Ring[u8, 4]`, "Buffer", "alias(Ring[u8,4])"},
		{"nested const generic", `Ring[T, N: u32]: type = { data: [N]T }
pub Buffer: type = { data: [2]Ring[u8, 4] }`, "Buffer", "record{data:[2]Ring[u8,4]}"},
		{"nested function field", `pub Buffer: type = { handlers: [2]([align 64]u8) -> u32 }`, "Buffer", "record{handlers:[2]fn([align 64]u8)->u32}"},
		{"nested record", `pub Buffer: type = { data: [2]{ z: [align 64]byte, a: u8 } }`, "Buffer", "record{data:[2]record{a:u8,z:[align 64]u8}}"},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			snapshot := indexedAPISnapshot(t, tc.source, "1.0.0")
			if got := snapshot.Exports[tc.export].Type; got != tc.want {
				t.Fatalf("%s type = %q, want %q", tc.export, got, tc.want)
			}
		})
	}
}

func TestAPISnapshotIndexedTypeBreakingChanges(t *testing.T) {
	cases := []struct {
		name, before, after string
	}{
		{"view alignment", `pub take: (value: []u8): u32 = 0`, `pub take: (value: [align 64]u8): u32 = 0`},
		{"span alignment", `pub take: (value: [*]u8): u32 = 0`, `pub take: (value: [* align 64]u8): u32 = 0`},
		{"weaker return alignment", `pub identity: (value: [align 64]u8): [align 64]u8 = value`, `pub identity: (value: [align 64]u8): []u8 = value`},
		{"stronger alignment", `pub take: (value: [align 32]u8): u32 = 0`, `pub take: (value: [align 64]u8): u32 = 0`},
		{"nested alignment", `pub Buffer: type = { data: [4][]u8 }`, `pub Buffer: type = { data: [4][align 64]u8 }`},
		{"array length", `pub take: (value: [4]u8): u32 = 0`, `pub take: (value: [8]u8): u32 = 0`},
		{"view to span", `pub take: (value: []u8): u32 = 0`, `pub take: (value: [*]u8): u32 = 0`},
		{"nested function alignment", `pub take: (callback: ([]u8) -> u32): u32 = 0`, `pub take: (callback: ([align 64]u8) -> u32): u32 = 0`},
		{"alias element alignment", `Byte: type = u8
pub take: (value: []Byte): u32 = 0`, `Byte: type = u8
pub take: (value: [align 64]Byte): u32 = 0`},
		{"alignment versus symbolic extent", `pub Buffer[align64: u32]: type = { data: [align64]u8 }`, `pub Buffer[align64: u32]: type = { data: [align 64]u8 }`},
		{"symbolic extent", `pub Buffer[T, N: u32]: type = { data: [N]T }`, `pub Buffer[T, N: u32]: type = { data: [N+1]T }`},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			before := indexedAPISnapshot(t, tc.before, "1.0.0")
			after := indexedAPISnapshot(t, tc.after, "1.0.1")
			if report := packageapi.Compare(before, after); report.Required != packageapi.Major {
				t.Fatalf("contract change classified as %s: %#v -> %#v", report.Required, before.Exports, after.Exports)
			}
			if _, err := packageapi.Enforce(before, after); err == nil {
				t.Fatal("patch publication accepted changed indexed type contract")
			}
			after.Version = "2.0.0"
			if _, err := packageapi.Enforce(before, after); err != nil {
				t.Fatalf("major publication rejected: %v", err)
			}
		})
	}
}

func TestAPISnapshotIndexedTypeEquivalentSpellings(t *testing.T) {
	cases := []struct {
		name, before, after string
	}{
		{"checked primitive alias", `pub take: (value: [align 64]byte): u32 = 0`, `pub take: (value: [align 64]u8): u32 = 0`},
		{"named alias definition", `pub Byte: type = byte
pub take: (value: [align 64]Byte): u32 = 0`, `pub Byte: type = u8
pub take: (value: [align 64]Byte): u32 = 0`},
		{"declared primitive alias", `pub Buffer: type = { data: [* align 64]byte }`, `pub Buffer: type = { data: [* align 64]u8 }`},
		{"array extent", `pub Buffer: type = { data: [0x4]byte }`, `pub Buffer: type = { data: [4]u8 }`},
		{"const generic", `Ring[T, N: u32]: type = { data: [N]T }
pub Bytes: type = Ring[byte, 0x4]`, `Ring[T, N: u32]: type = { data: [N]T }
pub Bytes: type = Ring[u8, 4]`},
		{"symbolic extent spelling", `pub Buffer[T, N: u32]: type = { data: [N+0x1]T }`, `pub Buffer[T, N: u32]: type = { data: [(N + 1)]T }`},
		{"nested field order", `pub Buffer: type = { data: [2]{ z: [align 64]byte, a: u8 } }`, `pub Buffer: type = { data: [2]{ a: u8, z: [align 64]u8 } }`},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			before := indexedAPISnapshot(t, tc.before, "1.0.0")
			after := indexedAPISnapshot(t, tc.after, "1.0.1")
			if report, err := packageapi.Enforce(before, after); err != nil || report.Required != packageapi.Patch {
				t.Fatalf("equivalent types need more than a patch: report=%#v error=%v; %#v -> %#v", report, err, before.Exports, after.Exports)
			}
		})
	}
}

func TestCanonicalIndexedTypeNesting(t *testing.T) {
	// Borrowed aggregates are currently rejected as function parameters. Check
	// the recursive projection itself without claiming that use is admitted.
	checked := &typechecker.ArrayType{
		Length: 4,
		ElementType: &typechecker.ArrayType{
			Length: -1, IsSlice: true, Align: 64,
			ElementType: &typechecker.PrimitiveType{Name: "byte"},
		},
	}
	if got := canonicalCheckedType(checked); got != "[4][align 64]u8" {
		t.Fatalf("nested checked identity = %q", got)
	}

	// Generic arguments remain nested types; they are not flattened into the
	// outer application's argument list because their spelling ends with ']'.
	syntax := &ast.IndexExpression{
		TypeForm: ast.IndexGenericType,
		Left:     &ast.Identifier{Value: "Box"},
		Index: &ast.IndexExpression{
			TypeForm: ast.IndexArrayType, Align: 64,
			Left: &ast.Identifier{Value: "byte"}, Index: &ast.Identifier{},
		},
	}
	if got, err := canonicalTypeExpression(syntax); err != nil || got != "Box[[align 64]u8]" {
		t.Fatalf("nested syntax identity = %q, %v", got, err)
	}
}

func TestAPISnapshotRejectsUnrepresentedCallableEffects(t *testing.T) {
	for _, source := range []string{
		`pub apply: (callback: (u8) -> u32 effects { }): u32 = 0`,
		`pub apply: (callback: (u8) -> u32 effects { Host.Read }): u32 = 0`,
		`pub keep: (callback: (u8) -> u32 effects { Host.Read }): (u8) -> u32 effects { Host.Read } = callback`,
		`Callback: type = | Callback: (u8) -> u32 effects { Host.Read }
pub apply: (callback: Callback): u32 = 0`,
		`Callback: type = | Callback: (u8) -> u32 effects { Host.Read }
hidden: (value: u8): u32 = 0
pub callback: Callback = .Callback(hidden)`,
		`Callback: type = | Callback: (u8) -> u32 effects { Host.Read }
hidden: (value: u8): u32 = 0
pub make: (): Callback = .Callback(hidden)`,
		`hidden: (value: u8): u32 = 0
pub get: (): ((u8) -> u32 effects { }) = hidden`,
		`Hidden: type = | Hidden: (u8) -> u32 effects { Host.Read }
Alias: type = Hidden
pub apply[Hidden]: (callback: Alias): u32 = 0`,
		`pub Buffer: type = { handler: (u8) -> u32 effects { } }`,
		`pub Buffer: type = { handler: (u8) -> u32 effects { Host.Read } }`,
		`pub Buffer: type = { handlers: [2](u8) -> u32 effects { } }`,
		`pub Buffer: type = { handlers: [2](u8) -> u32 effects { Host.Read } }`,
		`pub Buffer: type = { handlers: [2]{ callback: (u8) -> u32 effects { Host.Read } } }`,
	} {
		compilation := New().WithSource("callable.oak", source)
		if _, err := compilation.Check().Get(); err != nil {
			t.Errorf("source must be checked before API projection (%s): %v", source, err)
			continue
		}
		_, err := compilation.APISnapshot("1.0.0").Get()
		if err == nil || !strings.Contains(err.Error(), "callable effect rows") {
			t.Errorf("incomplete callable identity must fail closed, got %v", err)
		}
	}
}

func TestAPISnapshotCallableRowGuardPreservesUnaffectedSurfaces(t *testing.T) {
	for name, source := range map[string]string{
		"unused private alias": `Callback: type = | Callback: (u8) -> u32 effects { Host.Read }
pub answer: (): u32 = 0`,
		"opaque representation": `pub(opaque) Handle: type = { callback: (u8) -> u32 effects { Host.Read } }
pub take: (value: Handle): u32 = 0`,
		"function type parameter": `Callback: type = | Callback: (u8) -> u32 effects { Host.Read }
pub identity[Callback]: (value: Callback): Callback = value`,
		"record type parameter": `Callback: type = | Callback: (u8) -> u32 effects { Host.Read }
pub Box[Callback]: type = { value: Callback }`,
		"outer effects":  `pub read: (): u32 effects { Host.Read } = 0`,
		"outer forbids":  `pub run: (): u32 forbids { Host.Read } = 0`,
		"plain callback": `pub apply: (callback: (u8) -> u32): u32 = 0`,
	} {
		t.Run(name, func(t *testing.T) {
			indexedAPISnapshot(t, source, "1.0.0")
		})
	}
}

func TestAPISnapshotCallableRowGuardRejectsAliasCycles(t *testing.T) {
	alias := func(name, target string) *ast.ADTType {
		return &ast.ADTType{
			Name: &ast.Identifier{Value: name}, Exported: true,
			Variants: []*ast.ADTVariant{{Name: &ast.Identifier{Value: name}, Payload: &ast.Identifier{Value: target}}},
		}
	}
	program := &ast.Program{Statements: []ast.Statement{alias("A", "B"), alias("B", "A")}}
	if err := validatePublicCallableRows(program); err == nil || !strings.Contains(err.Error(), "cyclic type alias") {
		t.Fatalf("cyclic alias guard = %v", err)
	}
}
