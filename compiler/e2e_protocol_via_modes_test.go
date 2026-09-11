package compiler

import (
	"errors"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

// Parameter modes on protocol `via` lines (docs/spec/112-protocols.md
// section 5): `via close(consumed h)` declares, in source, the resource
// contract the checker enforces, and because protocol declarations are
// elaborated with internal names the contract travels with the package
// that declares it into every importer, sealed imports included.
const viaModesSource = `
Handle: type = struct { id: u32 }
inspect: (h: Handle): () = {}
close: (h: Handle): () = {}

Lifecycle: protocol = {
  resource Handle
  initial Open
  look: Open -> Open via inspect(borrowed h)
  shut: Open -> Closed via close(consumed h)
}
`

func viaModesError(t *testing.T, name, body string) error {
	t.Helper()
	_, err := New().WithSource(name+".oak", viaModesSource+body).Check().Get()
	return err
}

func TestViaModesDeclareContractsInSource(t *testing.T) {
	if err := viaModesError(t, "via-borrowed", `
f: (h: Handle): u32 {
  inspect(h)
  inspect(h)
  h.id
}
`); err != nil {
		t.Fatalf("a borrowed via mode must keep the handle live: %v", err)
	}
	expectCode(t, "via-consumed", viaModesError(t, "via-consumed", `
f: (h: Handle): u32 {
  close(h)
  h.id
}
`), typechecker.CodeResourceUsedAfterConsume)
	// The wrapper rule of section 9 follows from the source declaration too
	// (one protocol governs a resource type, so peek joins Lifecycle).
	wrapper := strings.Replace(viaModesSource, "  shut: Open -> Closed via close(consumed h)\n", "  shut: Open -> Closed via close(consumed h)\n  peek: Open -> Open via peek(borrowed h)\n", 1)
	_, err := New().WithSource("via-wrapper.oak", wrapper+`
peek: (h: Handle): u32 {
  close(h)
  h.id
}
`).Check().Get()
	expectCode(t, "via-wrapper", err, typechecker.CodeResourceParameterForwarded)
}

func TestViaModesShapeErrors(t *testing.T) {
	cases := map[string]string{
		"unknown parameter": "Bad: protocol = {\n  resource Handle\n  initial Open\n  shut: Open -> Closed via close(consumed g)\n}\n",
		"twice":             "Bad: protocol = {\n  resource Handle\n  initial Open\n  shut: Open -> Closed via close(consumed h, borrowed h)\n}\n",
		"no receiver":       "Bad: protocol = {\n  resource Handle\n  initial Open\n  shut: Open -> Closed via close(consumed receiver)\n}\n",
	}
	for name, body := range cases {
		err := viaModesError(t, name, body)
		if err == nil || !strings.Contains(err.Error(), CodeProtocolShape) {
			t.Errorf("%s: want %s, got %v", name, CodeProtocolShape, err)
		}
	}
	if _, err := New().WithSource("bad-mode.oak", "Handle: type = struct { id: u32 }\nclose: (h: Handle): () = {}\nBad: protocol = {\n  resource Handle\n  initial Open\n  shut: Open -> Closed via close(owned h)\n}\n").Check().Get(); err == nil || !strings.Contains(err.Error(), "expected a parameter mode") {
		t.Errorf("unknown mode word: got %v", err)
	}
}

func TestViaModesTravelWithImports(t *testing.T) {
	geo := `package geo
pub Handle: type = struct { id: u32 }
pub open: (id: u32): Handle = Handle { id: id }
pub inspect: (h: Handle): () = {}
pub close: (h: Handle): () = {}

pub Lifecycle: protocol = {
  resource Handle
  initial Open
  look: Open -> Open via inspect(borrowed h)
  shut: Open -> Closed via close(consumed h)
}
`
	// An importer consuming through the qualified call loses the handle.
	root := writeModule(t, map[string]string{
		"oak.mod":     "module example.com/via\noak 0.1.0\n",
		"geo/geo.oak": geo,
		"main.oak": `package main
import("example.com/via/geo")
finish: (h: geo.Handle): u32 {
  geo.inspect(h)
  geo.close(h)
  h.id
}
main: (): i32 = i32_bits_u32(finish(geo.open(u32(1))))
`,
	})
	_, err := New().WithPackageDir(root).Check().Get()
	var diagnosticErr *DiagnosticError
	if !errors.As(err, &diagnosticErr) {
		t.Fatalf("expected a diagnostic error through the import, got %v", err)
	}
	found := false
	for _, d := range diagnosticErr.Diagnostics {
		if d != nil && d.Code == typechecker.CodeResourceUsedAfterConsume {
			found = true
		}
	}
	if !found {
		for _, d := range diagnosticErr.Diagnostics {
			t.Logf("diagnostic: %s %s", d.Code, d.Title)
		}
		t.Fatalf("consumption declared in geo did not reach main")
	}
	// Borrowing through the import keeps it live and the program runs.
	live := writeModule(t, map[string]string{
		"oak.mod":     "module example.com/via2\noak 0.1.0\n",
		"geo/geo.oak": geo,
		"main.oak": `package main
import("example.com/via2/geo")
look_twice: (h: geo.Handle): u32 {
  geo.inspect(h)
  geo.inspect(h)
  h.id
}
main: (): i32 = i32_bits_u32(look_twice(geo.open(u32(42))))
`,
	})
	_, code, abnormal := buildAndRunFrom(t, "via2", New().WithPackageDir(live))
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
