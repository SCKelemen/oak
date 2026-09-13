package compiler

import (
	"strings"
	"testing"
)

// A payload name carrying different types across steps names different
// domains (docs/notes/oak-requests-2026-09-13.md finding 2): two steps
// whose record payloads are both spelled `c` but of different types get
// two record-set domains and two constant families, each step quantifies
// over its own, and two scalars named `n` of different widths part ways
// the same way. Names that carry one type keep their old spelling.
func TestE2EProtocolPayloadDomainsDisambiguatedByType(t *testing.T) {
	source := `import(std)
Request: type = struct { k: u8, v: u8 }
Reply: type = struct { ok: Bool }
Rpc: protocol = {
  data { last: u32 }
  init { last: u32(0) }
  initial Idle
  send(c: Request): Idle -> Busy when u32(c.k) < u32(4) then { data.last = u32(c.v) }
  recv(c: Reply): Busy -> Idle when c.ok
  tick(n: u8): Idle -> Idle when u32(n) < u32(2)
  tock(n: u32): Idle -> Idle when n < u32(2)
}
main: (): i32 = 0
`
	tree, err := New().WithSource("rpc.oak", source).Parse().Get()
	if err != nil {
		t.Fatal(err)
	}
	decl := Protocols(tree)[0]
	records := RecordDeclarations(tree.Root)
	module, err := ProtocolTLAWithRecords(decl, "rpc.oak", records)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"CONSTANTS C_RequestK, C_RequestV, C_ReplyOk, N_u8, N_u32",
		"C_Request == [k: C_RequestK, v: C_RequestV]",
		"C_Reply == [ok: C_ReplyOk]",
		"(\\E c \\in C_Request : Send(c))",
		"(\\E c \\in C_Reply : Recv(c))",
		"(\\E n \\in N_u8 : Tick(n))",
		"(\\E n \\in N_u32 : Tock(n))",
	} {
		if !strings.Contains(module, want) {
			t.Fatalf("module lacks %q:\n%s", want, module)
		}
	}
	if strings.Contains(module, "CONSTANTS CK") || strings.Contains(module, "\nC == [") {
		t.Fatalf("a payload domain was keyed by the parameter name:\n%s", module)
	}
	// Every scalar domain runs one past the largest literal the guards
	// mention (4, in `u32(c.k) < u32(4)`; docs/spec/112-protocols.md §4).
	cfg := ProtocolTLCConfigWith(decl, records)
	for _, want := range []string{
		"    C_RequestK = {0, 1, 2, 3, 4, 5}\n", "    C_RequestV = {0, 1, 2, 3, 4, 5}\n", "    C_ReplyOk = {TRUE, FALSE}\n",
		"    N_u8 = {0, 1, 2, 3, 4, 5}\n", "    N_u32 = {0, 1, 2, 3, 4, 5}\n",
	} {
		if !strings.Contains(cfg, want) {
			t.Fatalf("configuration lacks %q:\n%s", want, cfg)
		}
	}
}
