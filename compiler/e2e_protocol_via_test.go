package compiler

import "testing"

// A `via`-bound transition projects into the resource protocol facts; a
// program whose callable exists and takes the governed type compiles.
func TestProtocolViaProjectsResourceFacts(t *testing.T) {
	src := `
Handle: type = struct { id: u32 }
Access: protocol = {
  resource Handle
  initial Closed
  open: Closed -> Open via open_handle
  close: Open -> Closed via close_handle
}
open_handle: (h: Handle): () = {}
close_handle: (h: Handle): () = {}
main: (): i32 {
  h: Handle = Handle { id: u32(1) }
  open_handle(h)
  close_handle(h)
  s: AccessState = access_initial()
  ok: Bool = access_legal(s, .Open)
  ok ? { 42 } | { 0 }
}
`
	code, abnormal := buildAndRun(t, "protocol_via", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
