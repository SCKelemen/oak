package compiler

import "testing"

// Buffer custody is per function (docs/spec/92-ffi.md section 2.8): a
// buffer handed back in one body leaves a same-named local of a later
// function untouched. Found by the certificate rung's solver driver, whose
// `body` buffer poisoned every later `body` in the program.
func TestBufferCustodyIsPerFunction(t *testing.T) {
	src := `
malloc: (n: c.Size): c.Ptr = c.extern("malloc")
free: (p: c.Ptr): () = c.extern("free")
first: (): u32 {
  raw: c.Ptr = malloc(c.Size(u32(16)))
  total: u32 = 0
  unsafe {
    body: Buffer[u8] = c.own[u8](raw, u32(16))
    total = len(view(&body))
    free(c.disown(body))
  }
  total
}
second: (): u32 {
  raw: c.Ptr = malloc(c.Size(u32(8)))
  total: u32 = 0
  unsafe {
    body: Buffer[u8] = c.own[u8](raw, u32(8))
    total = len(view(&body))
    free(c.disown(body))
  }
  total
}
main: (): i32 = first() + second() == u32(24) ? 42 | 1
`
	code, abnormal := buildAndRun(t, "buffer_custody_scope", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
