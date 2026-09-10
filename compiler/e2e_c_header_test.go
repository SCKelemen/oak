package compiler

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// The generated C header (docs/spec/92-ffi.md section 2.6) carries the
// exported surface: a C consumer includes it, constructs a record and an
// array wrapper, reads a tagged-union result through the named tag
// constants, and calls the pub functions; Oak reads the verdict back
// through an extern binding. No hand-written mirror types.
func TestE2EGeneratedHeaderConsumedFromC(t *testing.T) {
	src := `
Effect: type = None | Send: u32
Point: type = struct { x: i32, y: i32 }
pub make_point: (x: i32, y: i32): Point = Point { x: x, y: y }
pub total: (p: Point, d: [2]u32): u32 {
  u32_bits_i32(p.x + p.y) + d[0] + d[1]
}
pub next_effect: (n: u32): Effect {
  e: Effect = .None
  n > 0 ? { e = .Send(n) }
  e
}
helper: (n: u32): u32 = n + 1
probe: (): c.UInt = c.extern("probe_header")
main: (): i32 {
  assert(helper(0) == 1)
  assert(u32(probe()) == 42)
  42
}
`
	comp := New().WithSource("api.oak", src)
	header, err := comp.EmitHeader().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"#ifndef OAK_MAIN_H",
		"typedef struct oak_Point {",
		"typedef struct oak_Effect {",
		"typedef struct oak_arr_u32_2 { u32 v[ 2 ]; } oak_arr_u32_2;",
		"oak_Point oak_make_point( i32 x, i32 y );",
		"u32 oak_total( oak_Point p, oak_arr_u32_2 d );",
		"oak_Effect oak_next_effect( u32 n );",
		"#endif /* OAK_MAIN_H */",
	} {
		if !strings.Contains(header, want) {
			t.Fatalf("header lacks %q:\n%s", want, header)
		}
	}
	for _, private := range []string{"oak_helper", "oak_main", "probe_header", "oak_assert", "static u8"} {
		if strings.Contains(header, private) {
			t.Fatalf("header exposes private %q:\n%s", private, header)
		}
	}
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "api.h"), []byte(header), 0o644); err != nil {
		t.Fatal(err)
	}
	consumer := `
#include "api.h"
unsigned int probe_header(void) {
  oak_Point p = oak_make_point(20, 15);
  oak_arr_u32_2 d = { { 3, 4 } };
  oak_Effect e = oak_next_effect(7u);
  if (e.tag != oak_Effect_tag_Send || e.payload.Send != 7u) { return 0u; }
  oak_Effect none = oak_next_effect(0u);
  if (none.tag != oak_Effect_tag_None) { return 0u; }
  return oak_total(p, d);
}
`
	consumerPath := filepath.Join(dir, "consumer.c")
	if err := os.WriteFile(consumerPath, []byte(consumer), 0o644); err != nil {
		t.Fatal(err)
	}
	_, code, abnormal := buildAndRunFrom(t, "api", comp, "-I"+dir, consumerPath)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

// A package directory builds to one program, so its header carries the
// package's exported types and functions under the program's C names and
// leaves private functions out.
func TestGeneratedHeaderForPackageDirectory(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":       helloManifest,
		"util/util.oak": "package util\n\npub Box: type = struct { v: i32 }\npub boxed: (v: i32): Box = Box { v: v }\nunwrap: (b: Box): i32 = b.v\n",
	})
	header, err := New().WithPackageDir(filepath.Join(root, "util")).EmitHeader().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"#ifndef OAK_MAIN_H", "typedef struct oak_Box {", "oak_Box oak_boxed( i32 v );"} {
		if !strings.Contains(header, want) {
			t.Fatalf("header lacks %q:\n%s", want, header)
		}
	}
	if strings.Contains(header, "unwrap") {
		t.Fatalf("header exposes the private function:\n%s", header)
	}
}
