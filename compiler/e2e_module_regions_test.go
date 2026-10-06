package compiler

import (
	"path/filepath"
	"testing"
)

// Package elaboration must preserve the region declaration's identity and
// the caller's dependency, including through an intermediate package.
const moduleRegionLibrary = `package slices
pub Cursor[R]: type = struct { data: View[u8, R], pos: u32 }
pub open[R]: (buf: View[u8, R]): Cursor[R] = Cursor { data: buf, pos: 0 }
pub current[R]: (c: Cursor[R]): View[u8, R] = subslice(c.data, c.pos, 1)
pub tail[R]: (buf: Span[u8, R]): Span[u8, R] = subslice(buf, 1, 1)
pub first: (buf: []u8): []u8 = subslice(buf, 0, 1)
`

func moduleRegionFiles(main string) map[string]string {
	return map[string]string{
		"oak.mod":           helloManifest,
		"slices/slices.oak": moduleRegionLibrary,
		"forward/forward.oak": `package forward
s := import("example.com/hello/slices")
pub first[R]: (buf: View[u8, R]): View[u8, R] = s.first(buf)
`,
		"app/main.oak": main,
	}
}

func TestE2EModuleRegionReturns(t *testing.T) {
	root := writeModule(t, moduleRegionFiles(`package app
s := import("example.com/hello/slices")
f := import("example.com/hello/forward")
main: (): i32 {
  data: [2]u8 = [2]u8{ 21, 0 }
  cursor: s.Cursor = s.open(view(&data))
  a: []u8 = s.current(cursor)
  b: []u8 = f.first(view(&data))
  i32(a[0]) + i32(b[0])
}
`))
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(filepath.Join(root, "app")))
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}

func TestModuleRegionReturnsRejectOwnerWrite(t *testing.T) {
	root := writeModule(t, moduleRegionFiles(`package app
f := import("example.com/hello/forward")
main: (): i32 {
  data: [2]u8 = [2]u8{ 21, 0 }
  v: []u8 = f.first(view(&data))
  data[0] = 0
  i32(v[0])
}
`))
	expectModuleError(t, root, "app", "OAK-B0103")
}

func TestModuleRegionReturnsSuspendSpan(t *testing.T) {
	root := writeModule(t, moduleRegionFiles(`package app
s := import("example.com/hello/slices")
main: (): i32 {
  data: [2]u8 = [2]u8{ 21, 0 }
  parent: [*]u8 = span(&data)
  child: [*]u8 = s.tail(parent)
  parent[0] = 0
  i32(child[0])
}
`))
	expectModuleError(t, root, "app", "OAK-B0107")
}

func TestModuleRegionReturnsRejectLocalEscape(t *testing.T) {
	files := moduleRegionFiles(`package app
s := import("example.com/hello/slices")
main: (): i32 {
  data: [2]u8 = [2]u8{ 21, 0 }
  v: []u8 = s.first(view(&data))
  i32(v[0])
}
`)
	files["slices/slices.oak"] = `package slices
pub first[R]: (buf: View[u8, R]): View[u8, R] {
  local: [2]u8 = [2]u8{ 1, 2 }
  view(&local)
}
`
	expectModuleError(t, writeModule(t, files), "app", "OAK-B0113")
}
