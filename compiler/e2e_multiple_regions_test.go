package compiler

import (
	"path/filepath"
	"strings"
	"testing"
)

const multipleRegionsDeclarations = `
Parts[A, B]: type = struct { header: View[u8, A], payload: View[u8, B] }
parts[A, B]: (a: View[u8, A], b: View[u8, B]): Parts[A, B] = Parts { header: a, payload: b }
forward[A, B]: (p: Parts[A, B]): Parts[A, B] = p
header[A, B]: (p: Parts[A, B]): View[u8, A] = p.header
payload[A, B]: (p: Parts[A, B]): View[u8, B] = subslice(p.payload, 0, 1)
swap[A, B]: (p: Parts[A, B]): Parts[B, A] = Parts { header: p.payload, payload: p.header }
`

func TestE2EMultipleRegionRecords(t *testing.T) {
	src := multipleRegionsDeclarations + `
main: (): i32 {
 a: [1]u8 = [1]u8{ 10 }
 b: [1]u8 = [1]u8{ 32 }
 p: Parts = forward(parts(view(&a), view(&b)))
 q: Parts = swap(p)
 h: []u8 = header(q)
 t: []u8 = payload(q)
 i32(h[0]) + i32(t[0])
}`
	out, err := New().WithSource("multiple-regions.oak", src).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out, "oak_Parts oak_parts( oak_view_u8 a, oak_view_u8 b )") {
		t.Fatalf("regions were not erased from C signature")
	}
	code, abnormal := buildAndRun(t, "multiple-regions", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, %v), want 42", code, abnormal)
	}
	if got := interpretChecked(t, src); got != 42 {
		t.Fatalf("interpreter = %d", got)
	}
}

func TestMultipleRegionRecordsRejections(t *testing.T) {
	cases := []struct{ name, body, code string }{
		{"swapped fields", `bad[A,B]: (a: View[u8,A], b: View[u8,B]): Parts[A,B] = Parts {header:b, payload:a}`, "OAK-B0113"},
		{"wrong projected field", `bad[A,B]: (p: Parts[A,B]): View[u8,A] = p.payload`, "OAK-B0113"},
		{"wrong returned call field", `bad[A,B]: (p: Parts[A,B]): View[u8,A] = payload(p)`, "OAK-B0113"},
		{"local in second field", `bad[A,B]: (a: View[u8,A], b: View[u8,B]): Parts[A,B] { local: [1]u8 = [1]u8{9}; Parts {header:a, payload:view(&local)} }`, "OAK-B0113"},
		{"laundered local", `bad[A,B]: (a: View[u8,A], b: View[u8,B]): Parts[A,B] { local: [1]u8 = [1]u8{9}; p: Parts = parts(a, view(&local)); forward(p) }`, "OAK-B0113"},
		{"ambiguous region", `bad[A,B]: (p: Parts[A,A], b: View[u8,B]): Parts[A,B] = Parts {header:p.header,payload:b}`, "OAK-B0113"},
		{"owner header write", `main: (): i32 { a:[1]u8=[1]u8{1}; b:[1]u8=[1]u8{2}; p:Parts=parts(view(&a),view(&b)); a[0]=9; i32(p.header[0]) }`, "OAK-B0103"},
		{"owner payload write", `main: (): i32 { a:[1]u8=[1]u8{1}; b:[1]u8=[1]u8{2}; p:Parts=forward(parts(view(&a),view(&b))); b[0]=9; i32(p.payload[0]) }`, "OAK-B0103"},
		{"conditional wrong field", `bad[A,B]: (p: Parts[A,B], yes:Bool): Parts[A,B] = yes ? {p} | {Parts {header:p.payload,payload:p.header}}`, "OAK-B0113"},
		{"local record alias", `bad[A,B]: (a: View[u8,A], b: View[u8,B]): Parts[A,B] { local:[1]u8=[1]u8{1}; p:Parts=Parts {header:a,payload:view(&local)}; q:Parts=p; q }`, "OAK-B0113"},
		{"record overwrite", `bad[A,B]: (a: View[u8,A], b: View[u8,B]): Parts[A,B] { p:Parts=parts(a,b); p.payload=a; p }`, "OAK-B0109"},
		{"projection binding owner write", `main: (): i32 { a:[1]u8=[1]u8{1}; b:[1]u8=[1]u8{2}; p:Parts=parts(view(&a),view(&b)); v:[]u8=p.payload; b[0]=9; i32(v[0]) }`, "OAK-B0103"},
		{"temporary projection owner write", `main: (): i32 { a:[1]u8=[1]u8{1}; b:[1]u8=[1]u8{2}; v:[]u8=parts(view(&a),view(&b)).payload; b[0]=9; i32(v[0]) }`, "OAK-B0103"},
		{"indirect call", `main: (): i32 { a:[1]u8=[1]u8{1}; b:[1]u8=[1]u8{2}; f := parts; p:Parts=f(view(&a),view(&b)); b[0]=9; i32(p.payload[0]) }`, "OAK-B0109"},
		{"ADT wrapper", `Maybe[T]: type = Some:T | None
bad[A,B]: (a:View[u8,A], b:View[u8,B]): Maybe[Parts[A,B]] = .Some(Parts {header:a,payload:b})`, "OAK-B0113"},
		{"derived temporary projection", `main: (): i32 { a:[1]u8=[1]u8{1}; b:[1]u8=[1]u8{2}; v:[]u8=parts(view(&a),view(&b)).payload[0:1]; b[0]=9; i32(v[0]) }`, "OAK-B0113"},
		{"mutable record", `Mutable[A,B]: type = struct { a:Span[u8,A], b:View[u8,B] }
bad[A,B]: (a:Span[u8,A], b:View[u8,B]): Mutable[A,B] = Mutable {a:a,b:b}`, "OAK-B0113"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			src := multipleRegionsDeclarations + c.body
			if !strings.Contains(c.body, "main:") {
				src += "\nmain: (): i32 {0}"
			}
			_, err := New().WithSource("reject-multiple.oak", src).Check().Get()
			if err == nil || !strings.Contains(err.Error(), c.code) {
				t.Fatalf("error = %v; want %s", err, c.code)
			}
		})
	}
}

// A returned projection keeps only its own owner borrowed. The temporary
// aggregate is never bound in this scope, so its other field must not linger.
func TestMultipleRegionProjectionReleasesUnrelatedOwner(t *testing.T) {
	src := multipleRegionsDeclarations + `
main: (): i32 {
 a:[1]u8=[1]u8{10}
 b:[1]u8=[1]u8{32}
 h:[]u8=header(parts(view(&a),view(&b)))
 b[0]=32
 i32(h[0])+i32(b[0])
}`
	for _, source := range []string{src, strings.Replace(src, "header(parts(view(&a),view(&b)))", "parts(view(&a),view(&b)).header", 1)} {
		code, abnormal := buildAndRun(t, "region-projection", source)
		if abnormal || code != 42 {
			t.Fatalf("exit = (%d,%v)", code, abnormal)
		}
	}
}

func TestE2EMultipleRegionNestedRecords(t *testing.T) {
	// Deliberately declare the outer record first, and retain an ordinary type
	// parameter beside its regions through specialization.
	src := `
Envelope[T,A,B]: type = struct { tag:T, parts:Pair[A,B] }
Pair[A,B]: type = struct { left:View[u8,A], right:View[u8,B] }
pack[A,B]: (a:View[u8,A], b:View[u8,B]): Envelope[u8,A,B] = Envelope {tag:0u8,parts:Pair {left:a,right:b}}
right[A,B]: (p:Envelope[u8,A,B]): View[u8,B] = p.parts.right
choose[A,B]: (a:View[u8,A], b:View[u8,B], first:Bool): Pair[A,B] = first ? { Pair {left:a,right:b} } | { Pair {left:subslice(a,0,1),right:b} }
main: (): i32 {
 a:[1]u8=[1]u8{10}
 b:[1]u8=[1]u8{32}
 p:Envelope[u8]=pack(view(&a),view(&b))
 q:Pair=choose(view(&a),view(&b),false)
 v:[]u8=right(p)
 i32(q.left[0])+i32(v[0])
}`
	code, abnormal := buildAndRun(t, "nested-regions", src)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d,%v)", code, abnormal)
	}
}

func TestE2EModuleMultipleRegions(t *testing.T) {
	files := map[string]string{
		"oak.mod":         helloManifest,
		"parts/parts.oak": "package parts\n" + strings.ReplaceAll(strings.TrimSpace(multipleRegionsDeclarations), "\n", "\npub "),
		"forward/forward.oak": `package forward
p := import("example.com/hello/parts")
pub payload[A,B]: (a:View[u8,A], b:View[u8,B]): View[u8,B] = p.payload(p.forward(p.parts(a,b)))
`,
		"app/main.oak": `package app
f := import("example.com/hello/forward")
main: (): i32 {
 a:[1]u8=[1]u8{10}
 b:[1]u8=[1]u8{32}
 v:[]u8=f.payload(view(&a),view(&b))
 a[0]=10
 i32(a[0])+i32(v[0])
}`,
	}
	files["parts/parts.oak"] = strings.Replace(files["parts/parts.oak"], "package parts\nParts", "package parts\npub Parts", 1)
	root := writeModule(t, files)
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(filepath.Join(root, "app")))
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d,%v)", code, abnormal)
	}
	files["app/main.oak"] = strings.Replace(files["app/main.oak"], "a[0]=10", "b[0]=10", 1)
	expectModuleError(t, writeModule(t, files), "app", "OAK-B0103")
	files["parts/parts.oak"] = strings.Replace(files["parts/parts.oak"], "Parts { header: a, payload: b }", "Parts { header: b, payload: a }", 1)
	expectModuleError(t, writeModule(t, files), "app", "OAK-B0113")
}
