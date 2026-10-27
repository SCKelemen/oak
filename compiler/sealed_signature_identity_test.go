package compiler

import "testing"

func TestSealedSignatureRejectsNominalShapeSubstitution(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"lib/lib.oak": `package lib
pub Stored: type = struct { x: u8 }
pub n: u8 = 42
pub read: (value: Stored): u8 = value.x
`,
		"main.oak": `package main
h: { read: ({ x: u8 }) -> u8, n: u8 } = import("example.com/hello/lib")
main: (): i32 = i32(h.n)
`,
	})
	expectModuleError(t, root, ".", "OAK-M0113")
}

func TestSealedSignaturePreservesPrimitiveAliases(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"lib/lib.oak": `package lib
pub read: (value: u8): u8 = value
`,
		"main.oak": `package main
h: { read: (byte) -> byte } = import("example.com/hello/lib")
main: (): i32 = i32(h.read(byte(42)))
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
