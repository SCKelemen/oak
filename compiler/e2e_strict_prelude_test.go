package compiler

import "testing"

// The standard library under the strict profile (ml third-list item 6): a
// strict-profile module may import json, strings, hash, or mx and use the
// derived JSON encoder without a strict diagnostic, so choosing strict for
// a root module never forces it back to default because of the prelude.
func TestStrictProfileAdmitsStandardLibrary(t *testing.T) {
	for name, main := range map[string]string{
		"json":    "import(\"json\")\nmain: (): i32 {\n  _ = json.json_encoder()\n  42\n}\n",
		"strings": "import(\"strings\")\nmain: (): i32 { i32(strings.ascii_lower(u8(65))) - 55 }\n",
		"hash":    "import(\"hash\")\nmain: (): i32 {\n  data: [4]u8\n  i32_bits_u32(hash.crc32c(view(&data)) & u32(0)) + 42\n}\n",
		"mx":      "import(\"mx\")\nmain: (): i32 { i32(mx.fp4_round_f32(6.0)) + 35 }\n",
	} {
		root := writeModule(t, map[string]string{
			"oak.mod":  "module example.com/strict" + name + "\noak 0.1.0\nprofile strict\n",
			"main.oak": "package main\n" + main,
		})
		code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
		if abnormal || code != 42 {
			t.Fatalf("%s under strict: exit (%d, abnormal=%v), want 42", name, code, abnormal)
		}
	}
	src := derivedJsonPrelude + "main: (): i32 {\n data: [128]u8\n dst: [*]u8 = span(&data)\n assert(json_result_ok(encode[Record, Json](make_record(), dst)))\n 42\n}\n"
	if _, err := New().WithSource("derived.oak", src).WithProfile("strict").EmitC().Get(); err != nil {
		t.Fatalf("derived JSON codec under strict: %v", err)
	}
}
