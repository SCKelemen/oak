package compiler

import "testing"

// A tag schema is declared once per package and visible to every file of
// it, whatever the files' order (docs/notes/oak-requests-2026-09-13.md
// finding 7): a record in a.oak may carry a tag whose schema z.oak
// declares.
func TestE2ETagSchemaVisibleAcrossPackageFiles(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/tags\noak 0.1.0\n",
		"a.oak": `package main

User: type = struct {
  id(json: "user_id"): u64
  name: string
}

main: (): i32 = 42
`,
		"z.oak": `package main

json: tag = { name: string }
`,
	})
	if _, err := New().WithPackageDir(root).Check().Get(); err != nil {
		t.Fatalf("schema declared in a later file of the package: %v", err)
	}
}
