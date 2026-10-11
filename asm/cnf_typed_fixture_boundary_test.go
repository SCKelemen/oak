package asm

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestTypedCNFFixtureJSONBoundaries(t *testing.T) {
	valid := []byte(`{"id":0,"kind":1,"width":64,"declared":0,"cond":-1,"left":-1,"right":-1,"value":18446744073709551615,"name":"","op":"","args":[]}`)
	node, err := typedFixtureDecodeNode(valid)
	if err != nil || node.Value != ^uint64(0) {
		t.Fatalf("exact uint64 boundary: value=%d error=%v", node.Value, err)
	}
	cases := map[string][]byte{
		"duplicate":         bytes.Replace(valid, []byte(`"id":0`), []byte(`"id":0,"id":0`), 1),
		"escaped-duplicate": bytes.Replace(valid, []byte(`"id":0`), []byte(`"id":0,"\u0069d":0`), 1),
		"missing":           bytes.Replace(valid, []byte(`,"args":[]`), nil, 1),
		"unknown":           bytes.Replace(valid, []byte(`"id":0`), []byte(`"id":0,"extra":1`), 1),
		"case-folded":       bytes.Replace(valid, []byte(`"id":0`), []byte(`"ID":0`), 1),
		"null":              bytes.Replace(valid, []byte(`"declared":0`), []byte(`"declared":null`), 1),
		"null-args":         bytes.Replace(valid, []byte(`"args":[]`), []byte(`"args":null`), 1),
		"negative-uint64":   bytes.Replace(valid, []byte("18446744073709551615"), []byte("-1"), 1),
		"overflow-uint64":   bytes.Replace(valid, []byte("18446744073709551615"), []byte("18446744073709551616"), 1),
		"fraction":          bytes.Replace(valid, []byte("18446744073709551615"), []byte("1.5"), 1),
		"exponent":          bytes.Replace(valid, []byte("18446744073709551615"), []byte("1e3"), 1),
		"quoted-number":     bytes.Replace(valid, []byte("18446744073709551615"), []byte(`"1"`), 1),
		"invalid-utf8":      bytes.Replace(valid, []byte(`"name":""`), []byte{'"', 'n', 'a', 'm', 'e', '"', ':', '"', 0xff, '"'}, 1),
		"trailing-object":   append(append([]byte{}, valid...), []byte(" {}")...),
		"trailing-junk":     append(append([]byte{}, valid...), 'x'),
		"not-object":        []byte("[]"),
		"cap":               bytes.Repeat([]byte{' '}, 4097),
	}
	for name, data := range cases {
		t.Run(name, func(t *testing.T) {
			if _, err := typedFixtureDecodeNode(data); err == nil {
				t.Fatal("malformed node accepted")
			}
		})
	}
}

func TestTypedCNFFixtureManifestBoundaries(t *testing.T) {
	data, err := os.ReadFile(filepath.Join(typedFixtureDirectory, "fixture.json"))
	if err != nil {
		t.Fatal(err)
	}
	if err := typedFixtureManifest(data); err != nil {
		t.Fatal(err)
	}
	cases := map[string][]byte{
		"format":                bytes.Replace(data, []byte(typedFixtureFormat), []byte("unrecognized"), 1),
		"profile":               bytes.Replace(data, []byte(typedFixtureProfile), []byte("conjoined-domain"), 1),
		"root":                  bytes.Replace(data, []byte(`"premise": 104`), []byte(`"premise": 105`), 1),
		"duplicate-root":        bytes.Replace(data, []byte(`"premise": 104`), []byte(`"premise": 104, "premise": 104`), 1),
		"missing-root":          bytes.Replace(data, []byte(`"premise": 104,`), nil, 1),
		"unknown-root":          bytes.Replace(data, []byte(`"premise": 104`), []byte(`"premise": 104, "domain": 0`), 1),
		"duplicate-declaration": bytes.Replace(data, []byte("le.bytes_at"), []byte("ew[?]"), 1),
		"declaration-width":     bytes.Replace(data, []byte(`"width": 1`), []byte(`"width": 32`), 1),
		"declaration-field":     bytes.Replace(data, []byte(`"name": "signed"`), []byte(`"name": "signed", "noise": 0`), 1),
		"cnf-identity":          bytes.Replace(data, []byte(typedFixtureCNFSHA256), []byte(strings.Repeat("0", 64)), 1),
		"proof-identity":        bytes.Replace(data, []byte(typedFixtureProofSHA256), []byte(strings.Repeat("0", 64)), 1),
	}
	for name, bad := range cases {
		t.Run(name, func(t *testing.T) {
			if bytes.Equal(data, bad) {
				t.Fatal("boundary mutation did not change the manifest")
			}
			if err := typedFixtureManifest(bad); err == nil {
				t.Fatal("malformed manifest accepted")
			}
		})
	}
}

func TestTypedCNFFixtureGraphBoundaries(t *testing.T) {
	data, err := os.ReadFile(filepath.Join(typedFixtureDirectory, "nodes.jsonl"))
	if err != nil {
		t.Fatal(err)
	}
	graph, err := typedFixtureGraph(data)
	if err != nil {
		t.Fatal(err)
	}
	if graph.nodes[0] == graph.nodes[9] {
		t.Fatal("distinct identical leaf identities were not preserved")
	}
	for _, id := range []int{0, 9} {
		node := graph.nodes[id]
		if node.kind != termParam || node.width != 32 || node.declared != 32 || node.name != "width" || node.op != "" || node.value != 0 || node.cond != nil || node.left != nil || node.right != nil {
			t.Fatal("identical leaf syntax changed")
		}
	}
	seen := map[*term]bool{}
	for _, node := range graph.nodes {
		if seen[node] {
			t.Fatal("fixture records share a term pointer")
		}
		seen[node] = true
	}
	mutate := func(id int, edit func(*typedFixtureNode)) []byte {
		lines := bytes.Split(bytes.TrimSuffix(data, []byte{'\n'}), []byte{'\n'})
		node, err := typedFixtureDecodeNode(lines[id])
		if err != nil {
			t.Fatal(err)
		}
		edit(&node)
		lines[id], err = json.Marshal(node)
		if err != nil {
			t.Fatal(err)
		}
		return append(bytes.Join(lines, []byte{'\n'}), '\n')
	}
	cases := map[string][]byte{
		"self-cycle":        mutate(0, func(n *typedFixtureNode) { n.Left = 0 }),
		"forward-edge":      mutate(0, func(n *typedFixtureNode) { n.Left = 1 }),
		"bad-absent-edge":   mutate(0, func(n *typedFixtureNode) { n.Left = -2 }),
		"duplicate-id":      mutate(1, func(n *typedFixtureNode) { n.ID = 0 }),
		"bad-kind":          mutate(0, func(n *typedFixtureNode) { n.Kind = 6 }),
		"zero-width":        mutate(0, func(n *typedFixtureNode) { n.Width = 0 }),
		"declaration-width": mutate(0, func(n *typedFixtureNode) { n.Declared = 31 }),
		"declaration-name":  mutate(0, func(n *typedFixtureNode) { n.Name = "unknown" }),
		"args":              mutate(0, func(n *typedFixtureNode) { n.Args = []int{0} }),
		"unreachable": mutate(371, func(n *typedFixtureNode) {
			*n = typedFixtureNode{ID: 371, Kind: int(termConst), Width: 32, Cond: -1, Left: -1, Right: -1, Args: []int{}}
		}),
		"out-of-width-constant": mutate(1, func(n *typedFixtureNode) { n.Value = 1 << 32 }),
		"extra-node":            append(append([]byte{}, data...), []byte("{}\n")...),
		"missing-newline":       append([]byte{}, data[:len(data)-1]...),
	}
	for name, bad := range cases {
		t.Run(name, func(t *testing.T) {
			if _, err := typedFixtureGraph(bad); err == nil {
				t.Fatal("malformed graph accepted")
			}
		})
	}
}

func TestTypedCNFFixtureFileBoundaries(t *testing.T) {
	if _, err := loadTypedCNFFixture(filepath.Join(t.TempDir(), "absent")); err == nil {
		t.Fatal("missing fixture accepted")
	}
	directory := t.TempDir()
	path := filepath.Join(directory, "input")
	if err := os.WriteFile(path, []byte("abc"), 0600); err != nil {
		t.Fatal(err)
	}
	for _, bad := range []struct {
		cap  int64
		size int
		sha  string
	}{
		{2, 3, tcSHA([]byte("abc"))},
		{3, 2, tcSHA([]byte("abc"))},
		{3, 3, tcSHA([]byte("abd"))},
	} {
		if _, err := typedFixtureRead(directory, "input", bad.cap, bad.size, bad.sha); err == nil {
			t.Fatal("invalid file bound accepted")
		}
	}
	if _, err := typedFixtureRead(directory, "input", 3, 3, tcSHA([]byte("abc"))); err != nil {
		t.Fatal(err)
	}
	if err := os.Mkdir(filepath.Join(directory, "subdirectory"), 0700); err != nil {
		t.Fatal(err)
	}
	if _, err := typedFixtureRead(directory, "subdirectory", 1<<20, 3, ""); err == nil {
		t.Fatal("directory accepted as fixture file")
	}
}

func TestTypedCNFFixtureIdentityBoundaries(t *testing.T) {
	directory := t.TempDir()
	names := []string{"fixture.json", "nodes.jsonl", "raw.cnf", "raw.lrat"}
	for _, name := range names {
		data, err := os.ReadFile(filepath.Join(typedFixtureDirectory, name))
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(directory, name), data, 0600); err != nil {
			t.Fatal(err)
		}
	}
	if _, err := loadTypedCNFFixture(directory); err != nil {
		t.Fatal(err)
	}
	for _, name := range names {
		t.Run(name, func(t *testing.T) {
			path := filepath.Join(directory, name)
			data, err := os.ReadFile(path)
			if err != nil {
				t.Fatal(err)
			}
			bad := append([]byte{}, data...)
			switch name {
			case "fixture.json":
				// Same meaning and size: authentication must still fail.
				bad[bytes.IndexByte(bad, ' ')] = '\t'
			case "nodes.jsonl":
				// Both are allowed operators; topology and inventory stay valid.
				bad = bytes.Replace(bad, []byte(`"op":"ne"`), []byte(`"op":"eq"`), 1)
			default:
				bad[0] ^= 1
			}
			if bytes.Equal(data, bad) || len(data) != len(bad) {
				t.Fatal("identity mutation must preserve size and change bytes")
			}
			if err := os.WriteFile(path, bad, 0600); err != nil {
				t.Fatal(err)
			}
			_, loadErr := loadTypedCNFFixture(directory)
			if err := os.WriteFile(path, data, 0600); err != nil {
				t.Fatal(err)
			}
			if loadErr == nil {
				t.Fatal("changed fixture identity accepted")
			}
		})
	}
}

func TestTypedCNFFixtureCancellation(t *testing.T) {
	fixture, err := loadTypedCNFFixture(typedFixtureDirectory)
	if err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithCancel(t.Context())
	cancel()
	audit, err := checkTypedCNFFixture(ctx, fixture)
	if !errors.Is(err, context.Canceled) || audit.snapshot != nil || audit.Nodes != 0 {
		t.Fatalf("cancellation conferred a result: nodes=%d error=%v", audit.Nodes, err)
	}
}

func TestTypedCNFInstanceWriterBoundaries(t *testing.T) {
	w := &typedInstanceWriter{directory: t.TempDir()}
	for _, name := range []string{"../outside.lean", "sub/Outside.lean", "NotLean.txt"} {
		if err := w.save(name, ""); err == nil {
			t.Fatal("invalid source path accepted")
		}
	}
	w.bytes = typedFixtureSourceCap - 1
	if err := w.save("Over.lean", "ab"); err == nil {
		t.Fatal("aggregate source cap ignored")
	}
	w.bytes = 0
	if err := w.save("One.lean", "-- bounded source\n"); err != nil {
		t.Fatal(err)
	}
	before := w.bytes
	if err := w.save("One.lean", "replacement"); err == nil || w.bytes != before || len(w.files) != 1 {
		t.Fatal("existing source overwritten or failed write counted")
	}
	if err := w.complete(); err == nil {
		t.Fatal("partial source inventory accepted")
	}
}
