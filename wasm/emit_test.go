package wasm

import (
	"bytes"
	"testing"

	"github.com/SCKelemen/oak/optir"
)

func TestLEBEncoding(t *testing.T) {
	for _, tt := range []struct {
		v    int64
		want []byte
	}{
		{0, []byte{0}}, {63, []byte{63}}, {64, []byte{0xc0, 0}}, {-1, []byte{0x7f}},
		{-64, []byte{0x40}}, {-65, []byte{0xbf, 0x7f}},
		{-2147483648, []byte{0x80, 0x80, 0x80, 0x80, 0x78}},
		{9223372036854775807, []byte{0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0}},
		{-9223372036854775808, []byte{0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x7f}},
	} {
		var b binary
		b.s(tt.v)
		if !bytes.Equal(b, tt.want) {
			t.Fatalf("%d: %x want %x", tt.v, b, tt.want)
		}
	}
	var b binary
	b.u(624485)
	if !bytes.Equal(b, []byte{0xe5, 0x8e, 0x26}) {
		t.Fatal(b)
	}
}

func TestFailClosedCFG(t *testing.T) {
	makeCFG := func() optir.CFG {
		return optir.CFG{Name: "f", Entry: 1, Results: []optir.Type{"i32"}, Blocks: []optir.Block{{ID: 1, Operations: []optir.Operation{{Code: optir.OpConstInt, Results: []optir.Value{{ID: 1, Type: "i32"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "42"}}}}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}}}}}
	}
	for name, mutate := range map[string]func(*optir.CFG){
		"unknown opcode":    func(c *optir.CFG) { c.Blocks[0].Operations[0].Code = "unknown" },
		"wrong type":        func(c *optir.CFG) { c.Blocks[0].Operations[0].Results[0].Type = "Bool" },
		"missing SSA value": func(c *optir.CFG) { c.Blocks[0].Terminator.Values[0] = 9 },
		"missing entry":     func(c *optir.CFG) { c.Entry = 9 },
		"effect":            func(c *optir.CFG) { c.Blocks[0].Operations[0].Effects = []optir.Effect{optir.EffectAllocate} },
		"memory authority":  func(c *optir.CFG) { c.Blocks[0].Operations[0].MemoryAccessID = "forged" },
		"missing constant":  func(c *optir.CFG) { c.Blocks[0].Operations[0].Attributes = nil },
	} {
		t.Run(name, func(t *testing.T) {
			c := makeCFG()
			mutate(&c)
			m, err := Emit([]optir.CFG{c})
			if err == nil || len(m.Bytes) != 0 {
				t.Fatal("invalid CFG emitted", err)
			}
		})
	}
	c := makeCFG()
	if _, err := Emit([]optir.CFG{c, c}); err == nil {
		t.Fatal("duplicate name accepted")
	}
	if _, err := Emit(nil); err == nil {
		t.Fatal("empty module accepted")
	}
}

func TestWasmByteManifest(t *testing.T) {
	cfg := optir.CFG{Name: "f", Entry: 1, Results: []optir.Type{"i32"}, Blocks: []optir.Block{{ID: 1, Parameters: []optir.Value{{ID: 1, Type: "i32"}}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{1}}}}}
	makeModule := func() Module {
		t.Helper()
		m, err := Emit([]optir.CFG{cfg})
		if err != nil {
			t.Fatal(err)
		}
		return m
	}
	m := makeModule()
	if m.ByteValidation == nil || m.ByteValidation.SHA256 == "" || m.TranslationVerified {
		t.Fatal("missing byte evidence or false translation claim")
	}
	for name, mutate := range map[string]func(*Module){
		"bytes":            func(m *Module) { m.Bytes[0] = 1 },
		"name":             func(m *Module) { m.Exports[0].Name = "other" },
		"parameter width":  func(m *Module) { m.Exports[0].Parameters[0] = "u64" },
		"result width":     func(m *Module) { m.Exports[0].Result = "u64" },
		"result arity":     func(m *Module) { m.Exports[0].Result = "()" },
		"parameter arity":  func(m *Module) { m.Exports[0].Parameters = nil },
		"export arity":     func(m *Module) { m.Exports = nil },
		"profile":          func(m *Module) { m.Profile = "other" },
		"unlicensed proof": func(m *Module) { m.TranslationVerified = true },
	} {
		t.Run(name, func(t *testing.T) {
			m := makeModule()
			mutate(&m)
			if _, err := m.ValidateBytes(); err == nil {
				t.Fatal("stale or forged manifest accepted")
			}
		})
	}
	// The saved report is diagnostic, not authority. It cannot excuse bad bytes.
	m.ByteValidation.SHA256 = "forged"
	if r, err := m.ValidateBytes(); err != nil || r.SHA256 == "forged" {
		t.Fatal("relied on saved report", err)
	}
}
