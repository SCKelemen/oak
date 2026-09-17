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
		"old profile":      func(m *Module) { m.Profile = "oak.wasm.scalar.v0" },
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

func TestWasmDivisionEffects(t *testing.T) {
	for _, typ := range []optir.Type{"u32", "i32", "u64", "i64"} {
		for _, code := range []string{optir.OpIntDiv, optir.OpIntRem} {
			makeCFG := func() optir.CFG {
				return optir.CFG{Name: "f", Entry: 1, Results: []optir.Type{typ}, Blocks: []optir.Block{{
					ID: 1, Parameters: []optir.Value{{ID: 1, Type: typ}, {ID: 2, Type: typ}},
					Operations: []optir.Operation{{Code: code, Results: []optir.Value{{ID: 3, Type: typ}},
						Operands: []optir.ValueID{1, 2}, Effects: []optir.Effect{optir.EffectTrap}}},
					Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{3}},
				}}}
			}
			if _, err := Emit([]optir.CFG{makeCFG()}); err != nil {
				t.Fatal(typ, code, err)
			}
			for name, mutate := range map[string]func(*optir.Operation){
				"missing trap":   func(op *optir.Operation) { op.Effects = nil },
				"memory":         func(op *optir.Operation) { op.Effects = []optir.Effect{optir.EffectReadMemory} },
				"extra effect":   func(op *optir.Operation) { op.Effects = append(op.Effects, optir.EffectAllocate) },
				"duplicate trap": func(op *optir.Operation) { op.Effects = append(op.Effects, optir.EffectTrap) },
				"attribute":      func(op *optir.Operation) { op.Attributes = []optir.Attribute{{Name: "no-trap", Value: "true"}} },
				"authority":      func(op *optir.Operation) { op.MemoryAccessID = "forged" },
				"arity":          func(op *optir.Operation) { op.Operands = op.Operands[:1] },
				"result type":    func(op *optir.Operation) { op.Results[0].Type = "Bool" },
			} {
				t.Run(string(typ)+"/"+code+"/"+name, func(t *testing.T) {
					cfg := makeCFG()
					mutate(&cfg.Blocks[0].Operations[0])
					if m, err := Emit([]optir.CFG{cfg}); err == nil || len(m.Bytes) != 0 || m.ByteValidation != nil {
						t.Fatal("malformed division emitted", err)
					}
				})
			}
		}
	}
}

func TestWasmSingleBlockBackedgeKeepsDispatcher(t *testing.T) {
	// Block count alone is not enough: this function never returns. Do not run
	// it in-process; pin the dispatcher body, including the parallel edge copy.
	cfg := optir.CFG{Name: "spin", Entry: 9, Results: []optir.Type{"u32"}, Blocks: []optir.Block{{
		ID: 9, Parameters: []optir.Value{{ID: 1, Type: "u32"}},
		Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 9, Arguments: []optir.ValueID{1}}},
	}}}
	m, err := Emit([]optir.CFG{cfg})
	if err != nil {
		t.Fatal(err)
	}
	body := []byte{1, 1, 0x7f, 0x41, 0, 0x21, 1, 0x03, 0x40, 0x20, 1, 0x41, 0, 0x46, 0x04, 0x40,
		0x20, 0, 0x21, 0, 0x41, 0, 0x21, 1, 0x0c, 1, 0x0b, 0, 0x0b, 0, 0x0b}
	if !bytes.HasSuffix(m.Bytes, body) {
		t.Fatalf("one-block backedge changed: %x", m.Bytes)
	}
}
