package wasm

import (
	"context"
	"encoding/base64"
	"encoding/json"
	"testing"
	"time"

	"github.com/SCKelemen/oak/internal/wasmtest"
	"github.com/SCKelemen/oak/optir"
)

// The backedge swaps the HEADER parameters themselves. Sequential stores would
// corrupt this cycle; source-projected loops often hide it behind body params.
func loopTestCFG() optir.CFG {
	v := func(id optir.ValueID) optir.Value { return optir.Value{ID: id, Type: "u32"} }
	constant := func(id optir.ValueID, value string) optir.Operation {
		return optir.Operation{Code: optir.OpConstInt, Results: []optir.Value{v(id)}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: value}}}
	}
	binary := func(code string, id, x, y optir.ValueID) optir.Operation {
		return optir.Operation{Code: code, Results: []optir.Value{v(id)}, Operands: []optir.ValueID{x, y}}
	}
	return optir.CFG{Name: "swap", Entry: 10, Results: []optir.Type{"u32"}, Blocks: []optir.Block{
		{ID: 10, Parameters: []optir.Value{v(1), {ID: 16, Type: "Bool"}},
			Operations: []optir.Operation{constant(2, "0"), constant(3, "1"), constant(4, "2")},
			Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 20, Arguments: []optir.ValueID{2, 3, 4}}}},
		{ID: 20, Parameters: []optir.Value{v(5), v(6), v(7)},
			Operations: []optir.Operation{{Code: optir.OpLess, Results: []optir.Value{{ID: 8, Type: "Bool"}}, Operands: []optir.ValueID{5, 1}}},
			Terminator: optir.Terminator{Kind: optir.TerminatorCondBranch, Condition: 8, True: optir.Edge{Target: 30}, False: optir.Edge{Target: 40, Arguments: []optir.ValueID{6, 7}}}},
		{ID: 30, Operations: []optir.Operation{constant(9, "1"), binary(optir.OpIntAdd, 10, 5, 9)},
			Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 20, Arguments: []optir.ValueID{10, 7, 6}}}},
		{ID: 40, Parameters: []optir.Value{v(11), v(12)},
			Operations: []optir.Operation{constant(13, "10"), binary(optir.OpIntMul, 14, 11, 13), binary(optir.OpIntAdd, 15, 14, 12)},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{15}}},
	}}
}

func loopTestFunction(cfg optir.CFG) *function {
	f := &function{cfg: cfg, blocks: map[optir.BlockID]int{}}
	for i, b := range cfg.Blocks {
		f.blocks[b.ID] = i
		if b.ID == cfg.Entry {
			f.entry = b
		}
	}
	return f
}

func TestWasmLoopShape(t *testing.T) {
	for name, mutate := range map[string]func(*optir.CFG){
		"extra block":            func(c *optir.CFG) { c.Blocks = append(c.Blocks, optir.Block{ID: 50}) },
		"entry return":           func(c *optir.CFG) { c.Blocks[0].Terminator.Kind = optir.TerminatorReturn },
		"missing header":         func(c *optir.CFG) { c.Blocks[0].Terminator.True.Target = 999 },
		"header not conditional": func(c *optir.CFG) { c.Blocks[1].Terminator.Kind = optir.TerminatorBranch },
		"shared arms":            func(c *optir.CFG) { c.Blocks[1].Terminator.False.Target = 30 },
		"missing arm":            func(c *optir.CFG) { c.Blocks[1].Terminator.True.Target = 999 },
		"entry as arm":           func(c *optir.CFG) { c.Blocks[1].Terminator.True.Target = 10 },
		"header as arm":          func(c *optir.CFG) { c.Blocks[1].Terminator.True.Target = 20 },
		"break":                  func(c *optir.CFG) { c.Blocks[2].Terminator.True.Target = 40 },
		"self loop":              func(c *optir.CFG) { c.Blocks[2].Terminator.True.Target = 30 },
		"body conditional":       func(c *optir.CFG) { c.Blocks[2].Terminator.Kind = optir.TerminatorCondBranch },
		"two returns":            func(c *optir.CFG) { c.Blocks[2].Terminator.Kind = optir.TerminatorReturn },
		"exit not return":        func(c *optir.CFG) { c.Blocks[3].Terminator.Kind = optir.TerminatorBranch },
	} {
		t.Run(name, func(t *testing.T) {
			cfg := loopTestCFG()
			mutate(&cfg)
			if _, ok := loopTestFunction(cfg).matchLoop(); ok {
				t.Fatal("over-broad structured-loop match")
			}
		})
	}
	for _, block := range []int{0, 1, 2, 3} {
		cfg := loopTestCFG()
		cfg.Blocks[block].Operations[0].Effects = []optir.Effect{optir.EffectAllocate}
		if m, err := Emit([]optir.CFG{cfg}); err == nil || len(m.Bytes) != 0 {
			t.Fatal("structured loop bypassed operation admission", block, err)
		}
	}
}

func TestWasmLoopPolarityOrderAndPhiCycle(t *testing.T) {
	engine := wasmtest.Require(t)
	var encoded []string
	for _, inverted := range []bool{false, true} {
		for _, shuffled := range []bool{false, true} {
			cfg := loopTestCFG()
			if inverted {
				h := &cfg.Blocks[1]
				h.Operations[0].Code = optir.OpGreaterEqual
				h.Terminator.True, h.Terminator.False = h.Terminator.False, h.Terminator.True
			}
			if shuffled {
				cfg.Blocks = []optir.Block{cfg.Blocks[3], cfg.Blocks[2], cfg.Blocks[0], cfg.Blocks[1]}
			}
			if shape, ok := loopTestFunction(cfg).matchLoop(); !ok || shape.header.ID != 20 || shape.body.ID != 30 || shape.exit.ID != 40 {
				t.Fatal("valid shape not recognized", inverted, shuffled)
			}
			m, err := Emit([]optir.CFG{cfg})
			if err != nil {
				t.Fatal(err)
			}
			encoded = append(encoded, base64.StdEncoding.EncodeToString(m.Bytes))
		}
	}
	data, err := json.Marshal(encoded)
	if err != nil {
		t.Fatal(err)
	}
	script := `
for(const encoded of JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1])){
  const bytes=Uint8Array.from(atob(encoded),c=>c.charCodeAt(0));
  const e=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports;
  for(let n=0;n<100;n++)for(const p of [0,1])if(e.swap(n,p)!==(n%2?21:12))throw Error("phi cycle/polarity/order corruption");
  let trapped=false;try{e.swap(0,2)}catch(err){if(!(err instanceof WebAssembly.RuntimeError))throw err;trapped=true}
  if(!trapped)throw Error("unused Bool guard skipped on zero-trip path");
}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(data)).CombinedOutput(); err != nil {
		t.Fatalf("loop shape engine: %v\n%s", err, out)
	}
}
