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

func diamondTestCFG() optir.CFG {
	v := func(id optir.ValueID) optir.Value { return optir.Value{ID: id, Type: "u32"} }
	constant := func(id optir.ValueID, value string) optir.Operation {
		return optir.Operation{Code: optir.OpConstInt, Results: []optir.Value{v(id)}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: value}}}
	}
	binary := func(code string, id, x, y optir.ValueID) optir.Operation {
		return optir.Operation{Code: code, Results: []optir.Value{v(id)}, Operands: []optir.ValueID{x, y}}
	}
	return optir.CFG{Name: "choose", Entry: 10, Results: []optir.Type{"u32"}, Blocks: []optir.Block{
		{ID: 10, Parameters: []optir.Value{{ID: 1, Type: "Bool"}, v(2), v(3), {ID: 4, Type: "Bool"}},
			Operations: []optir.Operation{{Code: optir.OpCopy, Results: []optir.Value{{ID: 5, Type: "Bool"}}, Operands: []optir.ValueID{1}}},
			Terminator: optir.Terminator{Kind: optir.TerminatorCondBranch, Condition: 5, True: optir.Edge{Target: 20, Arguments: []optir.ValueID{2, 3}}, False: optir.Edge{Target: 30, Arguments: []optir.ValueID{3, 2}}}},
		{ID: 20, Parameters: []optir.Value{v(6), v(7)}, Operations: []optir.Operation{constant(8, "1"), binary(optir.OpIntAdd, 9, 6, 8)},
			Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 40, Arguments: []optir.ValueID{9, 7}}}},
		{ID: 30, Parameters: []optir.Value{v(10), v(11)}, Operations: []optir.Operation{constant(12, "2"), binary(optir.OpIntAdd, 13, 10, 12)},
			Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 40, Arguments: []optir.ValueID{11, 13}}}},
		{ID: 40, Parameters: []optir.Value{v(14), v(15)}, Operations: []optir.Operation{constant(16, "10"), binary(optir.OpIntMul, 17, 14, 16), binary(optir.OpIntAdd, 18, 17, 15)},
			Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{18}}},
	}}
}

func TestWasmDiamondShape(t *testing.T) {
	for name, mutate := range map[string]func(*optir.CFG){
		"extra block":     func(c *optir.CFG) { c.Blocks = append(c.Blocks, optir.Block{ID: 50}) },
		"entry branch":    func(c *optir.CFG) { c.Blocks[0].Terminator.Kind = optir.TerminatorBranch },
		"missing arm":     func(c *optir.CFG) { c.Blocks[0].Terminator.True.Target = 999 },
		"shared arms":     func(c *optir.CFG) { c.Blocks[0].Terminator.False = c.Blocks[0].Terminator.True },
		"returning arm":   func(c *optir.CFG) { c.Blocks[1].Terminator.Kind = optir.TerminatorReturn },
		"conditional arm": func(c *optir.CFG) { c.Blocks[2].Terminator.Kind = optir.TerminatorCondBranch },
		"cross edge":      func(c *optir.CFG) { c.Blocks[1].Terminator.True.Target = 30 },
		"backedge":        func(c *optir.CFG) { c.Blocks[2].Terminator.True.Target = 10 },
		"shared backedge": func(c *optir.CFG) { c.Blocks[1].Terminator.True.Target = 10; c.Blocks[2].Terminator.True.Target = 10 },
		"missing merge":   func(c *optir.CFG) { c.Blocks[1].Terminator.True.Target = 999; c.Blocks[2].Terminator.True.Target = 999 },
		"merge branch":    func(c *optir.CFG) { c.Blocks[3].Terminator.Kind = optir.TerminatorBranch },
	} {
		t.Run(name, func(t *testing.T) {
			cfg := diamondTestCFG()
			mutate(&cfg)
			if _, ok := shapeTestFunction(cfg).matchDiamond(); ok {
				t.Fatal("over-broad diamond match")
			}
		})
	}
	for i := 0; i < 4; i++ {
		cfg := diamondTestCFG()
		cfg.Blocks[i].Operations[0].Effects = []optir.Effect{optir.EffectAllocate}
		if m, err := Emit([]optir.CFG{cfg}); err == nil || len(m.Bytes) != 0 {
			t.Fatal("diamond bypassed operation admission", i, err)
		}
	}
	// A constant selector cannot authorize omission of a malformed untaken arm.
	for _, selector := range []string{"true", "false"} {
		cfg := diamondTestCFG()
		cfg.Blocks[0].Operations[0] = optir.Operation{Code: optir.OpConstBool, Results: []optir.Value{{ID: 5, Type: "Bool"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: selector}}}
		untaken := 2
		if selector == "false" {
			untaken = 1
		}
		cfg.Blocks[untaken].Operations[0].Effects = []optir.Effect{optir.EffectAllocate}
		if m, err := Emit([]optir.CFG{cfg}); err == nil || len(m.Bytes) != 0 {
			t.Fatal("constant branch hid an unsupported effect", err)
		}
	}
}

func TestWasmDiamondPolarityOrderAndParameters(t *testing.T) {
	engine := wasmtest.Require(t)
	var encoded []string
	for _, inverted := range []bool{false, true} {
		for _, shuffled := range []bool{false, true} {
			cfg := diamondTestCFG()
			if inverted {
				cfg.Blocks[0].Operations[0].Code = optir.OpBoolNot
				e := &cfg.Blocks[0].Terminator
				e.True, e.False = e.False, e.True
			}
			if shuffled {
				cfg.Blocks = []optir.Block{cfg.Blocks[3], cfg.Blocks[2], cfg.Blocks[0], cfg.Blocks[1]}
			}
			if shape, ok := shapeTestFunction(cfg).matchDiamond(); !ok || shape.merge.ID != 40 {
				t.Fatal("valid diamond missed")
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
  const e=new WebAssembly.Instance(new WebAssembly.Module(Uint8Array.from(atob(encoded),c=>c.charCodeAt(0))),{}).exports;
  const values=[0,1,7,2147483647,2147483648,4294967295];
  for(const x of values)for(const y of values)for(const p of [0,1])for(const unused of [0,1]){
    const want=p?((x+1)*10+y)|0:(x*10+y+2)|0;
    if(e.choose(p,x,y,unused)!==want)throw Error("diamond edge copy/order/polarity corruption");
  }
  for(const args of [[2,0,0,0],[0,0,0,2],[1,0,0,-1]]){
    let trapped=false;try{e.choose(...args)}catch(err){if(!(err instanceof WebAssembly.RuntimeError))throw err;trapped=true}
    if(!trapped)throw Error("Bool guard lost");
  }
}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(data)).CombinedOutput(); err != nil {
		t.Fatalf("diamond shape engine: %v\n%s", err, out)
	}
}
