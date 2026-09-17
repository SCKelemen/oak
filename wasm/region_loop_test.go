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

func regionLoopTestCFG(mode string) optir.CFG {
	cfg := loopTestCFG()
	cfg.Blocks[0].Parameters = append(cfg.Blocks[0].Parameters, optir.Value{ID: 18, Type: "Bool"}) // unused guard
	body := &cfg.Blocks[2]
	body.Terminator = optir.Terminator{Kind: optir.TerminatorCondBranch, Condition: 16,
		True: optir.Edge{Target: 20, Arguments: []optir.ValueID{10, 7, 6}}, False: optir.Edge{Target: 50}}
	last := optir.Block{ID: 50, Operations: []optir.Operation{{Code: optir.OpCopy, Results: []optir.Value{{ID: 17, Type: "u32"}}, Operands: []optir.ValueID{6}}},
		Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 20, Arguments: []optir.ValueID{10, 17, 7}}}}
	switch mode {
	case "break":
		last.Terminator = optir.Terminator{Kind: optir.TerminatorCondBranch, Condition: 16,
			True: last.Terminator.True, False: optir.Edge{Target: 40, Arguments: []optir.ValueID{7, 17}}}
	case "return":
		last.Terminator = optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{17}}
	case "cycle":
		last.Terminator.True = optir.Edge{Target: 50}
	}
	cfg.Blocks = append(cfg.Blocks, last)
	return cfg
}

func TestWasmRegionLoopShapeAndAdmission(t *testing.T) {
	for _, mode := range []string{"latches", "break", "return", "cycle"} {
		cfg := regionLoopTestCFG(mode)
		shape, ok, err := shapeTestFunction(cfg).matchRegionLoop()
		if err != nil || ok != (mode != "cycle") {
			t.Fatal(mode, shape, ok, err)
		}
		if ok && (len(shape.body) != 2 || shape.header.ID != 20 || shape.exit.ID != 40) {
			t.Fatal("incorrect region coverage", shape)
		}
		if _, err := Emit([]optir.CFG{cfg}); err != nil {
			t.Fatal(mode, err)
		}
	}
	for _, mutate := range []func(*optir.CFG){
		func(c *optir.CFG) { c.Blocks[0].Terminator.Kind = optir.TerminatorReturn },
		func(c *optir.CFG) { c.Blocks[1].Terminator.False = c.Blocks[1].Terminator.True },
		func(c *optir.CFG) {
			c.Blocks[3].Terminator = optir.Terminator{Kind: optir.TerminatorBranch, True: optir.Edge{Target: 10}}
		},
		func(c *optir.CFG) { c.Blocks[4].Terminator.True = optir.Edge{Target: 10} },
		func(c *optir.CFG) { c.Blocks = append(c.Blocks, optir.Block{ID: 99}) },
	} {
		cfg := regionLoopTestCFG("latches")
		mutate(&cfg)
		if _, ok, _ := shapeTestFunction(cfg).matchRegionLoop(); ok {
			t.Fatal("over-broad region-loop match")
		}
	}
	for i := 0; i < 5; i++ {
		cfg := regionLoopTestCFG("latches")
		cfg.Blocks[i].Operations[0].Effects = []optir.Effect{optir.EffectAllocate}
		if m, err := Emit([]optir.CFG{cfg}); err == nil || len(m.Bytes) != 0 {
			t.Fatal("region omitted effect admission", i, err)
		}
	}
	// Constant-false header cannot hide an unsupported body operation.
	cfg := regionLoopTestCFG("latches")
	cfg.Blocks[1].Operations[0] = optir.Operation{Code: optir.OpConstBool, Results: []optir.Value{{ID: 8, Type: "Bool"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: "false"}}}
	cfg.Blocks[4].Operations[0].Effects = []optir.Effect{optir.EffectAllocate}
	if m, err := Emit([]optir.CFG{cfg}); err == nil || len(m.Bytes) != 0 {
		t.Fatal("zero-trip prediction omitted effect admission", err)
	}
}

func TestWasmRegionLoopExecution(t *testing.T) {
	engine := wasmtest.Require(t)
	type fixture struct {
		Mode   string `json:"mode"`
		Module string `json:"module"`
	}
	var fixtures []fixture
	for _, mode := range []string{"latches", "break", "return", "cycle"} {
		for _, inverted := range []bool{false, true} {
			for _, shuffled := range []bool{false, true} {
				cfg := regionLoopTestCFG(mode)
				if inverted {
					h := &cfg.Blocks[1]
					h.Operations[0].Code = optir.OpGreaterEqual
					h.Terminator.True, h.Terminator.False = h.Terminator.False, h.Terminator.True
				}
				if shuffled {
					cfg.Blocks = []optir.Block{cfg.Blocks[4], cfg.Blocks[3], cfg.Blocks[2], cfg.Blocks[0], cfg.Blocks[1]}
				}
				m, err := Emit([]optir.CFG{cfg})
				if err != nil {
					t.Fatal(mode, err)
				}
				fixtures = append(fixtures, fixture{mode, base64.StdEncoding.EncodeToString(m.Bytes)})
			}
		}
	}
	data, err := json.Marshal(fixtures)
	if err != nil {
		t.Fatal(err)
	}
	script := `
for(const f of JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1])){
  const e=new WebAssembly.Instance(new WebAssembly.Module(Uint8Array.from(atob(f.module),c=>c.charCodeAt(0))),{}).exports;
  for(let n=0;n<100;n++)for(const p of [0,1])for(const unused of [0,1]){
    if(f.mode==="cycle"&&n>0&&!p)continue;
    const want=n===0?12:p?(n%2?21:12):f.mode==="break"?21:f.mode==="return"?1:12;
    if(e.swap(n,p,unused)!==want)throw Error("region phi/polarity/exit mismatch "+f.mode);
  }
  for(const args of [[0,0,2],[0,2,0],[1,1,-1]]){
    let trapped=false;try{e.swap(...args)}catch(err){if(!(err instanceof WebAssembly.RuntimeError))throw err;trapped=true}
    if(!trapped)throw Error("lost Bool guard");
  }
}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(data)).CombinedOutput(); err != nil {
		t.Fatalf("region loop: %v\n%s", err, out)
	}
}

func TestWasmRegionLoopDepthLimit(t *testing.T) {
	engine := wasmtest.Require(t)
	var modules []string
	for _, size := range []int{124, 125} {
		cfg := loopTestCFG()
		cfg.Blocks[0].Parameters = append(cfg.Blocks[0].Parameters, optir.Value{ID: 18, Type: "Bool"}, optir.Value{ID: 19, Type: "i64"}, optir.Value{ID: 20, Type: "i64"})
		body := &cfg.Blocks[2]
		body.Operations = append(body.Operations, optir.Operation{Code: optir.OpIntDiv, Results: []optir.Value{{ID: 10000, Type: "i64"}}, Operands: []optir.ValueID{19, 20}, Effects: []optir.Effect{optir.EffectTrap}})
		body.Terminator = optir.Terminator{Kind: optir.TerminatorCondBranch, Condition: 16,
			True: optir.Edge{Target: 20, Arguments: []optir.ValueID{10, 7, 6}}, False: optir.Edge{Target: 1000}}
		for i := 0; i < size-1; i++ {
			edge := optir.Edge{Target: optir.BlockID(1001 + i)}
			if i == size-2 {
				edge = optir.Edge{Target: 20, Arguments: []optir.ValueID{10, 6, 7}}
			}
			cfg.Blocks = append(cfg.Blocks, optir.Block{ID: optir.BlockID(1000 + i), Terminator: optir.Terminator{Kind: optir.TerminatorBranch, True: edge}})
		}
		if shape, ok, err := shapeTestFunction(cfg).matchRegionLoop(); err != nil || ok != (size == 124) || ok && len(shape.body) != size {
			t.Fatal("depth-limit route", size, shape, ok, err)
		}
		m, err := Emit([]optir.CFG{cfg})
		if err != nil {
			t.Fatal(size, err)
		}
		modules = append(modules, base64.StdEncoding.EncodeToString(m.Bytes))
	}
	data, err := json.Marshal(modules)
	if err != nil {
		t.Fatal(err)
	}
	script := `
for(const encoded of JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1])){
  const e=new WebAssembly.Instance(new WebAssembly.Module(Uint8Array.from(atob(encoded),c=>c.charCodeAt(0))),{}).exports;
  function trap(f){try{f()}catch(err){if(err instanceof WebAssembly.RuntimeError)return;throw err}throw Error("lost region-depth trap")}
  for(const p of [0,1]){
    if(e.swap(0,p,0,1n,0n)!==12)throw Error("zero-trip body executed");
    for(const n of [1,2,3,100])if(e.swap(n,p,1,-9223372036854775808n,-1n)!==(p&&n%2?21:12))throw Error("region-depth result mismatch");
    trap(()=>e.swap(1,p,0,1n,0n));trap(()=>e.swap(0,p,2,1n,1n));
  }
}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(data)).CombinedOutput(); err != nil {
		t.Fatalf("region depth: %v\n%s", err, out)
	}
}
