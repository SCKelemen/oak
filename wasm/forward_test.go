package wasm

import (
	"context"
	"encoding/base64"
	"encoding/json"
	"math/rand"
	"testing"
	"time"

	"github.com/SCKelemen/oak/internal/wasmtest"
	"github.com/SCKelemen/oak/optir"
)

// Every true edge goes to the next block; false edges may skip ahead. Distinct
// edge arguments matter even when both edges have the same destination.
func forwardTestCFG(skips []int) optir.CFG {
	cfg := optir.CFG{Name: "forward", Entry: 100, Results: []optir.Type{"u32"}}
	for i := 0; i <= len(skips); i++ {
		a := optir.ValueID(1 + i*4)
		b := optir.Block{ID: optir.BlockID(100 + i*7), Parameters: []optir.Value{{ID: a, Type: "u32"}, {ID: a + 1, Type: "u32"}},
			Operations: []optir.Operation{
				{Code: optir.OpIntAdd, Results: []optir.Value{{ID: a + 2, Type: "u32"}}, Operands: []optir.ValueID{a, a + 1}},
				{Code: optir.OpLess, Results: []optir.Value{{ID: a + 3, Type: "Bool"}}, Operands: []optir.ValueID{a, a + 1}},
			}, Terminator: optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{a + 2}}}
		if i < len(skips) {
			b.Terminator = optir.Terminator{Kind: optir.TerminatorCondBranch, Condition: a + 3,
				True:  optir.Edge{Target: optir.BlockID(100 + (i+1)*7), Arguments: []optir.ValueID{a + 2, a + 1}},
				False: optir.Edge{Target: optir.BlockID(100 + skips[i]*7), Arguments: []optir.ValueID{a + 1, a + 2}}}
		}
		cfg.Blocks = append(cfg.Blocks, b)
	}
	return cfg
}

func TestWasmForwardGraphs(t *testing.T) {
	engine := wasmtest.Require(t)
	type fixture struct {
		Module string     `json:"module"`
		Cases  [][3]int64 `json:"cases"`
	}
	var fixtures []fixture
	random := rand.New(rand.NewSource(781))
	values := []uint32{0, 1, 7, 2147483647, 2147483648, 4294967295}
	for trial := 0; trial < 64; trial++ {
		n := 3 + random.Intn(10)
		skips := make([]int, n-1)
		for i := range skips {
			skips[i] = i + 1 + random.Intn(n-i-1)
		}
		cfg := forwardTestCFG(skips)
		// A branch can return before the shared tail. Both paths must remain
		// structurally reachable even though one execution omits the tail.
		early := trial%4 == 0
		if early {
			skips[0] = 2
			cfg = forwardTestCFG(skips)
			cfg.Blocks[1].Terminator = optir.Terminator{Kind: optir.TerminatorReturn, Values: []optir.ValueID{7}}
		}
		// With no change to execution, vary polarity and physical block order.
		if trial%2 == 0 {
			for i := range cfg.Blocks {
				b := &cfg.Blocks[i]
				if b.Terminator.Kind == optir.TerminatorCondBranch {
					b.Operations[1].Code = optir.OpGreaterEqual
					b.Terminator.True, b.Terminator.False = b.Terminator.False, b.Terminator.True
				}
			}
		}
		random.Shuffle(n, func(i, j int) { cfg.Blocks[i], cfg.Blocks[j] = cfg.Blocks[j], cfg.Blocks[i] })
		m, err := Emit([]optir.CFG{cfg})
		if err != nil {
			t.Fatalf("trial %d: %v", trial, err)
		}
		f := fixture{Module: base64.StdEncoding.EncodeToString(m.Bytes)}
		for _, x := range values {
			for _, y := range values {
				a, b, i := x, y, 0
				for i < n-1 && !(early && i == 1) {
					if a < b {
						a = a + b
						i++
					} else {
						a, b = b, a+b
						i = skips[i]
					}
				}
				f.Cases = append(f.Cases, [3]int64{int64(x), int64(y), int64(int32(a + b))})
			}
		}
		fixtures = append(fixtures, f)
	}
	data, err := json.Marshal(fixtures)
	if err != nil {
		t.Fatal(err)
	}
	script := `
for(const f of JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1])){
  const bytes=Uint8Array.from(atob(f.module),c=>c.charCodeAt(0));
  if(!WebAssembly.validate(bytes))throw Error("invalid forward bytes");
  const e=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports;
  for(const [x,y,want] of f.cases)if(e.forward(x,y)!==want)throw Error("forward execution mismatch");
}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(data)).CombinedOutput(); err != nil {
		t.Fatalf("forward graphs: %v\n%s", err, out)
	}
}

func TestWasmForwardAdmission(t *testing.T) {
	for i := 0; i < 6; i++ {
		cfg := forwardTestCFG([]int{3, 4, 5, 5, 5})
		cfg.Blocks[i].Operations[0].Effects = []optir.Effect{optir.EffectAllocate}
		if m, err := Emit([]optir.CFG{cfg}); err == nil || len(m.Bytes) != 0 {
			t.Fatal("forward bypassed effect admission", i, err)
		}
	}
	for _, selected := range []string{"true", "false"} {
		cfg := forwardTestCFG([]int{2, 2, 3})
		cfg.Blocks[0].Operations[1] = optir.Operation{Code: optir.OpConstBool, Results: []optir.Value{{ID: 4, Type: "Bool"}}, Attributes: []optir.Attribute{{Name: optir.AttributeValue, Value: selected}}}
		cfg.Blocks[1].Operations[0].Effects = []optir.Effect{optir.EffectAllocate}
		if m, err := Emit([]optir.CFG{cfg}); err == nil || len(m.Bytes) != 0 {
			t.Fatal("constant branch hid effect admission", err)
		}
	}
}

func TestWasmForwardDepthLimit(t *testing.T) {
	engine := wasmtest.Require(t)
	var modules []string
	for _, n := range []int{127, 128} {
		skips := make([]int, n-1)
		for i := range skips {
			skips[i] = i + 1
		}
		cfg := forwardTestCFG(skips)
		for i := range cfg.Blocks {
			b := &cfg.Blocks[i]
			for j := range b.Parameters {
				b.Parameters[j].Type = "i64"
			}
			b.Operations[0].Results[0].Type = "i64"
		}
		cfg.Results[0] = "i64"
		// An unused signed division adds an internal if at maximum nesting.
		cfg.Blocks[0].Operations = append(cfg.Blocks[0].Operations, optir.Operation{Code: optir.OpIntDiv, Results: []optir.Value{{ID: 10000, Type: "i64"}}, Operands: []optir.ValueID{1, 2}, Effects: []optir.Effect{optir.EffectTrap}})
		m, err := Emit([]optir.CFG{cfg})
		if err != nil {
			t.Fatal(n, err)
		}
		modules = append(modules, base64.StdEncoding.EncodeToString(m.Bytes))
		// Pin the route: the 128-block graph must keep the dispatcher. The
		// admitted 127-block graph must not silently retreat from this boundary.
		// Inspect the materialized body through the same private helper setup as
		// EncodeCandidate; byte admission above separately checks actual nesting.
		f := shapeTestFunction(cfg)
		f.locals = map[optir.ValueID]uint32{}
		f.types = map[optir.ValueID]optir.Type{}
		define := func(v optir.Value) {
			f.locals[v.ID] = uint32(len(f.localTypes))
			f.types[v.ID] = v.Type
			typ, _ := valueType(v.Type)
			f.localTypes = append(f.localTypes, typ)
		}
		for _, v := range f.entry.Parameters {
			define(v)
		}
		for _, b := range cfg.Blocks {
			for _, v := range b.Parameters {
				if _, ok := f.locals[v.ID]; !ok {
					define(v)
				}
			}
			for _, op := range b.Operations {
				define(op.Results[0])
			}
		}
		body, err := f.body(map[string]*function{"forward": f})
		if err != nil {
			t.Fatal("wrong control-depth fallback route", n, err)
		}
		at := 0
		readULEB := func() (uint64, bool) {
			var value uint64
			for shift := uint(0); shift < 35 && at < len(body); shift += 7 {
				c := body[at]
				at++
				value |= uint64(c&0x7f) << shift
				if c&0x80 == 0 {
					return value, true
				}
			}
			return 0, false
		}
		groups, ok := readULEB()
		for i := uint64(0); ok && i < groups; i++ {
			_, ok = readULEB()
			if ok && at < len(body) {
				at++ // value type
			} else {
				ok = false
			}
		}
		want := byte(0x02) // first nested forward block
		if n > maxForwardBlocks {
			want = 0x41 // dispatcher PC initialization
		}
		if !ok || at >= len(body) {
			t.Fatalf("wrong control-depth fallback route %d: malformed locals prefix", n)
		}
		if body[at] != want {
			t.Fatalf("wrong control-depth fallback route %d: first opcode %#x, want %#x", n, body[at], want)
		}
	}
	data, err := json.Marshal(modules)
	if err != nil {
		t.Fatal(err)
	}
	script := `
for(const [index,encoded] of JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]).entries()){
  const e=new WebAssembly.Instance(new WebAssembly.Module(Uint8Array.from(atob(encoded),c=>c.charCodeAt(0))),{}).exports;
  for(const [x,y] of [[1n,2n],[-9223372036854775808n,-1n]]){
    let a=x,b=y;
    for(let i=0;i<126+index;i++){const sum=BigInt.asIntN(64,a+b);if(a<b)a=sum;else [a,b]=[b,sum]}
    if(e.forward(x,y)!==BigInt.asIntN(64,a+b))throw Error("limit result mismatch");
  }
  let trapped=false;try{e.forward(1n,0n)}catch(err){if(!(err instanceof WebAssembly.RuntimeError))throw err;trapped=true}
  if(!trapped)throw Error("lost unused division trap");
}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(data)).CombinedOutput(); err != nil {
		t.Fatalf("forward limits: %v\n%s", err, out)
	}
}
