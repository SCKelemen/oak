package compiler

import (
	"context"
	"encoding/base64"
	"encoding/json"
	"os"
	"testing"
	"time"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/internal/wasmtest"
	"github.com/SCKelemen/oak/optir"
	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/wasm"
)

var wasmNestedLoopCases = []struct {
	name, source string
}{
	{"nested", "main: (n: u32): u32 { i: u32 = 0; total: u32 = 0; while i < n { j: u32 = 0; while j < i { total = total + u32(1); j = j + u32(1) }; i = i + u32(1) }; total }"},
	{"branch", "main: (n: u32): u32 { i: u32 = 0; total: u32 = 0; while i < n { j: u32 = 0; while j < i { total = total + ((j & u32(1)) == u32(0) ? u32(1) | u32(2)); j = j + u32(1) }; i = i + u32(1) }; total }"},
}

func rawWasmSourceProjection(t *testing.T, source string) wasm.Module {
	t.Helper()
	comp := New().WithSource("nested-loop.oak", source).WithTarget(target.Target{OS: target.OSCore, Arch: target.ArchWasm32})
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	planner := newOptIRCallEffectPlanner(model.Tree.Root, model.TypeChecker, nil)
	var cfgs []optir.CFG
	for _, statement := range model.Tree.Root.Statements {
		function, ok := statement.(*ast.FunctionStatement)
		if !ok {
			t.Fatalf("unexpected statement %T", statement)
		}
		checked, err := planner.lowerRoot(function)
		if err != nil {
			t.Fatal(err)
		}
		cfgs = append(cfgs, checked.cfg)
	}
	module, err := wasm.Emit(cfgs)
	if err != nil {
		t.Fatal(err)
	}
	return module
}

func wasmNestedLoopFixtures(t *testing.T) []byte {
	t.Helper()
	type fixture struct {
		Name       string `json:"name"`
		Dispatcher string `json:"dispatcher"`
		Structured string `json:"structured"`
	}
	var fixtures []fixture
	for _, test := range wasmNestedLoopCases {
		dispatcher := rawWasmSourceProjection(t, test.source)
		structured, err := New().WithSource("nested-loop.oak", test.source).EmitWasm().Get()
		if err != nil {
			t.Fatal(err)
		}
		if structured.ByteValidation == nil || dispatcher.ByteValidation == nil || structured.TranslationVerified {
			t.Fatal("nested-loop output bypassed byte-only admission")
		}
		if len(structured.Bytes) >= len(dispatcher.Bytes) || structured.ByteValidation.Instructions >= dispatcher.ByteValidation.Instructions {
			t.Fatalf("%s structured lowering did not improve dispatcher: bytes %d/%d, instructions %d/%d",
				test.name, len(structured.Bytes), len(dispatcher.Bytes), structured.ByteValidation.Instructions, dispatcher.ByteValidation.Instructions)
		}
		t.Logf("%s bytes %d -> %d; instructions %d -> %d", test.name, len(dispatcher.Bytes), len(structured.Bytes), dispatcher.ByteValidation.Instructions, structured.ByteValidation.Instructions)
		fixtures = append(fixtures, fixture{Name: test.name,
			Dispatcher: base64.StdEncoding.EncodeToString(dispatcher.Bytes), Structured: base64.StdEncoding.EncodeToString(structured.Bytes)})
	}
	data, err := json.Marshal(fixtures)
	if err != nil {
		t.Fatal(err)
	}
	return data
}

func TestWasmNestedLoopStructuredLowering(t *testing.T) {
	data := wasmNestedLoopFixtures(t)
	engine := wasmtest.Require(t)
	script := `
for(const f of JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1])){
  const load=s=>new WebAssembly.Instance(new WebAssembly.Module(Uint8Array.from(atob(s),c=>c.charCodeAt(0))),{}).exports.main;
  const old=load(f.dispatcher), current=load(f.structured);
  for(const n of [...Array(100).keys(),255,1024]){
    let want=0;
    for(let i=0;i<n;i++)for(let j=0;j<i;j++)want+=f.name==="branch"?(j%2?2:1):1;
    want|=0;
    if(old(n)!==want||current(n)!==want)throw Error(f.name+" nested-loop mismatch at "+n);
  }
}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(data)).CombinedOutput(); err != nil {
		t.Fatalf("nested structured/dispatcher execution: %v\n%s", err, out)
	}
}

func TestWasmNestedLoopTiming(t *testing.T) {
	if os.Getenv("OAK_WASM_BENCHMARKS") != "1" {
		t.Skip("opt-in engine timings; no noisy CI threshold")
	}
	engine := wasmtest.Require(t)
	script := `
const f=JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]).find(x=>x.name==="branch");
const load=s=>new WebAssembly.Instance(new WebAssembly.Module(Uint8Array.from(atob(s),c=>c.charCodeAt(0))),{}).exports.main;
const lanes=[load(f.dispatcher),load(f.structured)],samples=[[],[]],calls=4,n=1000;
const expected=x=>{let total=0;for(let i=0;i<x;i++)for(let j=0;j<i;j++)total+=j%2?2:1;return total|0};
function batch(lane,count){const want=expected(count);for(let j=0;j<calls;j++)if(lanes[lane](count)!==want)throw Error("timing result mismatch")}
for(let k=0;k<15;k++)for(let lane=0;lane<2;lane++)batch(lane,100);
for(let round=0;round<7;round++)for(const lane of round%2?[1,0]:[0,1]){
  const start=performance.now();batch(lane,n);samples[lane].push(performance.now()-start);
}
const median=a=>[...a].sort((a,b)=>a-b)[3];
console.log(JSON.stringify({engine:typeof Deno!=="undefined"?Deno.version:process.versions,
  warmup:"15 batches per lane, 4 calls per batch, n=100",callsPerSample:calls,n,
  dispatcher_ms:samples[0],structured_ms:samples[1],median_ratio:median(samples[1])/median(samples[0])}));
`
	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(wasmNestedLoopFixtures(t))).CombinedOutput(); err != nil {
		t.Fatalf("nested-loop timing: %v\n%s", err, out)
	} else {
		t.Log(string(out))
	}
}

func TestWasmNestedLoopEffectsAndLaziness(t *testing.T) {
	engine := wasmtest.Require(t)
	const source = `
divide: (d: u32): u32 = u32(12) / d
noop: (): () = {}
discard: (d: u32): () { unused: u32 = divide(d); noop() }
main: (n: u32, p: Bool, d: u32): u32 {
  i: u32 = 0
  total: u32 = 0
  while i < n {
    j: u32 = 0
    while j < i { total = total + (p ? divide(d) | u32(1)); j = j + u32(1) }
    i = i + u32(1)
  }
  total
}
unit: (n: u32, p: Bool, d: u32): () {
  i: u32 = 0
  while i < n {
    j: u32 = 0
    while j < i { unused: () = p ? discard(d) | noop(); j = j + u32(1) }
    i = i + u32(1)
  }
  noop()
}
`
	module, err := New().WithSource("nested-effects.oak", source).EmitWasm().Get()
	if err != nil {
		t.Fatal(err)
	}
	script := `
const bytes=Uint8Array.from(atob(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]),c=>c.charCodeAt(0));
const e=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports;
const equal=(a,b)=>{if(a!==b)throw Error(a+" != "+b)};
const trap=f=>{try{f()}catch(err){if(err instanceof WebAssembly.RuntimeError)return;throw err}throw Error("lost nested trap")};
for(const n of [0,1,2,3,10]){
  const iterations=n*(n-1)/2;
  equal(e.main(n,0,0),iterations);equal(e.unit(n,0,0),undefined);
  if(iterations){equal(e.main(n,1,3),4*iterations);equal(e.unit(n,1,3),undefined);trap(()=>e.main(n,1,0));trap(()=>e.unit(n,1,0))}
  else {equal(e.main(n,1,0),0);equal(e.unit(n,1,0),undefined)}
}
trap(()=>e.main(0,2,3));trap(()=>e.unit(0,-1,3));
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, base64.StdEncoding.EncodeToString(module.Bytes)).CombinedOutput(); err != nil {
		t.Fatalf("nested effects execution: %v\n%s", err, out)
	}
}
