package compiler

import (
	"context"
	"encoding/base64"
	"encoding/json"
	"os"
	"testing"
	"time"

	"github.com/SCKelemen/oak/internal/wasmtest"
)

// Dispatcher baseline captured at specification 4777fef6, before loop lowering.
var wasmLoopCases = []struct {
	name, source, beforeHex     string
	wantBytes, wantInstructions int
}{
	{"sum", "main: (n: u32): u32 { i: u32 = 0; total: u32 = 0; while i < n { total = total + i; i = i + u32(1) }; total }",
		"0061736d0100000001060160017f017f03020100070801046d61696e00000aaa0101a7010d017f017f017f017f017f017f017f017f017f017f017f017f017f4100210d0340200d4100460440410021014100210220012002210421034101210d0c010b200d4101460440200320004921052005044020032004210721064102210d0c020520032004210c210b4103210d0c020b0b200d4102460440200720066a210841012109200620096a210a200a2008210421034101210d0c010b200d4103460440200c0f0b000b000b", 140, 45},
	{"swap", "main: (n: u32): u32 { a: u32 = 1; b: u32 = 2; i: u32 = 0; while i < n { tmp: u32 = a; a = b; b = tmp; i = i + u32(1) }; a * u32(10) + b }",
		"0061736d0100000001060160017f017f03020100070801046d61696e00000ad50101d20113017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f41002113034020134100460440410121014102210241002103200120022003210621052104410121130c010b201341014604402006200049210720070440200420052006210a21092108410221130c0205200420052006210f210e210d410321130c020b0b201341024604404101210b200a200b6a210c20092008200c210621052104410121130c010b20134103460440410a2110200d20106c21112011200e6a211220120f0b000b000b", 185, 61},
	{"gcd", "main: (a: u64, b: u64): u64 { x: u64 = a; y: u64 = b; while y != u64(0) { next: u64 = x % y; x = y; y = next }; x }",
		"0061736d0100000001070160027e7e017e03020100070801046d61696e00000a95010192010a017e017e017e017f017e017e017e017e017e017f4100210b0340200b410046044020002001210321024101210b0c010b200b410146044042002104200320045221052005044020022003210721064102210b0c020520022003210a21094103210b0c020b0b200b41024604402006200782210820072008210321024101210b0c010b200b410346044020090f0b000b000b", 120, 37},
}

func wasmLoopModules(t *testing.T) []byte {
	t.Helper()
	modules := map[string][]string{}
	for _, tc := range wasmLoopCases {
		m, err := New().WithSource("loop.oak", tc.source).EmitWasm().Get()
		if err != nil {
			t.Fatal(err)
		}
		if m.ByteValidation == nil || m.TranslationVerified || len(m.Bytes) != tc.wantBytes || m.ByteValidation.Instructions != tc.wantInstructions {
			t.Fatalf("%s: unexpected bytes/admission/instruction count: %+v", tc.name, m)
		}
		before := wasmSizeBaseline(t, tc.beforeHex)
		modules[tc.name] = []string{base64.StdEncoding.EncodeToString(before), base64.StdEncoding.EncodeToString(m.Bytes)}
		t.Logf("%s bytes %d → %d; new instructions %d", tc.name, len(before), len(m.Bytes), m.ByteValidation.Instructions)
	}
	data, err := json.Marshal(modules)
	if err != nil {
		t.Fatal(err)
	}
	return data
}

const wasmLoopInstances = `
const data=JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]);
const lanes=[{},{}];
for(const [name,pair] of Object.entries(data))for(let i=0;i<2;i++){
  const bytes=Uint8Array.from(atob(pair[i]),c=>c.charCodeAt(0));
  if(!WebAssembly.validate(bytes))throw Error("invalid "+name);
  lanes[i][name]=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports.main;
}
function equal(a,b){if(a!==b)throw Error(a+" != "+b)}
`

func TestWasmStructuredLoopExecution(t *testing.T) {
	engine := wasmtest.Require(t)
	script := wasmLoopInstances + `
for(const e of lanes){
  for(const n of [...Array(128).keys(),65535,65536,100000]){
    equal(e.sum(n),Number(BigInt.asIntN(32,BigInt(n)*BigInt(n-1)/2n)));
    equal(e.swap(n),n%2?21:12);
  }
  const edges=[0n,1n,2n,3n,462n,1071n,4294967295n,9223372036854775808n,18446744073709551615n];
  for(const x of edges)for(const y of edges){
    let a=x,b=y;while(b!==0n){const r=a%b;a=b;b=r}
    equal(e.gcd(x,y),BigInt.asIntN(64,a));
  }
}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(wasmLoopModules(t))).CombinedOutput(); err != nil {
		t.Fatalf("structured vs dispatcher loop execution: %v\n%s", err, out)
	}
}

func TestWasmStructuredLoopTiming(t *testing.T) {
	if os.Getenv("OAK_WASM_BENCHMARKS") != "1" {
		t.Skip("opt-in engine timings; no noisy CI threshold")
	}
	engine := wasmtest.Require(t)
	script := wasmLoopInstances + `
const samples=[[],[]],calls=8,n=1000000;
function batch(lane,count){
  for(let j=0;j<calls;j++){
    const size=count+j*97,got=lanes[lane].sum(size);
    equal(got,(size*(size-1)/2)|0);
  }
}
for(let k=0;k<20;k++)for(let lane=0;lane<2;lane++)batch(lane,10000);
for(let round=0;round<7;round++)for(const lane of round%2?[1,0]:[0,1]){
  const start=performance.now();batch(lane,n);samples[lane].push(performance.now()-start);
}
const median=a=>[...a].sort((a,b)=>a-b)[Math.floor(a.length/2)];
console.log(JSON.stringify({engine:typeof Deno!=="undefined"?Deno.version:process.versions,
  warmup:"20 batches per lane, 8 calls per batch, 10000+j*97 iterations",
  callsPerSample:calls,iterations:"1000000+j*97",dispatcher_ms:samples[0],structured_ms:samples[1],
  median_ratio:median(samples[1])/median(samples[0])}));
`
	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	out, err := engine.Command(ctx, script, string(wasmLoopModules(t))).CombinedOutput()
	if err != nil {
		t.Fatalf("loop timing: %v\n%s", err, out)
	}
	t.Log(string(out))
}

func TestWasmStructuredLoopEffects(t *testing.T) {
	engine := wasmtest.Require(t)
	const source = `
divide: (x: u32): u32 = u32(12) / x
noop: (): () = {}
discard: (x: u32): () { unused: u32 = divide(x); noop() }
entry: (n: u32, d: u32): u32 { i: u32 = divide(d); while i < n { i = i + u32(1) }; i }
header: (n: u32): u32 { i: u32 = n; while divide(i) > u32(0) { i = i - u32(1) }; i }
exit: (n: u32, d: u32): u32 { i: u32 = 0; while i < n { i = i + u32(1) }; divide(d) }
unit: (n: u32): () { i: u32 = 0; while i < n { discard(i); i = i + u32(1) }; noop() }
nested: (n: u32): u32 {
  i: u32 = 0
  total: u32 = 0
  while i < n {
    j: u32 = 0
    while j < i { total = total + u32(1); j = j + u32(1) }
    i = i + u32(1)
  }
  total
}
`
	m, err := New().WithSource("effects.oak", source).EmitWasm().Get()
	if err != nil {
		t.Fatal(err)
	}
	script := `
const bytes=Uint8Array.from(atob(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]),c=>c.charCodeAt(0));
const e=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports;
function equal(a,b){if(a!==b)throw Error(a+" != "+b)}
function trap(f){try{f()}catch(err){if(err instanceof WebAssembly.RuntimeError)return;throw err}throw Error("lost loop trap")}
equal(e.entry(0,3),4);equal(e.entry(10,3),10);trap(()=>e.entry(0,0));trap(()=>e.entry(10,0));
equal(e.header(13),13);trap(()=>e.header(0));trap(()=>e.header(1));trap(()=>e.header(12));
equal(e.unit(0),undefined);trap(()=>e.unit(1));trap(()=>e.unit(10));
for(let n=0;n<20;n++){equal(e.exit(n,3),4);trap(()=>e.exit(n,0));equal(e.nested(n),n*(n-1)/2)}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, base64.StdEncoding.EncodeToString(m.Bytes)).CombinedOutput(); err != nil {
		t.Fatalf("structured loop effects: %v\n%s", err, out)
	}
}
