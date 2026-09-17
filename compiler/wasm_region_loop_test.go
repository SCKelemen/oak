package compiler

import (
	"context"
	"encoding/base64"
	"encoding/json"
	"os"
	"testing"
	"time"

	"github.com/SCKelemen/oak/internal/wasmtest"
	"github.com/SCKelemen/oak/wasm/check"
)

// Baselines captured at specification bd89ea49 before region-loop lowering.
var wasmRegionLoopCases = []struct {
	name, source, beforeHex                         string
	wantBytes, wantInstructions, beforeInstructions int
}{
	{"branch", "main: (n: u32): u32 { i: u32 = 0; total: u32 = 0; while i < n { total = total + ((i & u32(1)) == u32(0) ? i * u32(3) + u32(1) | i + u32(7)); i = i + u32(1) }; total }",
		"0061736d0100000001060160017f017f03020100070801046d61696e00000ab50201b20218017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f4100211803402018410046044041002101410021022001200221042103410121180c010b2018410146044020032000492105200504402003200421072106410221180c020520032004210d210c410321180c020b0b2018410246044041012108200620087121094100210a2009200a46210b200b0440410421180c0205410521180c020b0b20184103460440200d0f0b201841044604404103210e2006200e6c210f41012110200f20106a211120112114410621180c010b2018410546044041072112200620126a211320132114410621180c010b20184106460440200720146a211541012116200620166a21172017201521042103410121180c010b000b000b", 251, 93, 144},
	{"nested", "main: (n: u32): u32 { i: u32 = 0; total: u32 = 0; while i < n { total = total + ((i & u32(1)) == u32(0) ? ((i & u32(2)) == u32(0) ? i + u32(1) | i * u32(3)) | i + u32(7)); i = i + u32(1) }; total }",
		"0061736d0100000001060160017f017f03020100070801046d61696e00000a93030190031d017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f4100211d0340201d4100460440410021014100210220012002210421034101211d0c010b201d4101460440200320004921052005044020032004210721064102211d0c020520032004210d210c4103211d0c020b0b201d410246044041012108200620087121094100210a2009200a46210b200b04404104211d0c02054105211d0c020b0b201d4103460440200d0f0b201d41044604404102210e2006200e71210f41002110200f2010462111201104404107211d0c02054108211d0c020b0b201d410546044041072112200620126a2113201321144106211d0c010b201d4106460440200720146a211541012116200620166a211720172015210421034101211d0c010b201d410746044041012118200620186a21192019211c4109211d0c010b201d41084604404103211a2006201a6c211b201b211c4109211d0c010b201d4109460440201c21144106211d0c010b000b000b", 312, 122, 191},
}

func wasmRegionLoopModules(t *testing.T) []byte {
	t.Helper()
	modules := map[string][]string{}
	for _, tc := range wasmRegionLoopCases {
		m, err := New().WithSource("region-loop.oak", tc.source).EmitWasm().Get()
		if err != nil {
			t.Fatal(err)
		}
		if m.TranslationVerified || m.ByteValidation == nil || len(m.Bytes) != tc.wantBytes || m.ByteValidation.Instructions != tc.wantInstructions {
			t.Fatalf("%s unexpected admission/size: %+v", tc.name, m)
		}
		before := wasmSizeBaseline(t, tc.beforeHex)
		beforeReport, err := check.Validate(before)
		if err != nil || beforeReport.Instructions != tc.beforeInstructions {
			t.Fatalf("%s baseline instructions=%d, want %d: %v", tc.name, beforeReport.Instructions, tc.beforeInstructions, err)
		}
		modules[tc.name] = []string{base64.StdEncoding.EncodeToString(before), base64.StdEncoding.EncodeToString(m.Bytes)}
		t.Logf("%s bytes %d → %d; new instructions %d", tc.name, len(before), len(m.Bytes), m.ByteValidation.Instructions)
	}
	data, err := json.Marshal(modules)
	if err != nil {
		t.Fatal(err)
	}
	return data
}

func TestWasmRegionLoopEmission(t *testing.T) { wasmRegionLoopModules(t) }

const wasmRegionLoopInstances = `
const data=JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]);
const lanes=[{},{}];
for(const [name,pair] of Object.entries(data))for(let i=0;i<2;i++){
  const bytes=Uint8Array.from(atob(pair[i]),c=>c.charCodeAt(0));
  if(!WebAssembly.validate(bytes))throw Error("invalid "+name);
  lanes[i][name]=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports.main;
}
function equal(a,b){if(a!==b)throw Error(a+" != "+b)}
function pick(x){return ((x&1)?x+7:((x&2)?x*3:x+1))|0}
function expected(n){const g=Math.floor(n/4);let total=12*g*g+13*g;for(let i=4*g;i<n;i++)total+=pick(i);return total|0}
`

func TestWasmRegionLoopSourceExecution(t *testing.T) {
	engine := wasmtest.Require(t)
	script := wasmRegionLoopInstances + `
for(const e of lanes){
  let branch=0,nested=0;
  for(let n=0;n<1000;n++){
    equal(e.branch(n),branch);equal(e.nested(n),nested);equal(expected(n),nested);
    branch=(branch+(n%2?n+7:3*n+1))|0;nested=(nested+pick(n))|0;
  }
  for(const n of [65535,65536,100000]){
    const pairs=Math.floor(n/2);equal(e.branch(n),(4*pairs*pairs+5*pairs+(n%2?6*pairs+1:0))|0);
    equal(e.nested(n),expected(n));
  }
}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(wasmRegionLoopModules(t))).CombinedOutput(); err != nil {
		t.Fatalf("region source execution: %v\n%s", err, out)
	}
}

func TestWasmRegionLoopTiming(t *testing.T) {
	if os.Getenv("OAK_WASM_BENCHMARKS") != "1" {
		t.Skip("opt-in engine timings; no noisy CI threshold")
	}
	engine := wasmtest.Require(t)
	script := wasmRegionLoopInstances + `
const samples=[[],[]],calls=8,n=1000000;
function batch(lane,count){for(let j=0;j<calls;j++){const size=count+j*97;equal(lanes[lane].nested(size),expected(size))}}
for(let k=0;k<20;k++)for(let lane=0;lane<2;lane++)batch(lane,10000);
for(let round=0;round<7;round++)for(const lane of round%2?[1,0]:[0,1]){
  const start=performance.now();batch(lane,n);samples[lane].push(performance.now()-start);
}
const median=a=>[...a].sort((a,b)=>a-b)[3];
console.log(JSON.stringify({engine:typeof Deno!=="undefined"?Deno.version:process.versions,
  warmup:"20 batches per lane, 8 calls per batch, 10000+j*97 iterations",callsPerSample:calls,iterations:"1000000+j*97",
  dispatcher_ms:samples[0],region_loop_ms:samples[1],median_ratio:median(samples[1])/median(samples[0])}));
`
	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	out, err := engine.Command(ctx, script, string(wasmRegionLoopModules(t))).CombinedOutput()
	if err != nil {
		t.Fatalf("region loop timing: %v\n%s", err, out)
	}
	t.Log(string(out))
}

func TestWasmRegionLoopEffects(t *testing.T) {
	engine := wasmtest.Require(t)
	const source = `
divide: (d: u32): u32 = u32(12) / d
noop: (): () = {}
discard: (d: u32): () { unused: u32 = divide(d); noop() }
body: (n: u32, p: Bool, d: u32): u32 { i: u32 = 0; sum: u32 = 0; while i < n { sum = sum + (p ? divide(d) | u32(7)); i = i + u32(1) }; sum }
unit: (n: u32, p: Bool, d: u32): () { i: u32 = 0; while i < n { unused: () = p ? discard(d) | noop(); i = i + u32(1) }; noop() }
entry: (n: u32, p: Bool, d: u32): u32 { start: u32 = divide(d); i: u32 = 0; while i < n { i = i + (p ? u32(1) | u32(2)) }; start + i }
header: (n: u32, p: Bool, d: u32): u32 { i: u32 = 0; while i < n + divide(d) { i = i + (p ? u32(1) | u32(2)) }; i }
tail: (n: u32, p: Bool, d: u32): u32 { i: u32 = 0; while i < n { i = i + (p ? u32(1) | u32(2)) }; i + divide(d) }
signed: (n: u32, p: Bool, x: i64, d: i64): i64 { i: u32 = 0; total: i64 = 0; while i < n { total = total + (p ? x / d | i64(3)); i = i + u32(1) }; total }
nested_loop: (n: u32): u32 { i: u32 = 0; total: u32 = 0; while i < n { j: u32 = 0; while j < i { total = total + ((j & u32(1)) == u32(0) ? u32(1) | u32(2)); j = j + u32(1) }; i = i + u32(1) }; total }
`
	m, err := New().WithSource("region-effects.oak", source).EmitWasm().Get()
	if err != nil {
		t.Fatal(err)
	}
	script := `
const bytes=Uint8Array.from(atob(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]),c=>c.charCodeAt(0));
const e=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports;
function equal(a,b){if(a!==b)throw Error(a+" != "+b)}
function trap(f){try{f()}catch(err){if(err instanceof WebAssembly.RuntimeError)return;throw err}throw Error("lost loop trap")}
for(const n of [0,1,2,3,10])for(const p of [0,1]){
  equal(e.body(n,p,3),n*(p?4:7));equal(e.unit(n,p,3),undefined);
  const after=p?n:2*Math.ceil(n/2);equal(e.entry(n,p,3),4+after);equal(e.tail(n,p,3),after+4);
  equal(e.header(n,p,3),p?n+4:2*Math.ceil((n+4)/2));
  equal(e.signed(n,p,-9223372036854775808n,-1n),BigInt.asIntN(64,BigInt(n)*(p?-9223372036854775808n:3n)));
  trap(()=>e.entry(n,p,0));trap(()=>e.header(n,p,0));trap(()=>e.tail(n,p,0));
  equal(e.body(n,0,0),7*n);equal(e.unit(n,0,0),undefined);
  if(n){trap(()=>e.body(n,1,0));trap(()=>e.unit(n,1,0));trap(()=>e.signed(n,1,1n,0n))}
}
equal(e.body(0,1,0),0);equal(e.unit(0,1,0),undefined);equal(e.signed(0,1,1n,0n),0n);
trap(()=>e.body(0,2,3));trap(()=>e.unit(0,-1,3));
for(let n=0;n<30;n++){let want=0;for(let i=0;i<n;i++)for(let j=0;j<i;j++)want+=j%2?2:1;equal(e.nested_loop(n),want)}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, base64.StdEncoding.EncodeToString(m.Bytes)).CombinedOutput(); err != nil {
		t.Fatalf("region effects: %v\n%s", err, out)
	}
}
