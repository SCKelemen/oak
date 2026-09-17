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

// Pre-change bytes are captured from specification 65477201, whose nested and
// sequential conditionals still dispatch. Keep these executable, not just sizes.
var wasmForwardCases = []struct {
	name, source, beforeHex     string
	wantBytes, wantInstructions int
}{
	{"nested", "main: (p: Bool, q: Bool, x: u32): u32 = p ? (q ? x + u32(1) | x * u32(3)) | x + u32(7)",
		"0061736d0100000001080160037f7f7f017f03020100070801046d61696e00000ada0101d70109017f017f017f017f017f017f017f017f017f200041014b0440000b200141014b0440000b4100210b0340200b4100460440200004404101210b0c02054102210b0c020b0b200b4101460440200104404104210b0c02054105210b0c020b0b200b410246044041072103200220036a2104200421054103210b0c010b200b410346044020050f0b200b410446044041012106200220066a21072007210a4106210b0c010b200b410546044041032108200220086c21092009210a4106210b0c010b200b4106460440200a21054103210b0c010b000b000b", 167, 66},
	{"serial", "main: (p: Bool, q: Bool, x: i64, y: i64): i64 { a: i64 = p ? x | y; b: i64 = q ? a * i64(3) | a + i64(7); b + a }",
		"0061736d0100000001090160047f7f7e7e017e03020100070801046d61696e00000ad40101d10108017e017e017e017e017e017e017e017f200041014b0440000b200141014b0440000b4100210b0340200b4100460440200004404101210b0c02054102210b0c020b0b200b4101460440200221044103210b0c010b200b4102460440200321044103210b0c010b200b4103460440200104404104210b0c02054105210b0c020b0b200b410446044042032105200420057e2106200621094106210b0c010b200b410546044042072107200420077c2108200821094106210b0c010b200b4106460440200920047c210a200a0f0b000b000b", 160, 64},
	{"kernel", "pick: (x: u32): u32 = (x & u32(1)) == u32(0) ? ((x & u32(2)) == u32(0) ? x + u32(1) | x * u32(3)) | x + u32(7)\nmain: (n: u32): u32 { i: u32 = 0; total: u32 = 0; while i < n { total = total + pick(i); i = i + u32(1) }; total }",
		"0061736d01000000010b0260017f017f60017f017f0303020001070f02046d61696e0000047069636b00010af70202720d017f017f017f017f017f017f017f017f017f017f017f017f017f41002101410021022001200221042103034020032000492105200504402003200421072106200610012108200720086a21094101210a2006200a6a210b200b2009210421030c010520032004210d210c200d0f0b0b000b810211017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f017f410021110340201141004604404101210120002001712102410021032002200346210420040440410121110c0205410221110c020b0b201141014604404102210520002005712106410021072006200746210820080440410421110c0205410521110c020b0b2011410246044041072109200020096a210a200a210b410321110c010b20114103460440200b0f0b201141044604404101210c2000200c6a210d200d2110410621110c010b201141054604404103210e2000200e6c210f200f2110410621110c010b201141064604402010210b410321110c010b000b000b", 335, 126},
}

func wasmForwardModules(t *testing.T) []byte {
	t.Helper()
	modules := map[string][]string{}
	for _, tc := range wasmForwardCases {
		m, err := New().WithSource("forward.oak", tc.source).EmitWasm().Get()
		if err != nil {
			t.Fatal(err)
		}
		if m.TranslationVerified || m.ByteValidation == nil || len(m.Bytes) != tc.wantBytes || m.ByteValidation.Instructions != tc.wantInstructions {
			t.Fatalf("%s: unexpected admission/size/instructions: %+v", tc.name, m)
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

func TestWasmForwardEmission(t *testing.T) { wasmForwardModules(t) }

const wasmForwardInstances = `
const data=JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]);
const lanes=[{},{}];
for(const [name,pair] of Object.entries(data))for(let i=0;i<2;i++){
  const bytes=Uint8Array.from(atob(pair[i]),c=>c.charCodeAt(0));
  if(!WebAssembly.validate(bytes))throw Error("invalid "+name);
  lanes[i][name]=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports;
}
function equal(a,b){if(a!==b)throw Error(a+" != "+b)}
function pick(x){return ((x&1)?x+7:((x&2)?x*3:x+1))|0}
function expected(n){
  const groups=Math.floor(n/4);let total=12*groups*groups+13*groups;
  for(let i=groups*4;i<n;i++)total+=pick(i);
  return total|0;
}
`

func TestWasmForwardExecution(t *testing.T) {
	engine := wasmtest.Require(t)
	script := wasmForwardInstances + `
for(const e of lanes){
  for(const x of [0,1,2,2147483647,2147483648,4294967295])for(const p of [0,1])for(const q of [0,1])
    equal(e.nested.main(p,q,x),(p?(q?x+1:x*3):x+7)|0);
  const edges=[0n,1n,-1n,2147483647n,-2147483648n,9223372036854775807n,-9223372036854775808n];
  for(const x of edges)for(const y of edges)for(const p of [0,1])for(const q of [0,1]){
    const a=p?x:y;equal(e.serial.main(p,q,x,y),BigInt.asIntN(64,(q?a*3n:a+7n)+a));
  }
  let reference=0;
  for(let n=0;n<1000;n++){equal(e.kernel.main(n),reference);equal(expected(n),reference);reference=(reference+pick(n))|0}
  for(const n of [65535,65536,100000])equal(e.kernel.main(n),expected(n));
  for(const x of [0,1,2,3,4,2147483647,2147483648,4294967295])equal(e.kernel.pick(x),pick(x));
}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(wasmForwardModules(t))).CombinedOutput(); err != nil {
		t.Fatalf("forward execution: %v\n%s", err, out)
	}
}

func TestWasmForwardTiming(t *testing.T) {
	if os.Getenv("OAK_WASM_BENCHMARKS") != "1" {
		t.Skip("opt-in engine timings; no noisy CI threshold")
	}
	engine := wasmtest.Require(t)
	script := wasmForwardInstances + `
const samples=[[],[]],calls=8,n=1000000;
function batch(lane,count){for(let j=0;j<calls;j++){const size=count+j*97;equal(lanes[lane].kernel.main(size),expected(size))}}
for(let k=0;k<20;k++)for(let lane=0;lane<2;lane++)batch(lane,10000);
for(let round=0;round<7;round++)for(const lane of round%2?[1,0]:[0,1]){
  const start=performance.now();batch(lane,n);samples[lane].push(performance.now()-start);
}
const median=a=>[...a].sort((a,b)=>a-b)[3];
console.log(JSON.stringify({engine:typeof Deno!=="undefined"?Deno.version:process.versions,
  warmup:"20 batches per lane, 8 calls per batch, 10000+j*97 iterations",callsPerSample:calls,iterations:"1000000+j*97",
  dispatcher_ms:samples[0],forward_ms:samples[1],median_ratio:median(samples[1])/median(samples[0])}));
`
	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	out, err := engine.Command(ctx, script, string(wasmForwardModules(t))).CombinedOutput()
	if err != nil {
		t.Fatalf("forward timing: %v\n%s", err, out)
	}
	t.Log(string(out))
}

func TestWasmForwardEffects(t *testing.T) {
	engine := wasmtest.Require(t)
	const source = `
divide: (d: u32): u32 = u32(12) / d
predicate: (d: u32): Bool = divide(d) > u32(0)
noop: (): () = {}
discard: (d: u32): () { unused: u32 = divide(d); noop() }
unit: (p: Bool, q: Bool, a: u32, b: u32): () = p ? (q ? discard(a) | discard(b)) | noop()
signed: (p: Bool, q: Bool, x: i64, y: i64, z: i64): i64 = p ? (q ? x / y | x / z) | x / -i64(1)
serial: (p: Bool, q: Bool, a: u32, b: u32, d: u32): u32 { x: u32 = p ? divide(a) | divide(b); y: u32 = q ? x | divide(d); y + x }
entry: (p: Bool, q: Bool, d: u32): u32 { x: u32 = divide(d); p ? (q ? x | u32(7)) | u32(9) }
tail: (p: Bool, q: Bool, d: u32): u32 { x: u32 = p ? (q ? u32(1) | u32(2)) | u32(3); x + divide(d) }
short: (p: Bool, q: Bool, d: u32): Bool = p && (q || predicate(d))
`
	m, err := New().WithSource("forward-effects.oak", source).EmitWasm().Get()
	if err != nil {
		t.Fatal(err)
	}
	script := `
const bytes=Uint8Array.from(atob(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]),c=>c.charCodeAt(0));
const e=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports;
function equal(a,b){if(a!==b)throw Error(a+" != "+b)}
function trap(f){try{f()}catch(err){if(err instanceof WebAssembly.RuntimeError)return;throw err}throw Error("lost forward trap")}
equal(e.unit(0,0,0,0),undefined);equal(e.unit(1,1,3,0),undefined);equal(e.unit(1,0,0,3),undefined);
trap(()=>e.unit(1,1,0,3));trap(()=>e.unit(1,0,3,0));trap(()=>e.unit(0,2,3,3));
const minimum=-9223372036854775808n;
equal(e.signed(0,0,minimum,0n,0n),minimum);equal(e.signed(1,1,minimum,-1n,0n),minimum);
equal(e.signed(1,0,12n,0n,3n),4n);trap(()=>e.signed(1,0,12n,3n,0n));trap(()=>e.signed(1,1,12n,0n,3n));
equal(e.serial(1,1,3,0,0),8);equal(e.serial(0,0,0,3,2),10);
trap(()=>e.serial(1,1,0,3,3));trap(()=>e.serial(0,1,3,0,3));trap(()=>e.serial(1,0,3,3,0));
for(const p of [0,1])for(const q of [0,1]){
  equal(e.entry(p,q,3),p?(q?4:7):9);trap(()=>e.entry(p,q,0));
  equal(e.tail(p,q,3),(p?(q?1:2):3)+4);trap(()=>e.tail(p,q,0));
}
equal(e.short(0,0,0),0);equal(e.short(1,1,0),1);equal(e.short(1,0,3),1);equal(e.short(1,0,13),0);
trap(()=>e.short(1,0,0));trap(()=>e.short(0,2,3));
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, base64.StdEncoding.EncodeToString(m.Bytes)).CombinedOutput(); err != nil {
		t.Fatalf("forward effects: %v\n%s", err, out)
	}
}
