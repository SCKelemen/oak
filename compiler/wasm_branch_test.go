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

// Baselines captured at specification b95bdffb: loops already structured, but
// diamond helpers still dispatch. Both versions use identical Oak semantics.
var wasmBranchCases = []struct {
	name, source, beforeHex     string
	wantBytes, wantInstructions int
}{
	{"guarded", "main: (x: u32, y: u32): u32 = y == u32(0) ? u32(123) | x / y",
		"0061736d0100000001070160027f7f017f03020100070801046d61696e00000a79017706017f017f017f017f017f017f41002107034020074100460440410021022001200246210320030440410121070c0205410221070c020b0b2007410146044041fb00210420042106410321070c010b20074102460440200020016e210520052106410321070c010b2007410346044020060f0b000b000b", 68, 16},
	{"join", "main: (p: Bool, x: i64, y: i64): i64 { z: i64 = p ? x | y; z * z + i64(3) }",
		"0061736d0100000001080160037f7e7e017e03020100070801046d61696e00000a7b017905017e017e017e017e017f200041014b0440000b4100210703402007410046044020000440410121070c0205410221070c020b0b2007410146044020012103410321070c010b2007410246044020022103410321070c010b20074103460440200320037e210442032105200420057c210620060f0b000b000b", 71, 20},
	{"kernel", "pick: (x: u32): u32 = (x & u32(1)) == u32(0) ? x * u32(3) + u32(1) | x + u32(7)\nmain: (n: u32): u32 { i: u32 = 0; total: u32 = 0; while i < n { total = total + pick(i); i = i + u32(1) }; total }",
		"0061736d01000000010b0260017f017f60017f017f0303020001070f02046d61696e0000047069636b00010a990202720d017f017f017f017f017f017f017f017f017f017f017f017f017f41002101410021022001200221042103034020032000492105200504402003200421072106200610012108200720086a21094101210a2006200a6a210b200b2009210421030c010520032004210d210c200d0f0b0b000ba3010c017f017f017f017f017f017f017f017f017f017f017f017f4100210c0340200c410046044041012101200020017121024100210320022003462104200404404101210c0c02054102210c0c020b0b200c410146044041032105200020056c210641012107200620076a21082008210b4103210c0c010b200c410246044041072109200020096a210a200a210b4103210c0c010b200c4103460440200b0f0b000b000b", 161, 56},
}

func wasmBranchModules(t *testing.T) []byte {
	t.Helper()
	modules := map[string][]string{}
	for _, tc := range wasmBranchCases {
		m, err := New().WithSource("branch.oak", tc.source).EmitWasm().Get()
		if err != nil {
			t.Fatal(err)
		}
		if m.ByteValidation == nil || m.TranslationVerified || len(m.Bytes) != tc.wantBytes || m.ByteValidation.Instructions != tc.wantInstructions {
			t.Fatalf("%s: bytes=%d instructions=%d; want %d/%d", tc.name, len(m.Bytes), m.ByteValidation.Instructions, tc.wantBytes, tc.wantInstructions)
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

const wasmBranchInstances = `
const data=JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]);
const lanes=[{},{}];
for(const [name,pair] of Object.entries(data))for(let i=0;i<2;i++){
  const bytes=Uint8Array.from(atob(pair[i]),c=>c.charCodeAt(0));
  if(!WebAssembly.validate(bytes))throw Error("invalid "+name);
  lanes[i][name]=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports;
}
function equal(a,b){if(a!==b)throw Error(a+" != "+b)}
function expectedKernel(n){const pairs=Math.floor(n/2);return (4*pairs*pairs+5*pairs+(n%2?6*pairs+1:0))|0}
`

func TestWasmDiamondExecution(t *testing.T) {
	engine := wasmtest.Require(t)
	script := wasmBranchInstances + `
for(const e of lanes){
  const edges=[0n,1n,-1n,2147483647n,-2147483648n,4294967295n,9223372036854775807n,-9223372036854775808n];
  for(const x of edges)for(const y of edges){
    const a=BigInt.asUintN(32,x),b=BigInt.asUintN(32,y);
    equal(e.guarded.main(Number(a),Number(b)),b===0n?123:Number(BigInt.asIntN(32,a/b)));
    for(const p of [0,1]){const z=p?x:y;equal(e.join.main(p,x,y),BigInt.asIntN(64,z*z+3n))}
  }
  for(let n=0;n<1000;n++)equal(e.kernel.main(n),expectedKernel(n));
  for(const n of [65535,65536,100000])equal(e.kernel.main(n),expectedKernel(n));
  for(const x of [0,1,2,2147483647,2147483648,4294967295])equal(e.kernel.pick(x),(x%2?x+7:x*3+1)|0);
}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(wasmBranchModules(t))).CombinedOutput(); err != nil {
		t.Fatalf("diamond execution: %v\n%s", err, out)
	}
}

func TestWasmDiamondTiming(t *testing.T) {
	if os.Getenv("OAK_WASM_BENCHMARKS") != "1" {
		t.Skip("opt-in engine timings; no noisy CI threshold")
	}
	engine := wasmtest.Require(t)
	script := wasmBranchInstances + `
const samples=[[],[]],calls=8,n=1000000;
function batch(lane,count){for(let j=0;j<calls;j++){const size=count+j*97;equal(lanes[lane].kernel.main(size),expectedKernel(size))}}
for(let k=0;k<20;k++)for(let lane=0;lane<2;lane++)batch(lane,10000);
for(let round=0;round<7;round++)for(const lane of round%2?[1,0]:[0,1]){
  const start=performance.now();batch(lane,n);samples[lane].push(performance.now()-start);
}
const median=a=>[...a].sort((a,b)=>a-b)[3];
console.log(JSON.stringify({engine:typeof Deno!=="undefined"?Deno.version:process.versions,
  warmup:"20 batches per lane, 8 calls per batch, 10000+j*97 iterations",callsPerSample:calls,iterations:"1000000+j*97",
  dispatcher_ms:samples[0],diamond_ms:samples[1],median_ratio:median(samples[1])/median(samples[0])}));
`
	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	out, err := engine.Command(ctx, script, string(wasmBranchModules(t))).CombinedOutput()
	if err != nil {
		t.Fatalf("diamond timing: %v\n%s", err, out)
	}
	t.Log(string(out))
}

func TestWasmDiamondEffects(t *testing.T) {
	engine := wasmtest.Require(t)
	const source = `
divide: (x: u32): u32 = u32(12) / x
predicate: (d: u32): Bool = divide(d) > u32(0)
noop: (): () = {}
discard: (d: u32): () { unused: u32 = divide(d); noop() }
condition: (d: u32, x: u32, y: u32): u32 = predicate(d) ? x | y
arms: (p: Bool, a: u32, b: u32): u32 = p ? divide(a) | divide(b)
unit: (p: Bool, a: u32, b: u32): () = p ? discard(a) | discard(b)
merge: (p: Bool, x: u32, y: u32, d: u32): u32 { z: u32 = p ? x | y; z + divide(d) }
always: (d: u32): u32 = true ? u32(7) | divide(d)
short_and: (p: Bool, d: u32): Bool = p && predicate(d)
short_or: (p: Bool, d: u32): Bool = p || predicate(d)
nested: (p: Bool, q: Bool): u32 = p ? (q ? u32(1) | u32(2)) | u32(3)
`
	m, err := New().WithSource("effects.oak", source).EmitWasm().Get()
	if err != nil {
		t.Fatal(err)
	}
	script := `
const bytes=Uint8Array.from(atob(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]),c=>c.charCodeAt(0));
const e=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports;
function equal(a,b){if(a!==b)throw Error(a+" != "+b)}
function trap(f){try{f()}catch(err){if(err instanceof WebAssembly.RuntimeError)return;throw err}throw Error("lost branch trap")}
equal(e.condition(3,5,9),5);equal(e.condition(13,5,9),9);trap(()=>e.condition(0,5,9));
equal(e.arms(1,3,0),4);equal(e.arms(0,0,3),4);trap(()=>e.arms(1,0,3));trap(()=>e.arms(0,3,0));
equal(e.unit(1,3,0),undefined);equal(e.unit(0,0,3),undefined);trap(()=>e.unit(1,0,3));trap(()=>e.unit(0,3,0));
equal(e.merge(1,5,9,3),9);equal(e.merge(0,5,9,3),13);trap(()=>e.merge(1,5,9,0));trap(()=>e.merge(0,5,9,0));
equal(e.always(0),7);equal(e.short_and(0,0),0);equal(e.short_or(1,0),1);
trap(()=>e.short_and(1,0));trap(()=>e.short_or(0,0));
for(const p of [0,1])for(const q of [0,1])equal(e.nested(p,q),p?(q?1:2):3);
trap(()=>e.nested(0,2));
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, base64.StdEncoding.EncodeToString(m.Bytes)).CombinedOutput(); err != nil {
		t.Fatalf("diamond effects: %v\n%s", err, out)
	}
}
