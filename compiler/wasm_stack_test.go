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

const wasmStackSource = `
pick: (x: u32): u32 = (x & u32(1)) == u32(0) ? x * u32(3) + u32(1) | x + u32(7)
main: (n: u32): u32 { i: u32 = 0; total: u32 = 0; while i < n { total = total + pick(i); i = i + u32(1) }; total }
`

// Captured from production recipe v8 at specification 5185645c, immediately
// before pure single-use SSA expressions were stackified.
const wasmStackBaselineHex = "0061736d01000000010b0260017f017f60017f017f0303020001070f02046d61696e0000047069636b00010ad40102720d017f017f017f017f017f017f017f017f017f017f017f017f017f41002101410021022001200221042103034020032000492105200504402003200421072106200610012108200720086a21094101210a2006200a6a210b200b2009210421030c010520032004210d210c200d0f0b0b000b5f0b017f017f017f017f017f017f017f017f017f017f017f410121012000200171210241002103200220034621042004044041032105200020056c210641012107200620076a21082008210b0541072109200020096a210a200a210b0b200b0b"

func wasmStackModules(t *testing.T) []byte {
	t.Helper()
	baseline := wasmSizeBaseline(t, wasmStackBaselineHex)
	baselineReport, err := check.Validate(baseline)
	if err != nil || len(baseline) != 258 || baselineReport.Instructions != 88 {
		t.Fatalf("invalid stackification baseline: bytes=%d instructions=%d err=%v", len(baseline), baselineReport.Instructions, err)
	}
	current, err := New().WithSource("stack.oak", wasmStackSource).EmitWasm().Get()
	if err != nil {
		t.Fatal(err)
	}
	if current.ByteValidation == nil || current.TranslationVerified || len(current.Bytes) != 161 || current.ByteValidation.Instructions != 56 {
		t.Fatalf("unexpected stackified module: bytes=%d instructions=%d", len(current.Bytes), current.ByteValidation.Instructions)
	}
	t.Logf("stackification bytes %d -> %d; instructions %d -> %d", len(baseline), len(current.Bytes), baselineReport.Instructions, current.ByteValidation.Instructions)
	data, err := json.Marshal([]string{base64.StdEncoding.EncodeToString(baseline), base64.StdEncoding.EncodeToString(current.Bytes)})
	if err != nil {
		t.Fatal(err)
	}
	return data
}

func TestWasmStackExpressionExecution(t *testing.T) {
	engine := wasmtest.Require(t)
	script := `
const modules=JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]);
const lanes=modules.map(s=>new WebAssembly.Instance(new WebAssembly.Module(Uint8Array.from(atob(s),c=>c.charCodeAt(0))),{}).exports);
const pick=x=>(x%2?x+7:3*x+1)|0;
for(const e of lanes){
  let want=0;
  for(let n=0;n<1000;n++){if(e.main(n)!==want||e.pick(n)!==pick(n))throw Error("stack expression mismatch at "+n);want=(want+pick(n))|0}
  for(const n of [65535,65536,100000]){let groups=Math.floor(n/2),want=(4*groups*groups+5*groups+(n%2?6*groups+1:0))|0;if(e.main(n)!==want)throw Error("large stack mismatch")}
}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(wasmStackModules(t))).CombinedOutput(); err != nil {
		t.Fatalf("stack expression execution: %v\n%s", err, out)
	}
}

func TestWasmStackExpressionTiming(t *testing.T) {
	if os.Getenv("OAK_WASM_BENCHMARKS") != "1" {
		t.Skip("opt-in engine timings; no noisy CI threshold")
	}
	engine := wasmtest.Require(t)
	script := `
const modules=JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]);
const lanes=modules.map(s=>new WebAssembly.Instance(new WebAssembly.Module(Uint8Array.from(atob(s),c=>c.charCodeAt(0))),{}).exports.main);
const samples=[[],[]],calls=8,n=10000000;
const expected=x=>{const p=Math.floor(x/2);return (4*p*p+5*p+(x%2?6*p+1:0))|0};
function batch(lane,count){for(let j=0;j<calls;j++){const size=count+j*97;if(lanes[lane](size)!==expected(size))throw Error("timing mismatch")}}
for(let k=0;k<20;k++)for(let lane=0;lane<2;lane++)batch(lane,100000);
for(let round=0;round<7;round++)for(const lane of round%2?[1,0]:[0,1]){const start=performance.now();batch(lane,n);samples[lane].push(performance.now()-start)}
const median=a=>[...a].sort((a,b)=>a-b)[3];
console.log(JSON.stringify({engine:typeof Deno!=="undefined"?Deno.version:process.versions,
  warmup:"20 batches per lane, 8 calls per batch, 100000 iterations",callsPerSample:calls,iterations:"10000000+j*97",
  local_ssa_ms:samples[0],stack_expression_ms:samples[1],median_ratio:median(samples[1])/median(samples[0])}));
`
	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(wasmStackModules(t))).CombinedOutput(); err != nil {
		t.Fatalf("stack expression timing: %v\n%s", err, out)
	} else {
		t.Log(string(out))
	}
}
