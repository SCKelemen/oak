package compiler

import (
	"bytes"
	"context"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"testing"
	"time"

	"github.com/SCKelemen/oak/internal/wasmtest"
	"github.com/SCKelemen/oak/wasm/check"
)

// Baseline bytes were captured from specification ea3c3793, before direct
// emission. Keep them executable: sizes alone cannot establish correctness.
var wasmSizeCases = []struct {
	name, source, beforeHex     string
	wantBytes, wantInstructions int
	unchanged                   bool
}{
	{"constant", "main: (): i32 = 42",
		"0061736d010000000105016000017f03020100070801046d61696e00000a20011e02017f017f41002101034020014100460440412a210020000f0b000b000b", 37, 2, false},
	{"identity", "main: (x: i64): i64 = x",
		"0061736d0100000001060160017e017e03020100070801046d61696e00000a1a011801017f4100210103402001410046044020000f0b000b000b", 38, 2, false},
	{"add", "main: (x: u32, y: u32): u32 = x + y",
		"0061736d0100000001070160027f7f017f03020100070801046d61696e00000a23012102017f017f41002103034020034100460440200020016a210220020f0b000b000b", 42, 4, false},
	{"shared", "main: (x: u64, y: u64): u64 { z: u64 = x * y; z + z }",
		"0061736d0100000001070160027e7e017e03020100070801046d61696e00000a2c012a03017e017e017f41002104034020044100460440200020017e2102200220027c210320030f0b000b000b", 51, 8, false},
	{"bool_guard", "main: (unused: Bool): i32 = 42",
		"0061736d0100000001060160017f017f03020100070801046d61696e00000a29012702017f017f200041014b0440000b41002102034020024100460440412a210120010f0b000b000b", 47, 8, false},
	{"unit", "main: (): () = {}",
		"0061736d0100000001040160000003020100070801046d61696e00000a1e011c02017f017f41002101034020014100460440410021000f0b000b000b", 34, 1, false},
	{"division", "main: (x: i64, y: i64): i64 = x / y",
		"0061736d0100000001070160027e7e017e03020100070801046d61696e00000a31012f02017e017f410021030340200341004604402001427f51047e420020007d05200020017f0b210220020f0b000b000b", 62, 15, false},
	{"call", "add: (x: u32, y: u32): u32 = x + y\nmain: (): u32 = add(u32(1), u32(2))",
		"0061736d01000000010b0260027f7f017f6000017f0303020001070e02036164640000046d61696e00010a52022102017f017f41002103034020034100460440200020016a210220020f0b000b000b2e04017f017f017f017f410021030340200341004604404101210041022101200020011000210220020f0b000b000b", 68, 10, false},
	{"branch", "main: (p: Bool, x: i32, y: i32): i32 = p ? x | y",
		"0061736d0100000001080160037f7f7f017f03020100070801046d61696e00000a63016102017f017f200041014b0440000b4100210403402004410046044020000440410121040c0205410221040c020b0b2004410146044020012103410321040c010b2004410246044020022103410321040c010b2004410346044020030f0b000b000b", 65, 16, false},
	{"loop", "main: (n: u32): u32 { i: u32 = 0; while i < n { i = i + u32(1) }; i }",
		"0061736d0100000001060160017f017f03020100070801046d61696e00000a850101820108017f017f017f017f017f017f017f017f410021080340200841004604404100210120012102410121080c010b20084101460440200220004921032003044020022104410221080c020520022107410321080c020b0b2008410246044041012105200420056a210620062102410121080c010b2008410346044020070f0b000b000b", 79, 23, false},
}

func wasmSizeBaseline(t *testing.T, encoded string) []byte {
	t.Helper()
	b, err := hex.DecodeString(encoded)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := check.Validate(b); err != nil {
		t.Fatal("invalid baseline bytes", err)
	}
	return b
}

func TestWasmDirectEmissionSize(t *testing.T) {
	for _, tc := range wasmSizeCases {
		t.Run(tc.name, func(t *testing.T) {
			before := wasmSizeBaseline(t, tc.beforeHex)
			beforeReport, _ := check.Validate(before)
			m, err := New().WithSource("size.oak", tc.source).EmitWasm().Get()
			if err != nil {
				t.Fatal(err)
			}
			if m.ByteValidation == nil || m.TranslationVerified {
				t.Fatal("direct emission bypassed byte admission or claimed formal verification")
			}
			if len(m.Bytes) != tc.wantBytes || m.ByteValidation.Instructions != tc.wantInstructions {
				t.Fatalf("bytes=%d instructions=%d; want %d/%d", len(m.Bytes), m.ByteValidation.Instructions, tc.wantBytes, tc.wantInstructions)
			}
			if tc.unchanged {
				if !bytes.Equal(m.Bytes, before) {
					t.Fatal("dispatcher fallback changed")
				}
			} else if len(m.Bytes) >= len(before) || m.ByteValidation.Instructions >= beforeReport.Instructions {
				t.Fatal("direct emission failed to improve static size/cost")
			}
			t.Logf("bytes %d → %d; instructions %d → %d", len(before), len(m.Bytes), beforeReport.Instructions, m.ByteValidation.Instructions)
		})
	}
}

func TestWasmDirectEmissionExecution(t *testing.T) {
	engine := wasmtest.Require(t)
	modules := map[string][]string{}
	for _, tc := range wasmSizeCases {
		m, err := New().WithSource("size.oak", tc.source).EmitWasm().Get()
		if err != nil {
			t.Fatal(err)
		}
		modules[tc.name] = []string{base64.StdEncoding.EncodeToString(wasmSizeBaseline(t, tc.beforeHex)), base64.StdEncoding.EncodeToString(m.Bytes)}
	}
	data, err := json.Marshal(modules)
	if err != nil {
		t.Fatal(err)
	}
	script := `
const data=JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]);
function equal(a,b){if(a!==b)throw Error(a+" != "+b)}
function trap(f){try{f()}catch(e){if(e instanceof WebAssembly.RuntimeError)return;throw e}throw Error("missing trap")}
const edges=[0n,1n,-1n,2147483647n,-2147483648n,4294967295n,9223372036854775807n,-9223372036854775808n];
for(const lane of [0,1]){
  const e={};
  for(const [name,pair] of Object.entries(data)){
    const bytes=Uint8Array.from(atob(pair[lane]),c=>c.charCodeAt(0));
    if(!WebAssembly.validate(bytes))throw Error("invalid "+name+" lane "+lane);
    e[name]=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports;
  }
  equal(e.constant.main(),42);equal(e.call.main(),3);equal(e.unit.main(),undefined);
  equal(e.bool_guard.main(0),42);equal(e.bool_guard.main(1),42);
  for(const p of [2,-1,2147483647,-2147483648])trap(()=>e.bool_guard.main(p));
  for(const x of edges){
    equal(e.identity.main(x),x);
    for(const y of edges){
      const a=BigInt.asUintN(32,x),b=BigInt.asUintN(32,y),sum=Number(BigInt.asIntN(32,a+b));
      equal(e.add.main(Number(a),Number(b)),sum);equal(e.call.add(Number(a),Number(b)),sum);
      equal(e.shared.main(x,y),BigInt.asIntN(64,2n*x*y));
      if(y===0n)trap(()=>e.division.main(x,y));
      else equal(e.division.main(x,y),BigInt.asIntN(64,x/y));
    }
  }
  equal(e.branch.main(0,3,7),7);equal(e.branch.main(1,3,7),3);trap(()=>e.branch.main(2,3,7));
  for(let n=0;n<100;n++)equal(e.loop.main(n),n);
}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(data)).CombinedOutput(); err != nil {
		t.Fatalf("direct vs dispatcher engine test: %v\n%s", err, out)
	}
}

func TestWasmDirectUnitCallTraps(t *testing.T) {
	engine := wasmtest.Require(t)
	const source = `
noop: (): () = {}
discard: (x: u32): () { unused: u32 = u32(1) / x; noop() }
keep: (x: u32): u32 { discard(x); x }
main: (): () { discard(u32(0)) }
`
	m, err := New().WithSource("unit.oak", source).EmitWasm().Get()
	if err != nil {
		t.Fatal(err)
	}
	script := `
const bytes=Uint8Array.from(atob(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]),c=>c.charCodeAt(0));
const e=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports;
if(e.discard(1)!==undefined||e.keep(3)!==3)throw Error("wrong result");
for(const f of [()=>e.discard(0),()=>e.keep(0),()=>e.main()]){
  let trapped=false;try{f()}catch(err){if(!(err instanceof WebAssembly.RuntimeError))throw err;trapped=true}
  if(!trapped)throw Error("Unit return/parameter return suppressed call or trap");
}
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, base64.StdEncoding.EncodeToString(m.Bytes)).CombinedOutput(); err != nil {
		t.Fatalf("direct Unit effect test: %v\n%s", err, out)
	}
}
