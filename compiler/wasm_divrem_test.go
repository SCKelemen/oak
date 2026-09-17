package compiler

import (
	"context"
	"encoding/base64"
	"fmt"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/internal/wasmtest"
	"github.com/SCKelemen/oak/wasm"
	"github.com/SCKelemen/oak/wasm/check"
)

func TestWasmDivisionRemainderExecution(t *testing.T) {
	engine := wasmtest.Require(t)
	var source strings.Builder
	for _, typ := range []string{"u32", "i32", "u64", "i64"} {
		fmt.Fprintf(&source, "quot_%s: (x: %s, y: %s): %s = x / y\n", typ, typ, typ, typ)
		fmt.Fprintf(&source, "rem_%s: (x: %s, y: %s): %s = x %% y\n", typ, typ, typ, typ)
	}
	source.WriteString(`
identity: (x: i64): i64 = x
call_quot: (x: i64, y: i64): i64 = identity(x) / identity(y)
choose: (p: Bool, x: i64, y: i64): i64 = p ? x / y | x % y
guarded: (x: u32, y: u32): u32 = y == u32(0) ? u32(123) | x / y
dead_div: (x: u32, y: u32): u32 { ignored: u32 = x / y; u32(7) }
dead_rem: (x: i64, y: i64): i64 { ignored: i64 = x % y; i64(7) }
constant_zero: (): u32 { ignored: u32 = u32(1) / u32(0); u32(7) }
trap_arg: (): i64 { ignored: i64 = i64(7) / i64(0); i64(8) }
trap_before_negation: (): i64 = trap_arg() / (-i64(1))
gcd: (a: u64, b: u64): u64 {
  x: u64 = a
  y: u64 = b
  while y != u64(0) {
    next: u64 = x % y
    x = y
    y = next
  }
  x
}
loop_trap: (n: u32): u32 {
  i: u32 = 0
  total: u32 = 0
  while i < n {
    total = total + u32(1) / i
    i = i + u32(1)
  }
  total
}
`)
	emission, err := New().WithSource("divrem.oak", source.String()).EmitWasmWithReport().Get()
	if err != nil {
		t.Fatal(err)
	}
	m := emission.Module
	if wasm.Profile != "oak.wasm.scalar.v1" {
		t.Fatal("unexpected profile revision", wasm.Profile)
	}
	if m.Profile != wasm.Profile || m.TranslationVerified ||
		m.ByteValidation == nil || m.ByteValidation.Validator != check.Validator || len(emission.Pipeline.Steps) != 4 {
		t.Fatal("missing v1 byte-only admission", m.ByteValidation)
	}
	script := `
const encoded=typeof Deno!=="undefined"?Deno.args[0]:process.argv[1];
const bytes=Uint8Array.from(atob(encoded),c=>c.charCodeAt(0));
if(!WebAssembly.validate(bytes))throw Error("invalid module");
const e=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports;
function trap(f){let trapped=false;try{f()}catch(err){if(!(err instanceof WebAssembly.RuntimeError))throw err;trapped=true}if(!trapped)throw Error("missing zero-divisor trap")}
function equal(a,b){if(a!==b)throw Error(a+" != "+b)}
const edges=[0n,1n,-1n,2n,-2n,3n,-3n,2147483646n,2147483647n,-2147483648n,2147483648n,4294967295n,
  9223372036854775806n,9223372036854775807n,-9223372036854775808n,9223372036854775808n,18446744073709551615n];
let checks=0,seed=0x123456789abcdefn;
function random(){seed=BigInt.asUintN(64,seed*6364136223846793005n+1442695040888963407n);return seed}
for(const [type,bits,signed] of [["u32",32,false],["i32",32,true],["u64",64,false],["i64",64,true]]){
  const norm=x=>(signed?BigInt.asIntN:BigInt.asUintN)(bits,x);
  const carrier=x=>bits===32?Number(x):BigInt.asIntN(64,x);
  function pair(x,y){const a=norm(x),b=norm(y);
    for(const op of ["quot","rem"]){checks++;const call=()=>e[op+"_"+type](carrier(a),carrier(b));
      if(b===0n){trap(call);continue}
      const expected=BigInt.asUintN(bits,op==="quot"?a/b:a%b),got=BigInt.asUintN(bits,BigInt(call()));
      if(got!==expected)throw Error(type+" "+op+"("+a+","+b+") = "+got+", expected "+expected);
    }
  }
  for(const x of edges)for(const y of edges)pair(x,y);
  for(let i=0;i<256;i++)pair(random(),random());
}
equal(e.call_quot(-9223372036854775808n,-1n),-9223372036854775808n);
equal(e.call_quot(-43n,7n),-6n);
equal(e.choose(1,-43n,7n),-6n);equal(e.choose(0,-43n,7n),-1n);
equal(e.guarded(99,0),123);equal(e.guarded(99,4),24);
equal(e.dead_div(7,2),7);equal(e.dead_rem(-9223372036854775808n,-1n),7n);
trap(()=>e.dead_div(7,0));trap(()=>e.dead_rem(7n,0n));trap(()=>e.constant_zero());trap(()=>e.trap_before_negation());
equal(e.loop_trap(0),0);trap(()=>e.loop_trap(1));
equal(e.gcd(1071n,462n),21n);equal(e.gcd(0n,0n),0n);equal(e.gcd(-1n,3n),3n);
console.log(checks+" arithmetic/trap cases plus calls, guards, dead results and loops");
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	output, err := engine.Command(ctx, script, base64.StdEncoding.EncodeToString(m.Bytes)).CombinedOutput()
	if err != nil {
		t.Fatalf("Wasm div/rem engine: %v\n%s", err, output)
	}
	t.Log(strings.TrimSpace(string(output)))
}
