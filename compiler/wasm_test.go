package compiler

import (
	"bytes"
	"context"
	"encoding/base64"
	"fmt"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/internal/wasmtest"
	"github.com/SCKelemen/oak/target"
)

// A JS engine independently decodes, validates and executes actual output bytes.
// These tests are conformance evidence, not formal refinement certificates.
func TestWasmScalarExecution(t *testing.T) {
	engine := wasmtest.Require(t)
	const source = `
add: (x: u32, y: u32): u32 = x + y
wide: (x: u64, y: u64): u64 = x * y
less: (x: u64, y: u64): Bool = x < y
signed_less: (x: i64, y: i64): Bool = x < y
neg: (x: i32): i32 = -x
neg_wide: (x: i64): i64 = -x
invert: (p: Bool): Bool = !p
noop: (): () = {}
call_noop: (): () = { noop() }
choose: (p: Bool, x: i32, y: i32): i32 = p ? x | y
sum: (n: u32): u32 {
  i: u32 = 0
  total: u32 = 0
  while i < n {
    total = add(total, i)
    i = i + u32(1)
  }
  total
}
swap: (n: u32): u32 {
  a: u32 = 1
  b: u32 = 2
  i: u32 = 0
  while i < n {
    tmp: u32 = a
    a = b
    b = tmp
    i = i + u32(1)
  }
  a * u32(10) + b
}
main: (): i32 = choose(sum(u32(10)) == u32(45), i32(42), i32(1))
`
	comp := New().WithSource("scalar.oak", source)
	module, err := comp.EmitWasm().Get()
	if err != nil {
		t.Fatal(err)
	}
	if module.TranslationVerified {
		t.Fatal("experimental emitter claimed formal verification")
	}
	if module.ByteValidation == nil || module.ByteValidation.SHA256 == "" {
		t.Fatal("emission bypassed independent byte validation")
	}
	again, err := comp.EmitWasm().Get()
	if err != nil || !bytes.Equal(module.Bytes, again.Bytes) {
		t.Fatal("nondeterministic emission", err)
	}
	script := `const encoded=typeof Deno!=="undefined"?Deno.args[0]:process.argv[1];
const b=Uint8Array.from(atob(encoded),c=>c.charCodeAt(0));
if(!WebAssembly.validate(b))throw Error("invalid module");
const m=new WebAssembly.Module(b);if(WebAssembly.Module.imports(m).length)throw Error("unexpected imports");
const e=new WebAssembly.Instance(m,{}).exports;
function equal(a,b){if(a!==b)throw Error(a+" != "+b);}
equal(e.main(),42);equal(e.add(-1,1),0);equal(e.neg(-2147483648),-2147483648);
equal(e.neg_wide(-9223372036854775808n),-9223372036854775808n);
equal(e.invert(0),1);equal(e.invert(1),0);equal(e.noop(),undefined);equal(e.call_noop(),undefined);
equal(e.wide(0xffffffffffffffffn,2n),-2n);equal(e.less(-1n,0n),0);equal(e.signed_less(-1n,0n),1);
equal(e.choose(0,3,7),7);equal(e.choose(1,3,7),3);
let trapped=false;try{e.choose(2,3,7)}catch(x){trapped=x instanceof WebAssembly.RuntimeError}if(!trapped)throw Error("invalid Bool accepted");
for(let n=0;n<100;n++){equal(e.sum(n),n*(n-1)/2);equal(e.swap(n),n%2?21:12);}
const bad=Uint8Array.from(b);bad[0]=1;if(WebAssembly.validate(bad))throw Error("bad magic accepted");
if(WebAssembly.validate(b.subarray(0,b.length-1)))throw Error("truncation accepted");`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, base64.StdEncoding.EncodeToString(module.Bytes)).CombinedOutput(); err != nil {
		t.Fatalf("Wasm engine: %v\n%s", err, out)
	}
}

// Exercise every binary opcode across both widths and signedness, comparing
// actual engine results against mathematical BigInt operations modulo 2^width.
func TestWasmIntegerOperations(t *testing.T) {
	engine := wasmtest.Require(t)
	ops := []struct{ name, token, result string }{
		{"add", "+", ""}, {"sub", "-", ""}, {"mul", "*", ""},
		{"and", "&", ""}, {"or", "|", ""}, {"xor", "^", ""},
		{"eq", "==", "Bool"}, {"ne", "!=", "Bool"}, {"lt", "<", "Bool"},
		{"le", "<=", "Bool"}, {"gt", ">", "Bool"}, {"ge", ">=", "Bool"},
	}
	var source, script strings.Builder
	script.WriteString(`const encoded=typeof Deno!=="undefined"?Deno.args[0]:process.argv[1];
const bytes=Uint8Array.from(atob(encoded),c=>c.charCodeAt(0));
const e=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports;
const cases=[0n,1n,-1n,63n,64n,127n,128n,-2147483648n,2147483647n,4294967295n,-9223372036854775808n,9223372036854775807n,18446744073709551615n];
function check(name,bits,signed,cmp,op){
for(const x of cases)for(const y of cases){
const a=(signed?BigInt.asIntN:BigInt.asUintN)(bits,x),b=(signed?BigInt.asIntN:BigInt.asUintN)(bits,y);
const value=op(a,b),want=cmp?Number(value):BigInt.asIntN(bits,value);
const got=e[name](bits===32?Number(a):a,bits===32?Number(b):b);
if((cmp?got:BigInt(got))!==want)throw Error(name+"("+a+","+b+"): "+got+" != "+want);
}}
`)
	for _, typ := range []string{"u32", "i32", "u64", "i64"} {
		for _, op := range ops {
			if typ[0] == 'i' && (op.name == "and" || op.name == "or" || op.name == "xor") {
				continue // Oak's source language restricts bitwise ops to unsigned.
			}
			result := op.result
			if result == "" {
				result = typ
			}
			name := typ + "_" + op.name
			fmt.Fprintf(&source, "%s: (x: %s, y: %s): %s = (x %s y)\n", name, typ, typ, result, op.token)
			fmt.Fprintf(&script, "check(%q,%s,%t,%t,(a,b)=>a %s b);\n", name, typ[1:], typ[0] == 'i', result == "Bool", op.token)
		}
	}
	module, err := New().WithSource("integer_ops.oak", source.String()).EmitWasm().Get()
	if err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script.String(), base64.StdEncoding.EncodeToString(module.Bytes)).CombinedOutput(); err != nil {
		t.Fatalf("Wasm integer operations: %v\n%s", err, out)
	}
}

func TestWasmRefusals(t *testing.T) {
	for _, source := range []string{
		"main: (): f32 = f32(1)",
		"main: (): u8 = u8(1)",
		"main: (x: u16): u16 = x / u16(3)",
		"main: (x: u32): u32 = x >> u32(1)",
		"main: (x: i32): i32 = x & i32(1)",
		"main: (): u32 { a: [2]u32; a[0] }",
		"g: u32 = 1\nmain: (): u32 = g",
		"main: (): i32 = missing()",
	} {
		got, err := New().WithSource("refuse.oak", source).EmitWasm().Get()
		if err == nil || len(got.Bytes) != 0 {
			t.Errorf("did not fail closed for %s: %v", source, err)
		}
	}
	comp := New().WithSource("main.oak", "main: (): i32 = 42")
	if _, err := comp.WithVerifiedProfile().EmitWasm().Get(); err == nil || !strings.Contains(err.Error(), "verification is not implemented") {
		t.Fatal("verified-only did not refuse", err)
	}
	if _, err := comp.WithNativeBodies().EmitWasm().Get(); err == nil {
		t.Fatal("native option accepted")
	}
	if _, err := comp.WithTarget(target.Target{OS: target.OSCore, Arch: target.ArchWasm32}).EmitC().Get(); err == nil {
		t.Fatal("C output accepted for Wasm")
	}
	if _, err := comp.WithTarget(target.Target{OS: target.OSCore, Arch: target.ArchWasm32}).EmitNative(HostObjectFormat()).Get(); err == nil {
		t.Fatal("native output accepted for Wasm")
	}
}
