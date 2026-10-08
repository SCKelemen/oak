package compiler

import (
	"context"
	"encoding/base64"
	"encoding/json"
	"testing"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/internal/wasmtest"
	"github.com/SCKelemen/oak/target"
)

var inferredPrimitiveVerificationCases = []struct{ name, source string }{
	{"unsigned", "main: (a, b: u32): u32 { x := a | b; x }"},
	{"signed", "main: (a, b: i32): i32 { x := a + b; x }"},
	{"boolean", "main: (a, b: Bool): Bool { x := a && !b; x }"},
	{"reassignment", "main: (a, b: u32): u32 { x := a; x = x | b; x }"},
	{"constructor", "main: (): u32 { x := u32(42); x }"},
	{"nested", "main: (a, b: u32): u32 { x := a | b; true ? { y := x; y } | x }"},
}

func TestInferredPrimitiveNativeVerificationParity(t *testing.T) {
	for _, arch := range []string{target.ArchArm64, target.ArchRiscv64} {
		for _, tc := range inferredPrimitiveVerificationCases {
			t.Run(arch+"/"+tc.name, func(t *testing.T) {
				model, err := New().WithSource("inferred.oak", tc.source).WithTarget(target.Target{OS: target.OSFreestanding, Arch: arch}).WithNativeBodies().Check().Get()
				if err != nil {
					t.Fatal(err)
				}
				if why, fallback := model.NativeFallbacks["main"]; fallback {
					t.Fatal(why)
				}
				verdict, ok := model.NativeVerdicts["main"]
				if !ok || verdict.Kind != asm.VerdictProven {
					t.Fatalf("inferred primitive verification: %v", verdict)
				}
			})
		}
	}
}

// Wasm keeps its existing byte-admission and execution boundary. Native
// source inference is not a reason to promote TranslationVerified here.
func TestInferredPrimitiveWasmExecutionParity(t *testing.T) {
	engine := wasmtest.Require(t)
	modules := map[string]string{}
	for _, tc := range inferredPrimitiveVerificationCases {
		module, err := New().WithSource("inferred.oak", tc.source).EmitWasm().Get()
		if err != nil {
			t.Fatal(err)
		}
		if module.ByteValidation == nil || module.TranslationVerified {
			t.Fatal("changed Wasm proof/admission boundary")
		}
		modules[tc.name] = base64.StdEncoding.EncodeToString(module.Bytes)
	}
	data, err := json.Marshal(modules)
	if err != nil {
		t.Fatal(err)
	}
	script := `
const input=JSON.parse(typeof Deno!=="undefined"?Deno.args[0]:process.argv[1]);
const f={};
for(const [name,text] of Object.entries(input)) {
 const bytes=Uint8Array.from(atob(text),c=>c.charCodeAt(0));
 if(!WebAssembly.validate(bytes))throw Error("invalid "+name);
 f[name]=new WebAssembly.Instance(new WebAssembly.Module(bytes),{}).exports.main;
}
const equal=(x,y)=>{if(x!==y)throw Error(x+" != "+y)};
for(const a of [0,1,42,2147483647,-2147483648,-1])
 for(const b of [0,1,42,2147483647,-2147483648,-1]) {
  for(const name of ["unsigned","reassignment","nested"])equal(f[name](a,b),a|b);
  equal(f.signed(a,b),(a+b)|0);
 }
for(const a of [0,1])for(const b of [0,1])equal(f.boolean(a,b),a&&!b?1:0);
equal(f.constructor(),42);
`
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	defer cancel()
	if out, err := engine.Command(ctx, script, string(data)).CombinedOutput(); err != nil {
		t.Fatalf("Wasm inferred primitives: %v\n%s", err, out)
	}
}
