package check

import (
	"bytes"
	"context"
	"encoding/json"
	"testing"
	"time"

	"github.com/SCKelemen/oak/internal/wasmtest"
)

// Validate, never execute, adversarial modules in a second implementation.
// The implication is one-way: our bounded profile is narrower than Core Wasm.
func TestWasmEngineValidation(t *testing.T) {
	engine := wasmtest.Require(t)
	type row struct {
		Data     []byte `json:"data"`
		Accepted bool   `json:"accepted"`
		Exact    bool   `json:"exact"`
	}
	var corpus []row
	accepted := 0
	add := func(data []byte, exact bool) {
		_, err := Validate(data)
		if err == nil {
			accepted++
		}
		corpus = append(corpus, row{data, err == nil, exact})
	}
	for _, tt := range controlFixtures() {
		base := scalarFixture(tt.result, tt.code...)
		// Type-indexed blocks are valid Core Wasm, intentionally outside v1.
		add(base, tt.name != "unsupported block index")
		for i := range base {
			for _, mask := range []byte{1, 0x40, 0x80, 0xff} {
				mutated := append([]byte(nil), base...)
				mutated[i] ^= mask
				add(mutated, false)
			}
		}
	}
	// Well-formed non-minimal signed LEB encodings must remain accepted.
	add(scalarFixture(0x7f, 0x41, 0xaa, 0, 0x0b), true)
	add(scalarFixture(0x7e, 0x42, 0xff, 0x7f, 0x0b), true)
	data, err := json.Marshal(corpus)
	if err != nil {
		t.Fatal(err)
	}
	script := `const text=typeof Deno!=="undefined" ? await new Response(Deno.stdin.readable).text() : require("node:fs").readFileSync(0,"utf8");
const rows=JSON.parse(text);
for(let i=0;i<rows.length;i++){
const r=rows[i], b=Uint8Array.from(atob(r.data),c=>c.charCodeAt(0)), engine=WebAssembly.validate(b);
if((r.accepted&&!engine)||(r.exact&&r.accepted!==engine))throw Error("validation disagreement row "+i+" bytes="+r.data+" oak="+r.accepted+" engine="+engine);
}`
	// Node's -e is CommonJS, so avoid top-level await in the shared program.
	script = "(async()=>{" + script + "})().catch(e=>{console.error(e);" + "if(typeof Deno!==\"undefined\")Deno.exit(1);else process.exit(1);});"
	ctx, cancel := context.WithTimeout(t.Context(), 30*time.Second)
	defer cancel()
	cmd := engine.Command(ctx, script)
	cmd.Stdin = bytes.NewReader(data)
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("independent engine: %v\n%s", err, output)
	}
	t.Logf("%d byte cases, %d accepted; all accepted cases also validate in the engine", len(corpus), accepted)
}
