//go:build js && wasm

package main

import (
	"encoding/json"
	"syscall/js"

	"github.com/SCKelemen/oak/playground"
)

func main() {
	compile := js.FuncOf(func(this js.Value, args []js.Value) any {
		if len(args) != 1 || args[0].Type() != js.TypeString {
			return `{"error":"expected source text"}`
		}
		result := playground.Compile(args[0].String())
		data, err := json.Marshal(result)
		if err != nil {
			return `{"error":"cannot encode compiler response"}`
		}
		return string(data)
	})
	js.Global().Set("oakCompile", compile)
	if ready := js.Global().Get("oakCompilerReady"); ready.Type() == js.TypeFunction {
		ready.Invoke()
	}
	select {}
}
