// Package playground is the bounded, filesystem-free single-file browser API.
package playground

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/wasm"
)

const MaxSourceBytes = 32768

type Response struct {
	Module        *wasm.Module `json:"module,omitempty"`
	Error         string       `json:"error,omitempty"`
	SourceSHA256  string       `json:"sourceSHA256"`
	ModuleSHA256  string       `json:"moduleSHA256,omitempty"`
	SourceChecked bool         `json:"sourceChecked"`
}

// Compile never runs user code, resolves imports or spawns external tools.
// The host must additionally enforce wall-clock cancellation (Worker.terminate
// in the browser); a source length limit is not a proof-search/time bound.
func Compile(source string) Response {
	var out Response
	if len(source) > MaxSourceBytes {
		out.Error = "source exceeds 32 KiB playground limit"
		return out
	}
	hash := sha256.Sum256([]byte(source))
	out.SourceSHA256 = hex.EncodeToString(hash[:])
	p := parser.New(layout.New(scanner.New(source)))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		out.Error = fmt.Sprint(errs)
		return out
	}
	// Refuse imports before the compiler's module resolver can see them.
	for _, stmt := range program.Statements {
		if _, ok := stmt.(*ast.FunctionStatement); !ok {
			out.Error = "playground scalar v0 accepts function declarations only; imports, globals and host bindings are unavailable"
			return out
		}
	}
	module, err := compiler.New().WithSource("playground.oak", source).EmitWasm().Get()
	if err != nil {
		out.Error = err.Error()
		return out
	}
	out.SourceChecked = true
	out.Module = &module
	hash = sha256.Sum256(module.Bytes)
	out.ModuleSHA256 = hex.EncodeToString(hash[:])
	return out
}
