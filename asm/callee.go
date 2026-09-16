package asm

import (
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// ResolveNativeCallee binds one machine call symbol to the only Oak function
// whose native entry may carry that spelling on arch. Scalar functions use
// their exact Oak name. A fixed-vector function uses that exact name followed
// by the active lane's ABI suffix. Every ambiguous, cross-lane, or malformed
// mapping is refused.
func ResolveNativeCallee(arch, symbol string, callees map[string]*ast.FunctionStatement) (*ast.FunctionStatement, bool) {
	switch arch {
	case "", ArchArm64:
		arch = ArchArm64
	case ArchRV64:
	default:
		return nil, false
	}
	if symbol == "" || callees == nil {
		return nil, false
	}

	activeSuffix := VectorEntrySuffix(arch)
	oppositeSuffix := VectorEntrySuffix(ArchRV64)
	if arch == ArchRV64 {
		oppositeSuffix = VectorEntrySuffix(ArchArm64)
	}
	if strings.HasSuffix(symbol, oppositeSuffix) {
		return nil, false
	}
	if base, suffixed := strings.CutSuffix(symbol, activeSuffix); suffixed {
		if base == "" {
			return nil, false
		}
		if _, ambiguous := callees[symbol]; ambiguous {
			return nil, false
		}
		callee := callees[base]
		if !canonicalNativeCallee(callee, base) || !fixedVectorCallee(callee) {
			return nil, false
		}
		return callee, true
	}

	callee := callees[symbol]
	if !canonicalNativeCallee(callee, symbol) || fixedVectorCallee(callee) {
		return nil, false
	}
	return callee, true
}

func canonicalNativeCallee(callee *ast.FunctionStatement, name string) bool {
	if callee == nil || callee.Name == nil || callee.Name.Value != name ||
		reservedNativeCalleeName(name) || callee.Body == nil || callee.Receiver != nil ||
		len(callee.TypeParams) != 0 || callee.ExternSymbol != "" {
		return false
	}
	for _, parameter := range callee.Parameters {
		if parameter == nil || parameter.Name == nil || parameter.Type == nil {
			return false
		}
	}
	return true
}

func reservedNativeCalleeName(name string) bool {
	return strings.HasSuffix(name, VectorEntrySuffix(ArchArm64)) ||
		strings.HasSuffix(name, VectorEntrySuffix(ArchRV64))
}

func fixedVectorCallee(callee *ast.FunctionStatement) bool {
	if callee == nil {
		return false
	}
	for _, parameter := range callee.Parameters {
		if _, vector := vectorShape(parameter.Type); vector {
			return true
		}
	}
	_, vector := vectorShape(callee.ReturnType)
	return vector
}
