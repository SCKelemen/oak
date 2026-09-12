package typechecker

// Target constants (docs/spec/92-ffi.md section 2.11): a top-level binding
// whose value is a C constant the target's headers define —
//
//	CLOCK_MONOTONIC: c.Int = c.const("CLOCK_MONOTONIC", "<time.h>")
//
// The value is never known to Oak: the C backend emits the identifier and
// the C compiler resolves it per target, the interpreter rejects the
// program, and the Lean extraction treats the binding as an uninterpreted
// constant. What Oak checks is the shape — a `c.*` scalar annotation, a C
// identifier, a header spelling — so nothing but a validated identifier and
// a validated header name ever reaches the generated C.

import (
	"fmt"
	"regexp"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// CodeTargetConstant rejects a `c.const` anywhere but as the initializer
// of a top-level binding with a `c.*` scalar annotation, a malformed C
// identifier or header spelling, and a non-scalar annotation
// (docs/spec/92-ffi.md section 2.11).
const CodeTargetConstant = "OAK-F0114"

// TargetConstant is one checked `c.const` binding.
type TargetConstant struct {
	Name       string // the Oak binding
	Identifier string // the C identifier the target defines
	Header     string // the header that defines it, as spelled: <time.h> or "mine.h"
	Type       *CType // the c.* scalar annotation
}

// targetConstantTypes are the `c.*` members a target constant may carry:
// the integer scalars. Pointers and strings are not constants a header
// spells, and floats have no boundary constants in this increment.
var targetConstantTypes = map[string]bool{
	"Int": true, "UInt": true, "Int32": true, "UInt32": true, "Int64": true, "UInt64": true,
	"Long": true, "ULong": true, "Size": true,
}

// cHeaderPattern is the header grammar: angle-bracketed or quoted, path
// segments of identifier characters, dots and hyphens, separated by
// slashes. No spaces, no quotes inside, no parent-directory segments
// (checked separately), so the spelling is injection-free in `#include`.
var cHeaderPattern = regexp.MustCompile(`^(<[A-Za-z0-9_][A-Za-z0-9_.\-]*(/[A-Za-z0-9_][A-Za-z0-9_.\-]*)*>|"[A-Za-z0-9_][A-Za-z0-9_.\-]*(/[A-Za-z0-9_][A-Za-z0-9_.\-]*)*")$`)

// ValidCHeader reports whether header is a spelling `#include` may carry
// as written: `<name.h>`, `<sys/name.h>`, or `"name.h"`, with no `..`
// segment.
func ValidCHeader(header string) bool {
	if !cHeaderPattern.MatchString(header) {
		return false
	}
	inner := header[1 : len(header)-1]
	for _, segment := range strings.Split(inner, "/") {
		if segment == ".." || segment == "." {
			return false
		}
	}
	return true
}

// TargetConstantCall recognizes `c.const(...)` and returns the call.
func TargetConstantCall(expr ast.Expression) (*ast.InvocationExpression, bool) {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall {
		return nil, false
	}
	library, member, ok := libraryAccess(call.Function)
	if !ok || library != "c" || member != "const" {
		return nil, false
	}
	return call, true
}

// checkTargetConstant validates a top-level `NAME: c.T = c.const(id,
// header)` and records it. It reports whether the declaration was a target
// constant (valid or not); the caller binds the annotation's type either
// way so later code is checked against the declared type.
func (tc *TypeChecker) checkTargetConstant(stmt *ast.VariableDeclaration, call *ast.InvocationExpression, varType Type) {
	name := stmt.Name.Value
	scalar, isC := varType.(*CType)
	if !isC || !targetConstantTypes[scalar.Name] {
		d := tc.addTypeDiagnostic(stmt.Type, CodeTargetConstant,
			fmt.Sprintf("target constant %s must have a c.* integer type annotation, got %s", name, varType))
		d.AddNote("a target constant is a C integer the target's headers define; c.Ptr, c.String, and Oak types are not constants a header spells (docs/spec/92-ffi.md section 2.11)")
		return
	}
	if len(call.Arguments) != 2 {
		d := tc.addTypeDiagnostic(call, CodeTargetConstant,
			fmt.Sprintf("c.const takes a C identifier and a header, both string literals, got %d arguments", len(call.Arguments)))
		d.AddHelp("write NAME: c.Int = c.const(\"CLOCK_MONOTONIC\", \"<time.h>\")")
		return
	}
	identifierLiteral, isIdentifierLiteral := call.Arguments[0].(*ast.StringLiteral)
	if !isIdentifierLiteral || !ValidCSymbol(identifierLiteral.Value) {
		d := tc.addTypeDiagnostic(call.Arguments[0], CodeTargetConstant,
			"c.const: the constant must be a string literal that is a valid C identifier")
		d.AddNote("the identifier is emitted into generated C as written; the identifier grammar ([A-Za-z_][A-Za-z0-9_]*) is what makes that emission injection-free (docs/spec/92-ffi.md section 2.11)")
		return
	}
	headerLiteral, isHeaderLiteral := call.Arguments[1].(*ast.StringLiteral)
	if !isHeaderLiteral || !ValidCHeader(headerLiteral.Value) {
		d := tc.addTypeDiagnostic(call.Arguments[1], CodeTargetConstant,
			"c.const: the header must be a string literal spelled <name.h>, <dir/name.h>, or \"name.h\"")
		d.AddNote("the header is emitted as an #include line as written: identifier characters, dots, hyphens, and slashes only, no parent-directory segments (docs/spec/92-ffi.md section 2.11)")
		return
	}
	if tc.targetConstants == nil {
		tc.targetConstants = map[string]*TargetConstant{}
	}
	constant := &TargetConstant{Name: name, Identifier: identifierLiteral.Value, Header: headerLiteral.Value, Type: scalar}
	tc.targetConstants[name] = constant
	tc.targetConstantOrder = append(tc.targetConstantOrder, name)
}

// TargetConstants returns the checked target constants in declaration order.
func (tc *TypeChecker) TargetConstants() []*TargetConstant {
	out := make([]*TargetConstant, 0, len(tc.targetConstantOrder))
	for _, name := range tc.targetConstantOrder {
		out = append(out, tc.targetConstants[name])
	}
	return out
}

// TargetConstantOf returns the target constant bound to name, if any.
func (tc *TypeChecker) TargetConstantOf(name string) (*TargetConstant, bool) {
	constant, ok := tc.targetConstants[name]
	return constant, ok
}
