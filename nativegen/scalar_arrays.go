package nativegen

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// Scalar replacement of small array locals (docs/spec/94-assembler.md §9,
// arrays in registers). An owned array local whose every use is an
// element at a literal index in range or `len` of it — never borrowed
// (`&buf`, `view`, `span`), passed whole, assigned whole, or indexed by a
// computed value — is a set of independent scalars: `acc: [8]f32` in a
// tiled reduction is eight accumulators. Such an array is lowered as its
// elements, each a hidden scalar local `name#k` declared through the
// ordinary scalar declaration (so it takes a register home from the same
// pools and the same liveness as the array), read in place under a binary
// operation, and written by the operation's own instruction (assignVar's
// retarget) — where the frame array cost a load and a store per element
// per iteration. The Oak side of the verifier models the array as an
// aggregate either way; the equivalence is over the same values.

// scalarArrayLimit bounds the elements replaced (the register pools).
const scalarArrayLimit = 8

// scalarArray is a replaced array: its element type, length, and the
// hidden names of its elements in index order.
type scalarArray struct {
	elem   scalar
	length int64
	names  []string
}

// scalarReplaceable reports whether every use of the array local name in
// the function body is an element at a constant index in [0, length) or
// `len(name)`: the identifier appears only as the left of such an index
// expression or as len's argument, and no assignment rebinds the whole.
func scalarReplaceable(fn *ast.FunctionStatement, name string, length int64) bool {
	if fn == nil || fn.Body == nil || length <= 0 || length > scalarArrayLimit {
		return false
	}
	mentions, admitted := 0, 0
	ok := true
	walk(fn.Body, func(n ast.Node) {
		switch e := n.(type) {
		case *ast.Identifier:
			if e.Value == name {
				mentions++
			}
		case *ast.AssignmentStatement:
			if e.Name != nil && e.Name.Value == name {
				ok = false // the whole array assigned
			}
		case *ast.IndexExpression:
			if ident, isIdent := e.Left.(*ast.Identifier); isIdent && ident.Value == name && !e.Dot {
				if k, isConst := constantValue(e.Index); isConst && k >= 0 && k < length {
					admitted++
				} else {
					ok = false
				}
			}
		case *ast.InvocationExpression:
			if fn, isIdent := e.Function.(*ast.Identifier); isIdent && fn.Value == "len" && len(e.Arguments) == 1 {
				if arg, argIsIdent := e.Arguments[0].(*ast.Identifier); argIsIdent && arg.Value == name {
					admitted++
				}
			}
		}
	})
	return ok && mentions == admitted
}

// elementName is the hidden scalar local holding element k.
func elementName(name string, k int64) string { return fmt.Sprintf("%s#%d", name, k) }

// scalarElement recognizes `name[k]` over a replaced array at a constant
// index: the hidden local's name.
func (g *generator) scalarElement(e *ast.IndexExpression) (string, scalar, bool) {
	if e == nil || e.Dot {
		return "", scalar{}, false
	}
	ident, isIdent := e.Left.(*ast.Identifier)
	if !isIdent {
		return "", scalar{}, false
	}
	sa, isScalar := g.scalarArrays[ident.Value]
	if !isScalar {
		return "", scalar{}, false
	}
	k, isConst := constantValue(e.Index)
	if !isConst || k < 0 || k >= sa.length {
		return "", scalar{}, false
	}
	return sa.names[k], sa.elem, true
}

// declareScalarArray lowers a replaceable array declaration as its
// elements: each hidden local declared and given its initializer's
// element (or zero), the array's liveness shared with every element.
func (g *generator) declareScalarArray(s *ast.VariableDeclaration, elem scalar, length int64, literal *ast.ArrayLiteral) error {
	name := s.Name.Value
	if elem.isFloat {
		g.usedFloat = true
	}
	sa := &scalarArray{elem: elem, length: length, names: make([]string, length)}
	// A prior binding of the name (a sibling scope's array) is shadowed.
	delete(g.arrays, name)
	delete(g.slots, name)
	delete(g.types, name)
	delete(g.regs, name)
	for k := int64(0); k < length; k++ {
		hidden := elementName(name, k)
		sa.names[k] = hidden
		if g.lv != nil {
			// The element lives as long as the array: the liveness
			// pre-pass knows the array's name only.
			if at, seen := g.lv.decl[name]; seen {
				g.lv.decl[hidden] = at
			}
			if last, read := g.lv.lastUse[name]; read {
				g.lv.lastUse[hidden] = last
			}
		}
		g.declare(hidden, elem)
		var r int
		var err error
		if literal != nil {
			r, err = g.expr(literal.Elements[k], &elem)
		} else if elem.isFloat {
			r, err = g.alloc(elem)
			if err == nil {
				err = g.floatConstant(r, 0, elem)
			}
		} else {
			r, err = g.alloc(elem)
			if err == nil {
				g.emit("mov", reg(r, elem), imm(0))
			}
		}
		if err != nil {
			return err
		}
		g.assignVar(hidden, r)
	}
	if g.scalarArrays == nil {
		g.scalarArrays = map[string]*scalarArray{}
	}
	g.scalarArrays[name] = sa
	g.scopes[len(g.scopes)-1][name] = slotBinding{offset: -1, reg: -1, sa: sa}
	return nil
}
