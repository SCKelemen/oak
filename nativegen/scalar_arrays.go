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

// scalarArrayLimit bounds the elements replaced: the pools give the
// first elements registers and the rest frame slots of their own, which
// cost what the array's did — so past the pools the gain is the elements
// that fit. Sixteen is a hash compression's state.
const scalarArrayLimit = 16

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
// expression or as len's argument, and no assignment rebinds the whole —
// or, once, as the body's result expression, which the lowering writes
// element by element into the result area (resultRecordExpr).
func scalarReplaceable(fn *ast.FunctionStatement, name string, length int64) bool {
	if fn == nil || fn.Body == nil || length <= 0 || length > scalarArrayLimit {
		return false
	}
	mentions, admitted := 0, 0
	ok := true
	if result, isResult := resultIdentifier(fn.Body); isResult && result == name {
		admitted++
	}
	walk(fn.Body, func(n ast.Node) {
		switch e := n.(type) {
		case *ast.Identifier:
			if e.Value == name {
				mentions++
			}
		case *ast.AssignmentStatement:
			if e.Name != nil && e.Name.Value == name {
				// The whole array assigned: admitted from an array literal
				// of its length (a permutation, `m = [16]u32{ m[2], … }`),
				// lowered as a parallel assignment of the elements
				// (assignScalarArray); anything else keeps the array.
				lit, isLiteral := arrayLiteralOf(e.Value)
				if !isLiteral || int64(len(lit.Elements)) != length {
					ok = false
				} else if _, isPermutation := permutationSources(name, length, lit); !isPermutation && length > scalarAssignLimit {
					ok = false // too many values to hold at once
				}
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
	if hidden, elem, found := g.loopArrayElement(e); found {
		return hidden, elem, true
	}
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

// resultIdentifier names the identifier a body yields as its result: the
// last statement's expression when it is a bare identifier.
func resultIdentifier(body ast.Expression) (string, bool) {
	block, isBlock := body.(*ast.BlockExpression)
	if !isBlock || block.Block == nil || len(block.Block.Statements) == 0 {
		return "", false
	}
	es, isExpr := block.Block.Statements[len(block.Block.Statements)-1].(*ast.ExpressionStatement)
	if !isExpr || es.Discard {
		return "", false
	}
	ident, isIdent := es.Expression.(*ast.Identifier)
	if !isIdent {
		return "", false
	}
	return ident.Value, true
}

// assignScalarArray lowers `name = [N]T{ e0, …, eN-1 }` over a replaced
// array as a parallel assignment: every element expression evaluates
// first (a permutation reads the elements it overwrites), then each
// hidden local takes its value.
func (g *generator) assignScalarArray(sa *scalarArray, s *ast.AssignmentStatement) error {
	lit, isLiteral := arrayLiteralOf(s.Value)
	if !isLiteral || int64(len(lit.Elements)) != sa.length {
		return unsupported("an assignment to the scalar-replaced array %s from %s", s.Name.Value, s.Value.String())
	}
	if source, isPermutation := permutationSources(s.Name.Value, sa.length, lit); isPermutation {
		return g.permuteScalarArray(sa, source)
	}
	values := make([]int, sa.length)
	for k := range lit.Elements {
		r, err := g.expr(lit.Elements[k], &sa.elem)
		if err != nil {
			return err
		}
		values[k] = r
	}
	for k, r := range values {
		g.assignVar(sa.names[k], r)
		g.killLoopFacts(sa.names[k])
	}
	return nil
}

// scalarAssignLimit bounds the elements a whole assignment from a general
// literal holds in scratch registers at once; a permutation of the
// array's own elements needs two, whatever its length.
const scalarAssignLimit = 8

// permutationSources reads a literal over the array's own elements at
// distinct constant indices — `[16]u32{ m[2], m[6], … }` — as the source
// index of each destination.
func permutationSources(name string, length int64, lit *ast.ArrayLiteral) ([]int64, bool) {
	source := make([]int64, length)
	seen := make([]bool, length)
	for destination, element := range lit.Elements {
		index, isIndex := element.(*ast.IndexExpression)
		if !isIndex || index.Dot || !isName(index.Left, name) {
			return nil, false
		}
		at, isConst := constantValue(index.Index)
		if !isConst || at < 0 || at >= length || seen[at] {
			return nil, false
		}
		source[destination] = at
		seen[at] = true
	}
	return source, true
}

// permuteScalarArray realizes new[i] = old[source[i]] over the hidden
// locals cycle by cycle: the cycle's first value saved in one scratch,
// each element then taking the next's, the last taking the saved one —
// two scratch registers, whatever the length; fixed points need nothing.
func (g *generator) permuteScalarArray(sa *scalarArray, source []int64) error {
	visited := make([]bool, len(source))
	for start := range source {
		if visited[start] {
			continue
		}
		visited[start] = true
		next := int(source[start])
		if next == start {
			continue
		}
		saved, err := g.alloc(sa.elem)
		if err != nil {
			return err
		}
		g.put(g.loadVar(sa.names[start], saved))
		current := start
		for next != start {
			work, err := g.alloc(sa.elem)
			if err != nil {
				return err
			}
			g.put(g.loadVar(sa.names[next], work))
			g.assignVar(sa.names[current], work)
			g.killLoopFacts(sa.names[current])
			current = next
			visited[current] = true
			next = int(source[current])
		}
		g.assignVar(sa.names[current], saved)
		g.killLoopFacts(sa.names[current])
	}
	return nil
}

// arrayLiteralOf reads an array literal, bare or as the one expression of
// a block — the shape an expanded helper leaves (`m = blake3_permute(m)`
// becomes `m = { [16]u32{ m[2], … } }`).
func arrayLiteralOf(value ast.Expression) (*ast.ArrayLiteral, bool) {
	if lit, isLiteral := value.(*ast.ArrayLiteral); isLiteral {
		return lit, true
	}
	block, isBlock := value.(*ast.BlockExpression)
	if !isBlock || block.Block == nil || len(block.Block.Statements) != 1 {
		return nil, false
	}
	es, isExpr := block.Block.Statements[0].(*ast.ExpressionStatement)
	if !isExpr || es.Discard {
		return nil, false
	}
	lit, isLiteral := es.Expression.(*ast.ArrayLiteral)
	return lit, isLiteral
}
