package metal

// Thread independence (docs/spec/56-kernels.md section 6, 55-parallelism.md
// section 2): a launch runs the kernel body once per grid position, in any
// order and interleaved, so the positions must not communicate through the
// buffers — each position's span writes are disjoint from every other
// position's span reads and writes. Oak.Kernel.run_perm is the theorem
// that then makes the launch equal to the sequential host loop; this file
// is the checker rule that discharges its hypothesis for the two shapes a
// kernel author writes, failing closed on every other:
//
//   - one element per thread: every span access is at index `gid`;
//   - a tile per thread: every span access is at `gid * T + k` (either
//     operand order, or through a local `base: u32 = gid * T`), where `k`
//     is the counter of an enclosing `while k < T` loop and `T` is a
//     scalar parameter or a literal.
//
// Views are read-only and impose nothing. The fault word is shared by
// design and is not a buffer of the program. A span handed to a helper
// takes its accesses out of the kernel's sight and fails closed.

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// IndependenceError reports a kernel whose span accesses the checker cannot
// prove independent across grid positions (OAK-K0104).
type IndependenceError struct{ Msg string }

func (e *IndependenceError) Error() string { return e.Msg }

// independence checks one kernel and returns the shape it discharged
// ("element", or "tile T"); the error names the access that breaks the
// rule. Called after the kernel's parameters are classified.
func (em *emitter) independence(fn *ast.FunctionStatement) (string, error) {
	gid := fn.Parameters[0].Name.Value
	spans := map[string]bool{}
	scalars := map[string]bool{}
	spanRecords := map[string]bool{}
	for i, p := range fn.Parameters {
		if i == 0 || p == nil || p.Name == nil {
			continue
		}
		t, err := em.paramType(fn, i)
		if err != nil {
			return "", nil // the subset check reports the type
		}
		switch t.kind {
		case "span":
			spans[p.Name.Value] = true
		case "scalar":
			scalars[p.Name.Value] = true
		case "record":
			// A span field is a span named `p.field`; a record holding
			// one cannot be handed to a helper or copied (its indices
			// would leave the kernel's sight).
			for _, f := range em.records[t.record] {
				if f.typ.kind == "span" {
					spans[p.Name.Value+"."+f.name] = true
					spanRecords[p.Name.Value] = true
				}
			}
		}
	}
	in := &independenceWalk{gid: gid, spans: spans, scalars: scalars, spanRecords: spanRecords, tileBases: map[string]string{}, tileIndices: map[string]string{}, functions: em.functions, body: fn.Body, shape: "element"}
	if len(spans) == 0 {
		return in.shape, nil
	}
	if assignsName(fn.Body, gid) {
		return "", in.fail(fn.Name, "the grid position %s is reassigned; positions could overlap", gid)
	}
	var err error
	if body, ok := fn.Body.(*ast.BlockExpression); ok && body.Block != nil {
		err = in.block(body.Block.Statements, nil)
	} else {
		err = in.expr(fn.Body, nil)
	}
	if err != nil {
		return "", err
	}
	return in.shape, nil
}

type independenceWalk struct {
	gid         string
	spans       map[string]bool
	scalars     map[string]bool
	spanRecords map[string]bool
	// tileBases maps a local never reassigned to T for `local = gid * T`;
	// tileIndices names locals never reassigned that hold `gid * T + k`
	// under a loop bounding k by T, so `y[i]` is the tile shape by name.
	tileBases   map[string]string
	tileIndices map[string]string
	functions   map[string]*ast.FunctionStatement
	body        ast.Node
	// shape is "element" until a tile access is admitted, then "tile T".
	shape string
}

// loopBound is an enclosing `while k < T` in scope.
type loopBound struct{ counter, bound string }

func (in *independenceWalk) fail(node ast.Node, format string, args ...interface{}) error {
	return &IndependenceError{Msg: fmt.Sprintf("%s (at %s)", fmt.Sprintf(format, args...), node.String())}
}

func (in *independenceWalk) block(stmts []ast.Statement, loops []loopBound) error {
	for _, s := range stmts {
		if err := in.stmt(s, loops); err != nil {
			return err
		}
	}
	return nil
}

func (in *independenceWalk) stmt(s ast.Statement, loops []loopBound) error {
	switch v := s.(type) {
	case *ast.VariableDeclaration:
		if v.Name != nil && v.Value != nil {
			// A local that windows or aliases a span hides the index the
			// shapes are judged on; index the span parameter directly.
			if src, isSpanLocal := in.spanSource(v.Value); isSpanLocal {
				return in.fail(v, "local %s windows the span %s, hiding its indices; index the span parameter in the kernel body", v.Name.Value, src)
			}
			if !assignsName(in.body, v.Name.Value) {
				if t, ok := in.tileProduct(v.Value); ok {
					in.tileBases[v.Name.Value] = t
				}
				if t, ok := in.tileIndex(v.Value, loops); ok {
					in.tileIndices[v.Name.Value] = t
				}
			}
			return in.expr(v.Value, loops)
		}
		return nil
	case *ast.AssignmentStatement:
		return in.expr(v.Value, loops)
	case *ast.IndexAssignmentStatement:
		if err := in.access(v.Target, loops); err != nil {
			return err
		}
		return in.expr(v.Value, loops)
	case *ast.WhileStatement:
		if err := in.expr(v.Condition, loops); err != nil {
			return err
		}
		// The bound holds for the body only when the counter changes as
		// the body's last statement and nothing else (the canonical shape
		// the loop rule already requires) and the bound is never assigned.
		inner := loops
		if counter, bound, ok := in.counterBound(v.Condition); ok && !assignsName(in.body, bound) && counterOnlyLast(v.Body, counter) {
			inner = append(append([]loopBound{}, loops...), loopBound{counter, bound})
		}
		if v.Body != nil {
			return in.block(v.Body.Statements, inner)
		}
		return nil
	case *ast.ExpressionStatement:
		return in.expr(v.Expression, loops)
	case *ast.BlockStatement:
		return in.block(v.Statements, loops)
	}
	return nil
}

func (in *independenceWalk) expr(e ast.Expression, loops []loopBound) error {
	switch v := e.(type) {
	case nil:
		return nil
	case *ast.IndexExpression:
		if v.Dot {
			return nil
		}
		if err := in.access(v, loops); err != nil {
			return err
		}
		return in.expr(v.Index, loops)
	case *ast.InvocationExpression:
		if callee, ok := v.Function.(*ast.Identifier); ok {
			if target := in.functions[callee.Value]; target != nil {
				for _, a := range v.Arguments {
					if id, isIdent := a.(*ast.Identifier); isIdent && (in.spans[id.Value] || in.spanRecords[id.Value]) {
						return in.fail(v, "span %s is handed to %s, whose accesses the kernel cannot see; index the span in the kernel body", id.Value, callee.Value)
					}
					if key, isField := in.spanField(a); isField {
						return in.fail(v, "span field %s is handed to %s, whose accesses the kernel cannot see; index it in the kernel body", key, callee.Value)
					}
				}
			}
		}
		for _, a := range v.Arguments {
			if err := in.expr(a, loops); err != nil {
				return err
			}
		}
		return nil
	case *ast.InfixExpression:
		if err := in.expr(v.Left, loops); err != nil {
			return err
		}
		return in.expr(v.Right, loops)
	case *ast.PrefixExpression:
		return in.expr(v.Right, loops)
	case *ast.MatchExpression:
		if err := in.expr(v.Scrutinee, loops); err != nil {
			return err
		}
		for _, arm := range v.Arms {
			if err := in.expr(arm.Body, loops); err != nil {
				return err
			}
		}
		return nil
	case *ast.BlockExpression:
		if v.Block != nil {
			return in.block(v.Block.Statements, loops)
		}
		return nil
	}
	return nil
}

// spanField renders `p.field` for a span field of a record parameter.
func (in *independenceWalk) spanField(e ast.Expression) (string, bool) {
	dot, ok := e.(*ast.IndexExpression)
	if !ok || !dot.Dot {
		return "", false
	}
	base, ok := dot.Left.(*ast.Identifier)
	field, isField := dot.Index.(*ast.Identifier)
	if !ok || !isField {
		return "", false
	}
	key := base.Value + "." + field.Value
	return key, in.spans[key]
}

// access checks one span index against the two shapes.
func (in *independenceWalk) access(ix *ast.IndexExpression, loops []loopBound) error {
	name := ""
	if base, ok := ix.Left.(*ast.Identifier); ok && in.spans[base.Value] {
		name = base.Value
	} else if key, isField := in.spanField(ix.Left); isField {
		name = key
	}
	if name == "" {
		return nil
	}
	base := &ast.Identifier{Value: name}
	if id, isIdent := ix.Index.(*ast.Identifier); isIdent && id.Value == in.gid {
		return nil
	}
	if id, isIdent := ix.Index.(*ast.Identifier); isIdent && in.tileIndices[id.Value] != "" {
		in.shape = "tile " + in.tileIndices[id.Value]
		return nil
	}
	if t, ok := in.tileIndex(ix.Index, loops); ok {
		in.shape = "tile " + t
		return nil
	}
	return in.fail(ix, "span %s is accessed at %s, which is neither the grid position nor gid * T + k under a loop `while k < T`; positions could overlap", base.Value, ix.Index.String())
}

// tileProduct recognizes `gid * T` or `T * gid` with T a scalar parameter
// or a literal, returning T's spelling.
func (in *independenceWalk) tileProduct(e ast.Expression) (string, bool) {
	inf, ok := e.(*ast.InfixExpression)
	if !ok || inf.Operator != "*" {
		return "", false
	}
	for _, pair := range [][2]ast.Expression{{inf.Left, inf.Right}, {inf.Right, inf.Left}} {
		if id, isIdent := pair[0].(*ast.Identifier); isIdent && id.Value == in.gid {
			if t, isT := in.tileWidth(pair[1]); isT {
				return t, true
			}
		}
	}
	return "", false
}

// tileWidth admits a scalar parameter (never assigned in a kernel body:
// parameters are constant references) or an integer literal.
func (in *independenceWalk) tileWidth(e ast.Expression) (string, bool) {
	switch v := e.(type) {
	case *ast.Identifier:
		if in.scalars[v.Value] {
			return v.Value, true
		}
	case *ast.IntegerLiteral:
		return fmt.Sprint(v.Value), true
	}
	return "", false
}

// tileIndex recognizes `gid * T + k`, `k + gid * T`, `base + k`, `k + base`
// with base a recorded tile base of T and k a counter bounded by T,
// returning T.
func (in *independenceWalk) tileIndex(e ast.Expression, loops []loopBound) (string, bool) {
	inf, ok := e.(*ast.InfixExpression)
	if !ok || inf.Operator != "+" {
		return "", false
	}
	for _, pair := range [][2]ast.Expression{{inf.Left, inf.Right}, {inf.Right, inf.Left}} {
		t, isBase := in.tileProduct(pair[0])
		if !isBase {
			if id, isIdent := pair[0].(*ast.Identifier); isIdent {
				t, isBase = in.tileBases[id.Value]
			}
		}
		if !isBase {
			continue
		}
		k, isIdent := pair[1].(*ast.Identifier)
		if !isIdent {
			continue
		}
		for _, l := range loops {
			if l.counter == k.Value && l.bound == t {
				return t, true
			}
		}
	}
	return "", false
}

// counterBound reads `k < T` from a loop condition.
func (in *independenceWalk) counterBound(cond ast.Expression) (string, string, bool) {
	inf, ok := cond.(*ast.InfixExpression)
	if !ok || inf.Operator != "<" {
		return "", "", false
	}
	k, isIdent := inf.Left.(*ast.Identifier)
	if !isIdent {
		return "", "", false
	}
	t, isT := in.tileWidth(inf.Right)
	if !isT {
		return "", "", false
	}
	return k.Value, t, true
}

// spanSource names the span a declaration's value windows or aliases.
func (in *independenceWalk) spanSource(value ast.Expression) (string, bool) {
	switch v := value.(type) {
	case *ast.Identifier:
		if in.spans[v.Value] || in.spanRecords[v.Value] {
			return v.Value, true
		}
	case *ast.IndexExpression:
		if key, isField := in.spanField(v); isField {
			return key, true
		}
	case *ast.InvocationExpression:
		if callee, ok := v.Function.(*ast.Identifier); ok && callee.Value == "subslice" && len(v.Arguments) == 3 {
			if base, ok := v.Arguments[0].(*ast.Identifier); ok && in.spans[base.Value] {
				return base.Value, true
			}
			if key, isField := in.spanField(v.Arguments[0]); isField {
				return key, true
			}
		}
	case *ast.RecordLiteral:
		for _, f := range v.FieldOrder {
			if src, ok := in.spanSource(f.Value); ok {
				return src, true
			}
		}
	}
	return "", false
}

// assignsName reports whether a body assigns (not declares) the binding.
func assignsName(body ast.Node, name string) bool {
	found := false
	walk(body, func(n ast.Node) {
		if v, ok := n.(*ast.AssignmentStatement); ok && v.Name != nil && v.Name.Value == name {
			found = true
		}
	})
	return found
}

// counterOnlyLast reports whether the loop body assigns the counter exactly
// once, as its final statement, so every access in the body runs under the
// condition's most recent evaluation.
func counterOnlyLast(body *ast.BlockStatement, counter string) bool {
	if body == nil || len(body.Statements) == 0 {
		return false
	}
	last, ok := body.Statements[len(body.Statements)-1].(*ast.AssignmentStatement)
	if !ok || last.Name == nil || last.Name.Value != counter {
		return false
	}
	count := 0
	walk(body, func(n ast.Node) {
		if v, ok := n.(*ast.AssignmentStatement); ok && v.Name != nil && v.Name.Value == counter {
			count++
		}
	})
	return count == 1
}
