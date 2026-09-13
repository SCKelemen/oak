// Package hostform rewrites a kernel that uses lanes, threadgroup memory,
// or barriers into the form the host runs (docs/spec/56-kernels.md section
// 2a). On the device a kernel body runs once per thread; on the host the
// same body runs once per lane per position, phase by phase: the body's
// top-level statements are split at each `barrier()`, every phase runs for
// lanes 0 .. G-1 in order, `lane(G)` is the lane counter, a threadgroup
// array is one array per position declared before the phases, and a
// local declared in one phase and read in a later one is privatized as a
// [G]T array indexed by the lane. The C backend and the interpreter apply
// this one rewrite, so they agree lane for lane; the Metal emitter reads
// the original. Oak.Kernel.phases_perm is the theorem that the phase-major
// order computes what the device computes when each phase's lanes are
// independent.
package hostform

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// LaneVar is the host form's lane counter.
const LaneVar = "oak_lane"

// Uses reports whether a kernel body mentions lanes, barriers, or
// threadgroup memory, so an ordinary kernel is left untouched.
func Uses(fn *ast.FunctionStatement) bool {
	if fn == nil || !fn.Kernel || fn.Body == nil {
		return false
	}
	used := false
	walkNodes(fn.Body, func(n ast.Node) {
		switch v := n.(type) {
		case *ast.InvocationExpression:
			if id, ok := v.Function.(*ast.Identifier); ok && (id.Value == "lane" || id.Value == "barrier" || id.Value == "simd_shuffle_xor") {
				used = true
			}
		case *ast.VariableDeclaration:
			if v.Threadgroup {
				used = true
			}
		}
	})
	return used
}

// GroupSize is the group size a kernel's lane(G) calls name, 0 when it has
// none; every call must name the same literal.
func GroupSize(fn *ast.FunctionStatement) (int64, error) {
	var size int64
	var err error
	walkNodes(fn.Body, func(n ast.Node) {
		call, ok := n.(*ast.InvocationExpression)
		if !ok || err != nil {
			return
		}
		id, ok := call.Function.(*ast.Identifier)
		if !ok || id.Value != "lane" {
			return
		}
		if len(call.Arguments) != 1 {
			err = fmt.Errorf("lane takes the group size, an integer literal")
			return
		}
		lit, ok := call.Arguments[0].(*ast.IntegerLiteral)
		if !ok || lit.Value < 1 || lit.Value > 1024 || lit.Value&(lit.Value-1) != 0 {
			err = fmt.Errorf("lane(%s): the group size is an integer literal, a power of two up to 1024", call.Arguments[0].String())
			return
		}
		if size != 0 && size != lit.Value {
			err = fmt.Errorf("one kernel has one group size, got lane(%d) and lane(%d)", size, lit.Value)
			return
		}
		size = lit.Value
	})
	return size, err
}

// Check validates the placement rules the rewrite relies on and returns
// the errors the kernel analysis reports (OAK-K0101): barrier() only at
// the body's top level, threadgroup arrays only at the top level with no
// lane-dependent initializer, a group size when either is used, and a
// type annotation on every local that lives across a barrier.
func Check(fn *ast.FunctionStatement) error {
	if !Uses(fn) {
		return nil
	}
	size, err := GroupSize(fn)
	if err != nil {
		return err
	}
	if size == 0 {
		return fmt.Errorf("a kernel with barrier() or threadgroup memory declares its group through lane(G)")
	}
	block, ok := fn.Body.(*ast.BlockExpression)
	if !ok || block.Block == nil {
		return fmt.Errorf("a kernel with lanes has a block body")
	}
	top := map[ast.Node]bool{}
	topShuffle := map[ast.Node]bool{} // shuffle calls whose statement is top-level
	topLocals := map[string]*ast.VariableDeclaration{}
	for _, s := range block.Block.Statements {
		top[s] = true
		if es, isExpr := s.(*ast.ExpressionStatement); isExpr {
			top[es.Expression] = true
		}
		if decl, isDecl := s.(*ast.VariableDeclaration); isDecl && decl.Name != nil {
			topLocals[decl.Name.Value] = decl
		}
		for _, call := range shufflesIn(s) {
			topShuffle[call] = true
		}
	}
	walkNodes(fn.Body, func(n ast.Node) {
		if err != nil {
			return
		}
		switch v := n.(type) {
		case *ast.InvocationExpression:
			if id, ok := v.Function.(*ast.Identifier); ok && id.Value == "barrier" && !top[v] {
				err = fmt.Errorf("barrier() is a statement at the kernel body's top level, not inside a loop, a conditional, or an expression")
			}
			if id, ok := v.Function.(*ast.Identifier); ok && id.Value == "simd_shuffle_xor" {
				// A shuffle reads another lane at a point every lane has
				// reached: its statement is at the top level, its source a
				// top-level scalar local declared before it.
				if !topShuffle[v] {
					err = fmt.Errorf("simd_shuffle_xor is used in a statement at the kernel body's top level, not inside a loop or a conditional")
				} else if src, isIdent := v.Arguments[0].(*ast.Identifier); !isIdent || topLocals[src.Value] == nil {
					err = fmt.Errorf("simd_shuffle_xor shuffles a scalar local declared at the kernel body's top level, got %s", v.Arguments[0].String())
				} else if _, isArray := topLocals[src.Value].Type.(*ast.IndexExpression); isArray || topLocals[src.Value].Type == nil {
					err = fmt.Errorf("simd_shuffle_xor's source %s needs a scalar type annotation (it is private to each lane)", src.Value)
				} else if off, isLit := v.Arguments[1].(*ast.IntegerLiteral); !isLit || off.Value >= size {
					err = fmt.Errorf("simd_shuffle_xor's offset is a literal below the group size %d", size)
				}
			}
		case *ast.VariableDeclaration:
			if v.Threadgroup {
				if !top[v] {
					err = fmt.Errorf("threadgroup memory %s is declared at the kernel body's top level", v.Name.Value)
				} else if v.Value != nil && mentionsLane(v.Value) {
					err = fmt.Errorf("threadgroup memory %s is initialized the same for every lane; it cannot mention lane()", v.Name.Value)
				} else if _, isArray := v.Type.(*ast.IndexExpression); !isArray || v.Type.(*ast.IndexExpression).Dot {
					err = fmt.Errorf("threadgroup memory %s is a fixed array, [N]T", v.Name.Value)
				}
			}
		}
	})
	if err != nil {
		return err
	}
	_, err = plan(fn, size)
	return err
}

// Rewrite returns the host form of a kernel, or the kernel itself when it
// uses no lanes, barriers, or threadgroup memory. An error is one Check
// reports; callers that run after the analysis may ignore it.
func Rewrite(fn *ast.FunctionStatement) (*ast.FunctionStatement, error) {
	if !Uses(fn) {
		return fn, nil
	}
	if err := Check(fn); err != nil {
		return nil, err
	}
	size, _ := GroupSize(fn)
	p, err := plan(fn, size)
	if err != nil {
		return nil, err
	}
	tok := fn.Token
	u32 := func() *ast.Identifier { return &ast.Identifier{Token: tok, Value: "u32"} }
	laneID := func() *ast.Identifier { return &ast.Identifier{Token: tok, Value: LaneVar} }
	lit := func(v int64) *ast.IntegerLiteral { return &ast.IntegerLiteral{Token: tok, Value: v} }
	var out []ast.Statement
	// Threadgroup memory and the privatized locals come first: one array
	// per position, shared by every lane of every phase.
	for _, arena := range p.arenas {
		decl := *arena
		decl.Threadgroup = false
		out = append(out, &decl)
	}
	for _, name := range p.privateOrder {
		decl := p.private[name]
		out = append(out, &ast.VariableDeclaration{Token: tok, Name: &ast.Identifier{Token: tok, Value: privateName(name)},
			Type: &ast.IndexExpression{Token: tok, Left: decl.Type, Index: lit(size)}})
	}
	for _, sh := range p.shuffles {
		decl := p.private[sh.source]
		out = append(out, &ast.VariableDeclaration{Token: tok, Name: &ast.Identifier{Token: tok, Value: sh.temp},
			Type: &ast.IndexExpression{Token: tok, Left: decl.Type, Index: lit(size)}})
	}
	out = append(out, &ast.VariableDeclaration{Token: tok, Name: laneID(), Type: u32(), Value: lit(0)})
	rw := &rewriter{size: size, private: p.private, tok: tok, temps: map[*ast.InvocationExpression]string{}}
	for _, sh := range p.shuffles {
		rw.temps[sh.call] = sh.temp
	}
	for i, phase := range p.phases {
		if i > 0 {
			out = append(out, &ast.AssignmentStatement{Token: tok, Name: laneID(), Value: lit(0)})
		}
		var body []ast.Statement
		for _, s := range phase {
			body = append(body, rw.stmt(s)...)
		}
		body = append(body, &ast.AssignmentStatement{Token: tok, Name: laneID(),
			Value: &ast.InfixExpression{Token: tok, Operator: "+", Left: laneID(), Right: lit(1)}})
		out = append(out, &ast.WhileStatement{Token: tok,
			Condition: &ast.InfixExpression{Token: token.Token{TokenKind: token.LCHEV, Literal: "<"}, Operator: "<", Left: laneID(), Right: lit(size)},
			Body:      &ast.BlockStatement{Token: tok, Statements: body}})
	}
	host := *fn
	host.Body = &ast.BlockExpression{Token: tok, Block: &ast.BlockStatement{Token: tok, Statements: out}}
	return &host, nil
}

// hostPlan is the shape of a kernel's host form: its phases, threadgroup
// arrays, and the locals that live across a barrier.
type hostPlan struct {
	phases       [][]ast.Statement
	arenas       []*ast.VariableDeclaration
	private      map[string]*ast.VariableDeclaration
	privateOrder []string
	shuffles     []shuffle
}

// shuffle is one simd_shuffle_xor call: its source local and the per-lane
// temp that holds the partner's value across the phase boundary.
type shuffle struct {
	call   *ast.InvocationExpression
	source string
	temp   string
}

// shufflesIn lists the simd_shuffle_xor calls a statement makes directly
// — in its own expressions, not inside a loop body, a conditional's arm,
// or a nested block, where a shuffle is refused (Check).
func shufflesIn(s ast.Statement) []*ast.InvocationExpression {
	var out []*ast.InvocationExpression
	var expr func(e ast.Expression)
	expr = func(e ast.Expression) {
		switch v := e.(type) {
		case nil:
		case *ast.InvocationExpression:
			if id, ok := v.Function.(*ast.Identifier); ok && id.Value == "simd_shuffle_xor" && len(v.Arguments) == 2 {
				out = append(out, v)
			}
			for _, a := range v.Arguments {
				expr(a)
			}
		case *ast.InfixExpression:
			expr(v.Left)
			expr(v.Right)
		case *ast.PrefixExpression:
			expr(v.Right)
		case *ast.IndexExpression:
			expr(v.Left)
			if !v.Dot {
				expr(v.Index)
			}
		case *ast.ArrayLiteral:
			for _, el := range v.Elements {
				expr(el)
			}
		}
	}
	switch v := s.(type) {
	case *ast.VariableDeclaration:
		expr(v.Value)
	case *ast.AssignmentStatement:
		expr(v.Value)
	case *ast.IndexAssignmentStatement:
		expr(v.Target)
		expr(v.Value)
	case *ast.ExpressionStatement:
		expr(v.Expression)
	}
	return out
}

func plan(fn *ast.FunctionStatement, size int64) (*hostPlan, error) {
	block := fn.Body.(*ast.BlockExpression).Block
	p := &hostPlan{private: map[string]*ast.VariableDeclaration{}}
	var phase []ast.Statement
	declaredIn := map[string]int{} // top-level local -> phase index
	decls := map[string]*ast.VariableDeclaration{}
	for _, s := range block.Statements {
		if es, ok := s.(*ast.ExpressionStatement); ok {
			if call, isCall := es.Expression.(*ast.InvocationExpression); isCall {
				if id, isIdent := call.Function.(*ast.Identifier); isIdent && id.Value == "barrier" {
					p.phases = append(p.phases, phase)
					phase = nil
					continue
				}
			}
		}
		if shuffles := shufflesIn(s); len(shuffles) > 0 {
			// The statement reads other lanes: every lane has finished
			// the statements before it (a phase ends), the partners' slots
			// are read into per-lane temps in a phase of their own (so a
			// lane that also writes its source in this statement cannot
			// be read early), and the statement runs in the next phase.
			p.phases = append(p.phases, phase)
			var reads []ast.Statement
			for _, call := range shuffles {
				src := call.Arguments[0].(*ast.Identifier)
				p.shuffles = append(p.shuffles, shuffle{call: call, source: src.Value, temp: fmt.Sprintf("oak_sh%d", len(p.shuffles)+1)})
				// The read is spelled as the shuffle call in statement
				// position; the rewriter turns it into temp[lane] = source[lane ^ off].
				reads = append(reads, &ast.ExpressionStatement{Token: call.Token, Expression: call})
				if _, done := p.private[src.Value]; !done {
					p.private[src.Value] = decls[src.Value]
					p.privateOrder = append(p.privateOrder, src.Value)
				}
			}
			p.phases = append(p.phases, reads)
			phase = nil
		}
		if decl, ok := s.(*ast.VariableDeclaration); ok && decl.Threadgroup {
			p.arenas = append(p.arenas, decl)
			continue
		}
		if decl, ok := s.(*ast.VariableDeclaration); ok && decl.Name != nil {
			declaredIn[decl.Name.Value] = len(p.phases)
			decls[decl.Name.Value] = decl
		}
		phase = append(phase, s)
	}
	p.phases = append(p.phases, phase)
	// A local read or written in a phase after its declaration's is
	// private to its lane across the barrier.
	for i, ph := range p.phases {
		for _, s := range ph {
			walkNodes(s, func(n ast.Node) {
				name := ""
				switch v := n.(type) {
				case *ast.Identifier:
					name = v.Value
				case *ast.AssignmentStatement:
					name = v.Name.Value
				}
				if name == "" {
					return
				}
				if at, declared := declaredIn[name]; declared && at < i {
					if _, done := p.private[name]; !done {
						p.private[name] = decls[name]
						p.privateOrder = append(p.privateOrder, name)
					}
				}
			})
		}
	}
	for _, name := range p.privateOrder {
		decl := p.private[name]
		if decl.Type == nil {
			return nil, fmt.Errorf("local %s lives across a barrier and needs a type annotation (it is private to each lane)", name)
		}
		if _, isArray := decl.Type.(*ast.IndexExpression); isArray {
			return nil, fmt.Errorf("local array %s lives across a barrier; declare it (threadgroup) or keep it inside one phase", name)
		}
	}
	return p, nil
}

func privateName(name string) string { return "oak_priv_" + name }

// rewriter substitutes lane(G) by the lane counter and privatized locals
// by their lane's slot, copying the statements it changes.
type rewriter struct {
	size    int64
	private map[string]*ast.VariableDeclaration
	tok     token.Token
	temps   map[*ast.InvocationExpression]string
}

func (rw *rewriter) laneRef() ast.Expression {
	return &ast.Identifier{Token: rw.tok, Value: LaneVar}
}

func (rw *rewriter) slot(name string) *ast.IndexExpression {
	return &ast.IndexExpression{Token: rw.tok, Left: &ast.Identifier{Token: rw.tok, Value: privateName(name)}, Index: rw.laneRef()}
}

func (rw *rewriter) stmt(s ast.Statement) []ast.Statement {
	switch v := s.(type) {
	case *ast.VariableDeclaration:
		if _, isPrivate := rw.private[v.Name.Value]; isPrivate {
			// The declaration becomes the lane's slot taking the value;
			// a value-less one is the zero the array already holds.
			if v.Value == nil {
				return nil
			}
			return []ast.Statement{&ast.IndexAssignmentStatement{Token: v.Token, Target: rw.slot(v.Name.Value), Value: rw.expr(v.Value)}}
		}
		d := *v
		d.Value = rw.expr(v.Value)
		return []ast.Statement{&d}
	case *ast.AssignmentStatement:
		if _, isPrivate := rw.private[v.Name.Value]; isPrivate {
			return []ast.Statement{&ast.IndexAssignmentStatement{Token: v.Token, Target: rw.slot(v.Name.Value), Value: rw.expr(v.Value)}}
		}
		a := *v
		a.Value = rw.expr(v.Value)
		return []ast.Statement{&a}
	case *ast.IndexAssignmentStatement:
		a := *v
		target := *v.Target
		target.Left = rw.expr(v.Target.Left)
		target.Index = rw.expr(v.Target.Index)
		a.Target = &target
		a.Value = rw.expr(v.Value)
		return []ast.Statement{&a}
	case *ast.WhileStatement:
		w := *v
		w.Condition = rw.expr(v.Condition)
		w.Body = rw.block(v.Body)
		return []ast.Statement{&w}
	case *ast.ExpressionStatement:
		if call, isCall := v.Expression.(*ast.InvocationExpression); isCall {
			if temp, isShuffle := rw.temps[call]; isShuffle {
				// The pre-phase read: temp[lane] = source[lane ^ off], the
				// partner's value before the shuffling statement runs in
				// any lane.
				src := call.Arguments[0].(*ast.Identifier).Value
				partner := &ast.InfixExpression{Token: rw.tok, Operator: "^", Left: rw.laneRef(), Right: call.Arguments[1]}
				return []ast.Statement{&ast.IndexAssignmentStatement{Token: rw.tok,
					Target: &ast.IndexExpression{Token: rw.tok, Left: &ast.Identifier{Token: rw.tok, Value: temp}, Index: rw.laneRef()},
					Value:  &ast.IndexExpression{Token: rw.tok, Left: &ast.Identifier{Token: rw.tok, Value: privateName(src)}, Index: partner}}}
			}
		}
		e := *v
		e.Expression = rw.expr(v.Expression)
		return []ast.Statement{&e}
	case *ast.BlockStatement:
		return []ast.Statement{rw.block(v)}
	}
	return []ast.Statement{s}
}

func (rw *rewriter) block(b *ast.BlockStatement) *ast.BlockStatement {
	if b == nil {
		return nil
	}
	out := *b
	out.Statements = nil
	for _, s := range b.Statements {
		out.Statements = append(out.Statements, rw.stmt(s)...)
	}
	return &out
}

func (rw *rewriter) expr(e ast.Expression) ast.Expression {
	switch v := e.(type) {
	case nil:
		return nil
	case *ast.Identifier:
		if _, isPrivate := rw.private[v.Value]; isPrivate {
			return rw.slot(v.Value)
		}
		return v
	case *ast.InvocationExpression:
		if id, ok := v.Function.(*ast.Identifier); ok && id.Value == "lane" {
			return rw.laneRef()
		}
		if temp, isShuffle := rw.temps[v]; isShuffle {
			return &ast.IndexExpression{Token: rw.tok, Left: &ast.Identifier{Token: rw.tok, Value: temp}, Index: rw.laneRef()}
		}
		c := *v
		c.Arguments = make([]ast.Expression, len(v.Arguments))
		for i, a := range v.Arguments {
			c.Arguments[i] = rw.expr(a)
		}
		return &c
	case *ast.InfixExpression:
		i := *v
		i.Left, i.Right = rw.expr(v.Left), rw.expr(v.Right)
		return &i
	case *ast.PrefixExpression:
		p := *v
		p.Right = rw.expr(v.Right)
		return &p
	case *ast.IndexExpression:
		if v.Dot {
			ix := *v
			ix.Left = rw.expr(v.Left)
			return &ix
		}
		ix := *v
		ix.Left, ix.Index = rw.expr(v.Left), rw.expr(v.Index)
		return &ix
	case *ast.MatchExpression:
		m := *v
		m.Scrutinee = rw.expr(v.Scrutinee)
		m.Arms = make([]*ast.MatchArm, len(v.Arms))
		for i, arm := range v.Arms {
			a := *arm
			a.Body = rw.expr(arm.Body)
			m.Arms[i] = &a
		}
		return &m
	case *ast.BlockExpression:
		b := *v
		b.Block = rw.block(v.Block)
		return &b
	case *ast.ArrayLiteral:
		l := *v
		l.Elements = make([]ast.Expression, len(v.Elements))
		for i, el := range v.Elements {
			l.Elements[i] = rw.expr(el)
		}
		return &l
	}
	return e
}

func mentionsLane(e ast.Expression) bool {
	found := false
	walkNodes(e, func(n ast.Node) {
		if call, ok := n.(*ast.InvocationExpression); ok {
			if id, ok := call.Function.(*ast.Identifier); ok && id.Value == "lane" {
				found = true
			}
		}
	})
	return found
}

// walkNodes visits the statements and expressions of a kernel body.
func walkNodes(node ast.Node, visit func(ast.Node)) {
	if node == nil {
		return
	}
	visit(node)
	switch n := node.(type) {
	case *ast.BlockStatement:
		if n == nil {
			return
		}
		for _, s := range n.Statements {
			walkNodes(s, visit)
		}
	case *ast.BlockExpression:
		if n.Block != nil {
			walkNodes(n.Block, visit)
		}
	case *ast.ExpressionStatement:
		walkNodes(n.Expression, visit)
	case *ast.VariableDeclaration:
		if n.Value != nil {
			walkNodes(n.Value, visit)
		}
	case *ast.AssignmentStatement:
		walkNodes(n.Value, visit)
	case *ast.IndexAssignmentStatement:
		walkNodes(n.Target, visit)
		walkNodes(n.Value, visit)
	case *ast.WhileStatement:
		walkNodes(n.Condition, visit)
		if n.Body != nil {
			walkNodes(n.Body, visit)
		}
	case *ast.PrefixExpression:
		walkNodes(n.Right, visit)
	case *ast.InfixExpression:
		walkNodes(n.Left, visit)
		walkNodes(n.Right, visit)
	case *ast.IndexExpression:
		walkNodes(n.Left, visit)
		if !n.Dot {
			walkNodes(n.Index, visit)
		}
	case *ast.InvocationExpression:
		walkNodes(n.Function, visit)
		for _, a := range n.Arguments {
			walkNodes(a, visit)
		}
	case *ast.MatchExpression:
		walkNodes(n.Scrutinee, visit)
		for _, arm := range n.Arms {
			walkNodes(arm.Body, visit)
		}
	case *ast.ArrayLiteral:
		for _, el := range n.Elements {
			walkNodes(el, visit)
		}
	}
}
