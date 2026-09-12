package lowering

import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// LowerProgram performs lowering/desugaring transformations on the AST
// This transforms high-level operations (indexing, slicing) into core intrinsics
// that the C backend can easily handle
func LowerProgram(program *ast.Program, tc *typechecker.TypeChecker) *ast.Program {
	lowered := &ast.Program{
		Statements:           make([]ast.Statement, 0, len(program.Statements)),
		LeadingTriviaTokens:  program.LeadingTriviaTokens,
		TrailingTriviaTokens: program.TrailingTriviaTokens,
	}

	for _, stmt := range program.Statements {
		lowered.Statements = append(lowered.Statements, lowerStatement(stmt, tc))
	}

	return lowered
}

// lowerStatement lowers a statement
func lowerStatement(stmt ast.Statement, tc *typechecker.TypeChecker) ast.Statement {
	switch s := stmt.(type) {
	case *ast.VariableDeclaration:
		return lowerVariableDeclaration(s, tc)
	case *ast.ExpressionStatement:
		// A statement-position Bool match (the condition sugar of
		// docs/spec/10-syntax.md §3a, or an explicit true/false match)
		// lowers to the internal branch statement, so side-effecting
		// branches emit as C if/else.
		if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch {
			if branch, isBranch := lowerBoolMatchStatement(match, tc); isBranch {
				return branch
			}
		}
		return &ast.ExpressionStatement{
			BaseNode:   s.BaseNode,
			Token:      s.Token,
			Expression: lowerExpression(s.Expression, tc),
			Discard:    s.Discard,
		}
	case *ast.FunctionStatement:
		return lowerFunctionStatement(s, tc)
	case *ast.BlockStatement:
		return lowerBlockStatement(s, tc)
	case *ast.AssignmentStatement:
		return &ast.AssignmentStatement{
			BaseNode: s.BaseNode,
			Token:    s.Token,
			Name:     s.Name,
			Value:    lowerExpression(s.Value, tc),
		}
	case *ast.IndexAssignmentStatement:
		// The target stays an index expression (the store lowering is a
		// backend decision); its parts are lowered. Dot rides along: a
		// field name is not an expression and is never index-lowered.
		targetIndex := s.Target.Index
		if !s.Target.Dot {
			targetIndex = lowerExpression(s.Target.Index, tc)
		}
		return &ast.IndexAssignmentStatement{
			BaseNode: s.BaseNode,
			Token:    s.Token,
			Target: &ast.IndexExpression{
				BaseNode: s.Target.BaseNode,
				Token:    s.Target.Token,
				Left:     lowerExpression(s.Target.Left, tc),
				Index:    targetIndex,
				Dot:      s.Target.Dot,
			},
			Value: lowerExpression(s.Value, tc),
		}
	case *ast.IfStatement:
		loweredIf := &ast.IfStatement{
			BaseNode:  s.BaseNode,
			Token:     s.Token,
			Condition: lowerExpression(s.Condition, tc),
		}
		if s.Consequence != nil {
			loweredIf.Consequence = lowerBlockStatement(s.Consequence, tc)
		}
		switch alternative := s.Alternative.(type) {
		case *ast.IfStatement:
			loweredIf.Alternative = lowerStatement(alternative, tc)
		case *ast.BlockStatement:
			loweredIf.Alternative = lowerBlockStatement(alternative, tc)
		}
		return loweredIf
	case *ast.WhileStatement:
		lowered := &ast.WhileStatement{
			BaseNode:  s.BaseNode,
			Token:     s.Token,
			Condition: lowerExpression(s.Condition, tc),
		}
		if s.Body != nil {
			if body, ok := lowerStatement(s.Body, tc).(*ast.BlockStatement); ok {
				lowered.Body = body
			} else {
				lowered.Body = s.Body
			}
		}
		return lowered
	case *ast.UnsafeBlock:
		lowered := &ast.UnsafeBlock{
			BaseNode: s.BaseNode,
			Token:    s.Token,
		}
		if s.Body != nil {
			if body, ok := lowerStatement(s.Body, tc).(*ast.BlockStatement); ok {
				lowered.Body = body
			} else {
				lowered.Body = s.Body
			}
		}
		return lowered
	default:
		// Other statement types don't need lowering
		return stmt
	}
}

// lowerVariableDeclaration lowers variable declarations
func lowerVariableDeclaration(vd *ast.VariableDeclaration, tc *typechecker.TypeChecker) *ast.VariableDeclaration {
	if vd.Value != nil {
		return &ast.VariableDeclaration{
			BaseNode: vd.BaseNode,
			Token:    vd.Token,
			Name:     vd.Name,
			Type:     vd.Type,
			Value:    lowerExpression(vd.Value, tc),
			Section:  vd.Section,
		}
	}
	return vd
}

// lowerFunctionStatement lowers function statements
func lowerFunctionStatement(fn *ast.FunctionStatement, tc *typechecker.TypeChecker) *ast.FunctionStatement {
	if fn == nil {
		return nil
	}
	if fn.Name == nil {
		return nil
	}
	// Extern bindings have no Oak body to lower (docs/spec/92-ffi.md).
	if fn.ExternSymbol != "" {
		return fn
	}
	if fn.Body != nil {
		// Body is an Expression - just lower it recursively. A block body's
		// final statement is the function's return position: a match there
		// must stay a match (the backend emits it with arms in return
		// position), never the statement-form branch conversion.
		var loweredBody ast.Expression
		if block, isBlock := fn.Body.(*ast.BlockExpression); isBlock && block.Block != nil && len(block.Block.Statements) > 0 {
			loweredBody = lowerFunctionBodyBlock(block, tc)
		} else {
			loweredBody = lowerExpression(fn.Body, tc)
		}
		return &ast.FunctionStatement{
			BaseNode:     fn.BaseNode,
			Token:        fn.Token,
			EndToken:     fn.EndToken,
			TypeParams:   fn.TypeParams,
			Name:         fn.Name,
			Receiver:     fn.Receiver,
			Lowering:     fn.Lowering, // the protocol projection's compiler-known lowering rides along
			Parameters:   fn.Parameters,
			ReturnType:   fn.ReturnType,
			Body:         loweredBody,
			AsmBacked:    fn.AsmBacked,
			AsmArch:      fn.AsmArch,
			NativeBacked: fn.NativeBacked,
			Exported:     fn.Exported,
			Opaque:       fn.Opaque,
			// The C ABI symbol of an explicit export travels with the
			// definition to the backend (docs/spec/92-ffi.md section 2.9).
			ExportSymbol: fn.ExportSymbol,
		}
	}
	return fn
}

// lowerBoolMatchStatement converts a statement-position match whose arms
// are Bool-literal (or trailing wildcard) patterns into the internal branch
// statement (ast.IfStatement — no surface keyword; the surface form is the
// `?` condition sugar). Reports false for any other match shape.
func lowerBoolMatchStatement(match *ast.MatchExpression, tc *typechecker.TypeChecker) (ast.Statement, bool) {
	if match.Scrutinee == nil || len(match.Arms) == 0 || len(match.Arms) > 2 {
		return nil, false
	}
	var trueBody, falseBody ast.Expression
	for i, arm := range match.Arms {
		switch pattern := arm.Pattern.(type) {
		case *ast.LiteralPattern:
			boolLit, isBool := pattern.Value.(*ast.Boolean)
			if !isBool {
				return nil, false
			}
			if boolLit.Value {
				trueBody = arm.Body
			} else {
				falseBody = arm.Body
			}
		case *ast.WildcardPattern:
			// A trailing wildcard covers the remaining case.
			if i != len(match.Arms)-1 {
				return nil, false
			}
			if trueBody == nil {
				trueBody = arm.Body
			} else {
				falseBody = arm.Body
			}
		default:
			return nil, false
		}
	}
	if trueBody == nil {
		return nil, false
	}

	branch := &ast.IfStatement{
		BaseNode:    match.BaseNode,
		Token:       match.Token,
		Condition:   lowerExpression(match.Scrutinee, tc),
		Consequence: branchBlock(trueBody, tc),
	}
	if falseBlock := branchBlock(falseBody, tc); falseBlock != nil && len(falseBlock.Statements) > 0 {
		branch.Alternative = falseBlock
	}
	return branch, true
}

// branchBlock normalizes a lowered arm body into a block of statements.
func branchBlock(body ast.Expression, tc *typechecker.TypeChecker) *ast.BlockStatement {
	if body == nil {
		return nil
	}
	lowered := lowerExpression(body, tc)
	if block, isBlock := lowered.(*ast.BlockExpression); isBlock {
		if block.Block == nil {
			return &ast.BlockStatement{}
		}
		return block.Block
	}
	return &ast.BlockStatement{
		Statements: []ast.Statement{&ast.ExpressionStatement{Expression: lowered}},
	}
}

// lowerFunctionBodyBlock lowers a value-position block (function bodies,
// match arm and branch bodies), keeping the final statement's expression
// form intact — the block's value.
func lowerFunctionBodyBlock(body *ast.BlockExpression, tc *typechecker.TypeChecker) *ast.BlockExpression {
	statements := body.Block.Statements
	lowered := make([]ast.Statement, 0, len(statements))
	for _, stmt := range statements[:len(statements)-1] {
		if hoisted, wasHoisted := hoistBoolMatchValue(stmt, tc); wasHoisted {
			lowered = append(lowered, hoisted...)
			continue
		}
		lowered = append(lowered, lowerStatement(stmt, tc))
	}
	last := statements[len(statements)-1]
	if exprStmt, isExpr := last.(*ast.ExpressionStatement); isExpr {
		lowered = append(lowered, &ast.ExpressionStatement{
			BaseNode:   exprStmt.BaseNode,
			Token:      exprStmt.Token,
			Expression: lowerExpression(exprStmt.Expression, tc),
			Discard:    exprStmt.Discard,
		})
	} else {
		lowered = append(lowered, lowerStatement(last, tc))
	}
	return &ast.BlockExpression{
		BaseNode: body.BaseNode,
		Token:    body.Token,
		Block: &ast.BlockStatement{
			BaseNode:   body.Block.BaseNode,
			Token:      body.Block.Token,
			Statements: lowered,
		},
	}
}

// lowerBlockStatement lowers block statements
func lowerBlockStatement(block *ast.BlockStatement, tc *typechecker.TypeChecker) *ast.BlockStatement {
	loweredStmts := make([]ast.Statement, 0, len(block.Statements))
	for _, stmt := range block.Statements {
		// A declaration or assignment whose value is a Bool condition match
		// with statement-bearing branches hoists into a declaration plus a
		// branch statement assigning each branch's trailing value — the C an
		// author would write (docs/spec/10-syntax.md §3a).
		if hoisted, wasHoisted := hoistBoolMatchValue(stmt, tc); wasHoisted {
			loweredStmts = append(loweredStmts, hoisted...)
			continue
		}
		loweredStmts = append(loweredStmts, lowerStatement(stmt, tc))
	}
	return &ast.BlockStatement{
		BaseNode:   block.BaseNode,
		Token:      block.Token,
		Statements: loweredStmts,
	}
}

// hoistBoolMatchValue expands `x: T = cond ? {…; a} | {…; b}` (and the
// assignment form) when either branch carries statements: the value form
// cannot inline into a C expression, so it becomes a declaration followed
// by if/else whose branches end in an assignment of the trailing value.
func hoistBoolMatchValue(stmt ast.Statement, tc *typechecker.TypeChecker) ([]ast.Statement, bool) {
	var name *ast.Identifier
	var match *ast.MatchExpression
	var lead ast.Statement

	switch s := stmt.(type) {
	case *ast.VariableDeclaration:
		candidate, isMatch := s.Value.(*ast.MatchExpression)
		if !isMatch {
			return nil, false
		}
		name = s.Name
		match = candidate
		lead = &ast.VariableDeclaration{
			BaseNode: s.BaseNode, Token: s.Token, Name: s.Name, Type: s.Type, Section: s.Section,
		}
	case *ast.AssignmentStatement:
		candidate, isMatch := s.Value.(*ast.MatchExpression)
		if !isMatch {
			return nil, false
		}
		name = s.Name
		match = candidate
	default:
		return nil, false
	}

	trueBody, falseBody, isBool := boolMatchArms(match)
	if isBool {
		if !(branchCarriesStatements(trueBody) || branchCarriesStatements(falseBody)) {
			return nil, false
		}
		trueBlock, trueOK := branchAssignBlock(name, trueBody, tc)
		falseBlock, falseOK := branchAssignBlock(name, falseBody, tc)
		if !trueOK || !falseOK {
			return nil, false
		}

		branch := &ast.IfStatement{
			BaseNode:    match.BaseNode,
			Token:       match.Token,
			Condition:   lowerExpression(match.Scrutinee, tc),
			Consequence: trueBlock,
			Alternative: falseBlock,
		}
		if lead != nil {
			return []ast.Statement{lead, branch}, true
		}
		return []ast.Statement{branch}, true
	}

	// General value match (ADT/scalar arms): hoist to a declaration plus a
	// statement-position match whose arm bodies end in an assignment of
	// each arm's trailing value; the backend emits tag-guarded statement
	// blocks with payload bindings intact.
	if !matchNeedsHoist(match) {
		return nil, false
	}
	rewritten := &ast.MatchExpression{
		BaseNode:  match.BaseNode,
		Token:     match.Token,
		Scrutinee: lowerExpression(match.Scrutinee, tc),
	}
	for _, arm := range match.Arms {
		armBlock, ok := branchAssignBlock(name, arm.Body, tc)
		if !ok {
			return nil, false
		}
		rewritten.Arms = append(rewritten.Arms, &ast.MatchArm{
			Token:   arm.Token,
			Pattern: arm.Pattern,
			Body:    &ast.BlockExpression{Token: arm.Token, Block: armBlock},
		})
	}
	hoisted := &ast.ExpressionStatement{Expression: rewritten}
	if lead != nil {
		return []ast.Statement{lead, hoisted}, true
	}
	return []ast.Statement{hoisted}, true
}

// matchNeedsHoist reports whether a value-position match cannot inline as a
// C expression: variant patterns need tag guards and payload bindings, and
// statement-bearing block arms need statement position.
func matchNeedsHoist(match *ast.MatchExpression) bool {
	for _, arm := range match.Arms {
		if _, isVariant := arm.Pattern.(*ast.VariantPattern); isVariant {
			return true
		}
		if branchCarriesStatements(arm.Body) {
			return true
		}
	}
	return false
}

// boolMatchArms classifies a two-arm Bool condition match (true/false
// literal patterns, trailing wildcard admitted).
func boolMatchArms(match *ast.MatchExpression) (trueBody, falseBody ast.Expression, ok bool) {
	if match.Scrutinee == nil || len(match.Arms) != 2 {
		return nil, nil, false
	}
	for i, arm := range match.Arms {
		switch pattern := arm.Pattern.(type) {
		case *ast.LiteralPattern:
			boolLit, isBool := pattern.Value.(*ast.Boolean)
			if !isBool {
				return nil, nil, false
			}
			if boolLit.Value {
				trueBody = arm.Body
			} else {
				falseBody = arm.Body
			}
		case *ast.WildcardPattern:
			if i != 1 {
				return nil, nil, false
			}
			if trueBody == nil {
				trueBody = arm.Body
			} else {
				falseBody = arm.Body
			}
		default:
			return nil, nil, false
		}
	}
	return trueBody, falseBody, trueBody != nil && falseBody != nil
}

func branchCarriesStatements(body ast.Expression) bool {
	block, isBlock := body.(*ast.BlockExpression)
	return isBlock && block.Block != nil && len(block.Block.Statements) > 1
}

// branchAssignBlock lowers one value branch into a block whose final
// statement assigns the branch's trailing value to name.
func branchAssignBlock(name *ast.Identifier, body ast.Expression, tc *typechecker.TypeChecker) (*ast.BlockStatement, bool) {
	assign := func(value ast.Expression) ast.Statement {
		return &ast.AssignmentStatement{Name: name, Value: lowerExpression(value, tc)}
	}
	block, isBlock := body.(*ast.BlockExpression)
	if !isBlock {
		return &ast.BlockStatement{Statements: []ast.Statement{assign(body)}}, true
	}
	if block.Block == nil || len(block.Block.Statements) == 0 {
		return nil, false
	}
	statements := block.Block.Statements
	trailing, isExpr := statements[len(statements)-1].(*ast.ExpressionStatement)
	if !isExpr {
		return nil, false
	}
	loweredLead := make([]ast.Statement, 0, len(statements))
	for _, inner := range statements[:len(statements)-1] {
		loweredLead = append(loweredLead, lowerStatement(inner, tc))
	}
	return &ast.BlockStatement{
		BaseNode:   block.Block.BaseNode,
		Token:      block.Block.Token,
		Statements: append(loweredLead, assign(trailing.Expression)),
	}, true
}

// lowerExpression lowers an expression
func lowerExpression(expr ast.Expression, tc *typechecker.TypeChecker) ast.Expression {
	switch e := expr.(type) {
	case *ast.IndexExpression:
		return lowerIndexExpression(e, tc)
	case *ast.SliceExpression:
		return lowerSliceExpression(e, tc)
	case *ast.InfixExpression:
		return &ast.InfixExpression{
			BaseNode: e.BaseNode,
			Token:    e.Token,
			Left:     lowerExpression(e.Left, tc),
			Operator: e.Operator,
			Right:    lowerExpression(e.Right, tc),
		}
	case *ast.PrefixExpression:
		return &ast.PrefixExpression{
			BaseNode: e.BaseNode,
			Token:    e.Token,
			Operator: e.Operator,
			Right:    lowerExpression(e.Right, tc),
		}
	case *ast.InvocationExpression:
		return lowerInvocationExpression(e, tc)
	case *ast.VariantExpression:
		// Constructor payloads are ordinary expressions: lower their indexing
		// and calls too, while preserving the variant's resolution identity.
		lowered := *e
		lowered.Payload = lowerExpression(e.Payload, tc)
		return &lowered
	case *ast.MatchExpression:
		lowered := &ast.MatchExpression{
			BaseNode:  e.BaseNode,
			Token:     e.Token, // position keys resolution records
			Scrutinee: lowerExpression(e.Scrutinee, tc),
		}
		for _, arm := range e.Arms {
			lowered.Arms = append(lowered.Arms, &ast.MatchArm{
				Token:   arm.Token,
				Pattern: arm.Pattern,
				Body:    lowerExpression(arm.Body, tc),
			})
		}
		return lowered
	case *ast.BlockExpression:
		// A block expression's final statement is its VALUE: it lowers as
		// an expression (a tail match stays a match for return-position
		// emission), never through the statement-form conversion.
		if e.Block == nil || len(e.Block.Statements) == 0 {
			return e
		}
		return lowerFunctionBodyBlock(e, tc)
	default:
		// Other expressions don't need lowering
		return expr
	}
}

// lowerIndexExpression lowers arr[i] to core_index(arr, i)
func lowerIndexExpression(expr *ast.IndexExpression, tc *typechecker.TypeChecker) ast.Expression {
	// Member access spelled with '.' (record fields, library members, ADT
	// constructors) is not element indexing: only bracket indexing lowers
	// to bounds-checked core_index. The receiver still lowers.
	if expr.Dot {
		return &ast.IndexExpression{
			BaseNode: expr.BaseNode,
			Token:    expr.Token,
			Left:     lowerExpression(expr.Left, tc),
			Index:    expr.Index,
			Dot:      true,
		}
	}
	// Library member access (c.Int, arm64.clz64, simd.load_u8x16, ...) is
	// not element indexing: preserve the shape for the backend
	// (docs/spec/92-ffi.md, docs/spec/93-simd.md). (Defense in depth for
	// accesses constructed without the Dot mark.)
	if base, ok := expr.Left.(*ast.Identifier); ok && typechecker.CompilerKnownLibrary(base.Value) {
		if member, ok := expr.Index.(*ast.Identifier); ok && typechecker.KnownLibraryMember(base.Value, member.Value) {
			return expr
		}
	}
	// The callee of an inbound buffer borrow, c.borrow[T] (docs/spec/92-ffi.md
	// section 2.7), names an element type, not an element.
	if typechecker.ForeignBorrowCallee(expr) {
		return expr
	}
	// The callee of a message send, c.msg_send[(params) -> ret]
	// (docs/spec/92-ffi.md section 2.12), carries a signature, not an
	// element index.
	if _, isSend := typechecker.MessageSendCallee(expr); isSend {
		return expr
	}
	// Create a call to core_index intrinsic
	coreIndex := &ast.Identifier{
		Token: expr.Token,
		Value: "core_index",
	}
	return &ast.InvocationExpression{
		BaseNode: expr.BaseNode,
		Token:    expr.Token,
		Function: coreIndex,
		Arguments: []ast.Expression{
			lowerExpression(expr.Left, tc),
			lowerExpression(expr.Index, tc),
		},
	}
}

// lowerSliceExpression lowers arr[i:j] to core_slice(arr, i, j)
// Handles normalization: nil low -> 0, nil high -> len
func lowerSliceExpression(expr *ast.SliceExpression, tc *typechecker.TypeChecker) ast.Expression {
	// Create a call to core_slice intrinsic
	coreSlice := &ast.Identifier{
		Token: expr.Token,
		Value: "core_slice",
	}

	// Normalize bounds: nil low -> 0, nil high -> len(seq)
	low := expr.Low
	if low == nil {
		// Default low bound is 0
		low = &ast.IntegerLiteral{
			Token: expr.Token,
			Value: 0,
		}
	} else {
		low = lowerExpression(low, tc)
	}

	high := expr.High
	if high == nil {
		// Default high bound is len(seq)
		// We'll use a special intrinsic: core_len(seq)
		coreLen := &ast.Identifier{
			Token: expr.Token,
			Value: "core_len",
		}
		high = &ast.InvocationExpression{
			Token:    expr.Token,
			Function: coreLen,
			Arguments: []ast.Expression{
				lowerExpression(expr.Seq, tc),
			},
		}
	} else {
		high = lowerExpression(high, tc)
	}

	return &ast.InvocationExpression{
		BaseNode: expr.BaseNode,
		Token:    expr.Token,
		Function: coreSlice,
		Arguments: []ast.Expression{
			lowerExpression(expr.Seq, tc),
			low,
			high,
		},
	}
}

// lowerInvocationExpression lowers invocation expressions (recursively)
func lowerInvocationExpression(expr *ast.InvocationExpression, tc *typechecker.TypeChecker) *ast.InvocationExpression {
	loweredArgs := make([]ast.Expression, 0, len(expr.Arguments))
	for _, arg := range expr.Arguments {
		loweredArgs = append(loweredArgs, lowerExpression(arg, tc))
	}
	return &ast.InvocationExpression{
		BaseNode:       expr.BaseNode,
		Token:          expr.Token,
		Function:       lowerExpression(expr.Function, tc),
		Arguments:      loweredArgs,
		ResolvedMethod: expr.ResolvedMethod, // the checker's Type::method resolution rides along
	}
}

// NormalizeSliceBounds normalizes slice bounds for negative indices
// This is a helper that can be used during type checking or lowering
// For now, we only handle literal negative indices at compile time
func NormalizeSliceBounds(seqType typechecker.Type, low, high ast.Expression) (ast.Expression, ast.Expression) {
	// If low is a negative integer literal, normalize it
	if lowLit, ok := low.(*ast.IntegerLiteral); ok && lowLit.Value < 0 {
		// For now, we'll leave negative indices to runtime handling
		// In a full implementation, we'd compute: len - abs(value)
		// This requires knowing the length at compile time
	}

	// If high is a negative integer literal, normalize it
	if highLit, ok := high.(*ast.IntegerLiteral); ok && highLit.Value < 0 {
		// Similar to low, normalize at runtime or compile-time if possible
	}

	return low, high
}
