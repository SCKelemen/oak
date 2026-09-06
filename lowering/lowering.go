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
		return &ast.ExpressionStatement{
			BaseNode:   s.BaseNode,
			Token:      s.Token,
			Expression: lowerExpression(s.Expression, tc),
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
		// backend decision); its parts are lowered.
		return &ast.IndexAssignmentStatement{
			BaseNode: s.BaseNode,
			Token:    s.Token,
			Target: &ast.IndexExpression{
				BaseNode: s.Target.BaseNode,
				Token:    s.Target.Token,
				Left:     lowerExpression(s.Target.Left, tc),
				Index:    lowerExpression(s.Target.Index, tc),
			},
			Value: lowerExpression(s.Value, tc),
		}
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
		// Body is an Expression - just lower it recursively
		loweredBody := lowerExpression(fn.Body, tc)
		return &ast.FunctionStatement{
			BaseNode:   fn.BaseNode,
			Token:      fn.Token,
			EndToken:   fn.EndToken,
			TypeParams: fn.TypeParams,
			Name:       fn.Name,
			Receiver:   fn.Receiver,
			Parameters: fn.Parameters,
			ReturnType: fn.ReturnType,
			Body:       loweredBody,
		}
	}
	return fn
}

// lowerBlockStatement lowers block statements
func lowerBlockStatement(block *ast.BlockStatement, tc *typechecker.TypeChecker) *ast.BlockStatement {
	loweredStmts := make([]ast.Statement, 0, len(block.Statements))
	for _, stmt := range block.Statements {
		loweredStmts = append(loweredStmts, lowerStatement(stmt, tc))
	}
	return &ast.BlockStatement{
		BaseNode:   block.BaseNode,
		Token:      block.Token,
		Statements: loweredStmts,
	}
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
	case *ast.BlockExpression:
		if e.Block == nil {
			return e
		}
		lowered, ok := lowerStatement(e.Block, tc).(*ast.BlockStatement)
		if !ok {
			return e
		}
		return &ast.BlockExpression{
			BaseNode: e.BaseNode,
			Token:    e.Token,
			Block:    lowered,
		}
	default:
		// Other expressions don't need lowering
		return expr
	}
}

// lowerIndexExpression lowers arr[i] to core_index(arr, i)
func lowerIndexExpression(expr *ast.IndexExpression, tc *typechecker.TypeChecker) ast.Expression {
	// Library member access (c.Int, arm64.clz64, ...) is not element
	// indexing: preserve the shape for the backend (docs/spec/92-ffi.md).
	if base, ok := expr.Left.(*ast.Identifier); ok && (base.Value == "c" || base.Value == "arm64") {
		if member, ok := expr.Index.(*ast.Identifier); ok && typechecker.KnownLibraryMember(base.Value, member.Value) {
			return expr
		}
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
		BaseNode:  expr.BaseNode,
		Token:     expr.Token,
		Function:  lowerExpression(expr.Function, tc),
		Arguments: loweredArgs,
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
