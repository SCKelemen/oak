package borrowchecker

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// BorrowState represents the borrow state of an owned array
type BorrowState int

const (
	// Free means no active borrows
	Free BorrowState = iota
	// SharedRead means one or more read-only borrows (View/[]T)
	SharedRead
	// UniqueWrite means exactly one writable borrow (Span/[*]T)
	UniqueWrite
)

func (bs BorrowState) String() string {
	switch bs {
	case Free:
		return "Free"
	case SharedRead:
		return "SharedRead"
	case UniqueWrite:
		return "UniqueWrite"
	default:
		return fmt.Sprintf("BorrowState(%d)", int(bs))
	}
}

// BorrowChecker tracks borrow states and enforces borrowing rules
type BorrowChecker struct {
	// ownerStates maps owned array variable names to their current borrow state
	ownerStates map[string]BorrowState

	// ownerOf maps borrow variable names (views/spans) to their owner variable names
	ownerOf map[string]string

	// errors collects borrow checker errors
	errors []string

	// currentBlock tracks the current block scope for lexical borrowing
	// In v1, borrows cannot escape their creation block
	currentBlockDepth int
}

// New creates a new borrow checker
func New() *BorrowChecker {
	return &BorrowChecker{
		ownerStates: make(map[string]BorrowState),
		ownerOf:     make(map[string]string),
		errors:      []string{},
	}
}

// Errors returns all borrow checker errors
func (bc *BorrowChecker) Errors() []string {
	return bc.errors
}

// ClearErrors clears all errors
func (bc *BorrowChecker) ClearErrors() {
	bc.errors = []string{}
}

// addError adds an error to the error list
func (bc *BorrowChecker) addError(msg string) {
	bc.errors = append(bc.errors, fmt.Sprintf("[borrow error] %s", msg))
}

// CheckProgram performs borrow checking on a program
func (bc *BorrowChecker) CheckProgram(program *ast.Program, env *typechecker.TypeEnvironment) {
	bc.ClearErrors()
	bc.ownerStates = make(map[string]BorrowState)
	bc.ownerOf = make(map[string]string)
	bc.currentBlockDepth = 0

	for _, stmt := range program.Statements {
		bc.checkStatement(stmt, env)
	}
}

// checkStatement checks a statement for borrow violations
func (bc *BorrowChecker) checkStatement(stmt ast.Statement, env *typechecker.TypeEnvironment) {
	switch s := stmt.(type) {
	case *ast.VariableDeclaration:
		bc.checkVariableDeclaration(s, env)
	case *ast.ExpressionStatement:
		bc.checkExpression(s.Expression, env)
	case *ast.BlockStatement:
		bc.checkBlockStatement(s, env)
	default:
		// Other statement types don't affect borrowing
	}
}

// checkBlockStatement handles block scoping for lexical borrowing
func (bc *BorrowChecker) checkBlockStatement(block *ast.BlockStatement, env *typechecker.TypeEnvironment) {
	bc.currentBlockDepth++
	defer func() {
		// At end of block, drop all borrows created in this block
		bc.dropBorrowsInCurrentBlock()
		bc.currentBlockDepth--
	}()

	for _, stmt := range block.Statements {
		bc.checkStatement(stmt, env)
	}
}

// dropBorrowsInCurrentBlock removes borrows created in the current block
// and resets owner states if no borrows remain
func (bc *BorrowChecker) dropBorrowsInCurrentBlock() {
	// Find all borrows that should be dropped
	// In v1, all borrows are lexical, so we track them by block depth
	// For simplicity, we'll track borrows by variable name and drop them at block end
	// This is a simplified model - a full implementation would track scope more precisely

	// Recompute owner states: if no borrows point to an owner, set it to Free
	for ownerName := range bc.ownerStates {
		hasActiveBorrows := false
		for _, borrowOwner := range bc.ownerOf {
			if borrowOwner == ownerName {
				hasActiveBorrows = true
				break
			}
		}
		if !hasActiveBorrows {
			bc.ownerStates[ownerName] = Free
		}
	}
}

// checkVariableDeclaration checks variable declarations for borrow creation
func (bc *BorrowChecker) checkVariableDeclaration(vd *ast.VariableDeclaration, env *typechecker.TypeEnvironment) {
	varName := vd.Name.Value

	// Check if the value expression creates a borrow (check before we register the variable)
	if vd.Value != nil {
		bc.checkExpression(vd.Value, env, varName)
	}

	// After type checking, check if this variable is an owned array, view, or span
	// The typechecker should have registered the type by now
	typeScheme, ok := env.Get(varName)
	if ok && typeScheme != nil {
		typ := typeScheme.Type
		if arrayType, ok := typ.(*typechecker.ArrayType); ok {
			if !arrayType.IsSlice && !arrayType.IsSpan && arrayType.Length >= 0 {
				// This is an owned array [N]T - initialize its borrow state
				bc.ownerStates[varName] = Free
			}
		}
	} else if vd.Type != nil {
		// Type wasn't in environment yet - try to parse it from AST
		// This is a fallback for when type checking hasn't run yet
		// In practice, borrow checking should run after type checking
	}
}

// checkTypeExpression determines if a type expression represents an owned array, view, or span
func (bc *BorrowChecker) checkTypeExpression(typeExpr ast.Expression, varName string, env *typechecker.TypeEnvironment) {
	// This is handled in checkVariableDeclaration by querying the type environment
	// after type checking has resolved the type
}

// checkExpression checks an expression for borrow operations
// targetVarName is the name of the variable being assigned to (if any)
func (bc *BorrowChecker) checkExpression(expr ast.Expression, env *typechecker.TypeEnvironment, targetVarName ...string) {
	var targetVar string
	if len(targetVarName) > 0 {
		targetVar = targetVarName[0]
	}

	switch e := expr.(type) {
	case *ast.SliceExpression:
		bc.checkSliceExpression(e, env, targetVar)
	case *ast.IndexExpression:
		bc.checkIndexExpression(e, env)
	case *ast.InfixExpression:
		// Check both sides
		bc.checkExpression(e.Left, env)
		bc.checkExpression(e.Right, env)
	case *ast.PrefixExpression:
		bc.checkExpression(e.Right, env)
	case *ast.InvocationExpression:
		bc.checkInvocationExpression(e, env, targetVar)
	default:
		// Other expressions don't create borrows
	}
}

// checkSliceExpression checks slice operations for borrow creation
func (bc *BorrowChecker) checkSliceExpression(slice *ast.SliceExpression, env *typechecker.TypeEnvironment, targetVar string) {
	// Check the left-hand side (the array/view/span being sliced)
	bc.checkExpression(slice.Left, env)

	// According to the spec, slicing an owned array [N]T creates a View borrow
	// Slicing a View/[]T or Span/[*]T creates a derived subslice (no new borrow)

	// Extract owner from slice.Left
	ownerName := bc.extractOwnerName(slice.Left)
	if ownerName == "" {
		// Could be a view/span being sliced - check if it's a borrow
		if ident, ok := slice.Left.(*ast.Identifier); ok {
			// Check if this identifier is a borrow
			if _, isBorrow := bc.ownerOf[ident.Value]; isBorrow {
				// This is a subslice - share the same owner
				if targetVar != "" {
					bc.createSubslice(ident.Value, targetVar)
				}
				return
			}
		}
		return
	}

	// This is slicing an owned array - creates a View borrow
	if targetVar != "" {
		bc.createViewBorrow(ownerName, targetVar)
	}
}

// extractOwnerName extracts the owner variable name from an expression
// Returns empty string if the expression is not an owned array reference
func (bc *BorrowChecker) extractOwnerName(expr ast.Expression) string {
	switch e := expr.(type) {
	case *ast.Identifier:
		// Check if this is an owned array (has borrow state tracked)
		if _, exists := bc.ownerStates[e.Value]; exists {
			return e.Value
		}
		// Could be an owned array that hasn't been registered yet
		// Return the identifier name and let the caller check
		return e.Value
	case *ast.PrefixExpression:
		// Handle *arr (pointer dereference for view()/span() calls)
		if e.Operator == "*" {
			if ident, ok := e.Right.(*ast.Identifier); ok {
				// Check if the dereferenced identifier is an owned array
				if _, exists := bc.ownerStates[ident.Value]; exists {
					return ident.Value
				}
				return ident.Value
			}
		}
	}
	return ""
}

// checkIndexExpression checks index operations
func (bc *BorrowChecker) checkIndexExpression(index *ast.IndexExpression, env *typechecker.TypeEnvironment) {
	// Indexing doesn't create borrows, but we should check the expressions
	bc.checkExpression(index.Left, env)
	bc.checkExpression(index.Index, env)
}

// checkInvocationExpression checks function calls for borrow operations
func (bc *BorrowChecker) checkInvocationExpression(call *ast.InvocationExpression, env *typechecker.TypeEnvironment, targetVar string) {
	// Check if this is a call to view(), span(), or subslice()
	// For now, we'll check by function name
	if ident, ok := call.Function.(*ast.Identifier); ok {
		switch ident.Value {
		case "view":
			bc.checkViewCall(call, env, targetVar)
		case "span":
			bc.checkSpanCall(call, env, targetVar)
		case "subslice":
			bc.checkSubsliceCall(call, env, targetVar)
		}
	}

	// Check all arguments
	for _, arg := range call.Arguments {
		bc.checkExpression(arg, env)
	}
}

// checkViewCall handles view() calls: creates a read-only borrow
func (bc *BorrowChecker) checkViewCall(call *ast.InvocationExpression, env *typechecker.TypeEnvironment, targetVar string) {
	if len(call.Arguments) != 1 {
		bc.addError("view() expects exactly one argument")
		return
	}

	// The argument should be a pointer to an owned array: *[N]T
	ownerName := bc.extractOwnerName(call.Arguments[0])
	if ownerName == "" {
		bc.addError("view() argument must be a pointer to an owned array")
		return
	}

	if targetVar != "" {
		bc.createViewBorrow(ownerName, targetVar)
	}
}

// checkSpanCall handles span() calls: creates a unique writable borrow
func (bc *BorrowChecker) checkSpanCall(call *ast.InvocationExpression, env *typechecker.TypeEnvironment, targetVar string) {
	if len(call.Arguments) != 1 {
		bc.addError("span() expects exactly one argument")
		return
	}

	// The argument should be a pointer to an owned array: *[N]T
	ownerName := bc.extractOwnerName(call.Arguments[0])
	if ownerName == "" {
		bc.addError("span() argument must be a pointer to an owned array")
		return
	}

	if targetVar != "" {
		bc.createSpanBorrow(ownerName, targetVar)
	}
}

// checkSubsliceCall handles subslice() calls: creates a derived borrow
func (bc *BorrowChecker) checkSubsliceCall(call *ast.InvocationExpression, env *typechecker.TypeEnvironment, targetVar string) {
	if len(call.Arguments) != 3 {
		bc.addError("subslice() expects exactly three arguments (view/span, start, len)")
		return
	}

	// The first argument should be an existing view or span
	if ident, ok := call.Arguments[0].(*ast.Identifier); ok {
		if targetVar != "" {
			bc.createSubslice(ident.Value, targetVar)
		}
	} else {
		bc.addError("subslice() first argument must be a view or span variable")
	}
}

// createViewBorrow creates a read-only borrow (view) from an owner
func (bc *BorrowChecker) createViewBorrow(ownerName, borrowName string) {
	state := bc.ownerStates[ownerName]
	if state == UniqueWrite {
		bc.addError(fmt.Sprintf("cannot create view '%s' from '%s': owner has active writable borrow", borrowName, ownerName))
		return
	}

	// Transition to SharedRead if not already
	bc.ownerStates[ownerName] = SharedRead
	bc.ownerOf[borrowName] = ownerName
}

// createSpanBorrow creates a unique writable borrow (span) from an owner
func (bc *BorrowChecker) createSpanBorrow(ownerName, borrowName string) {
	state := bc.ownerStates[ownerName]
	if state != Free {
		bc.addError(fmt.Sprintf("cannot create span '%s' from '%s': owner has active borrows (state: %s)", borrowName, ownerName, state))
		return
	}

	// Transition to UniqueWrite
	bc.ownerStates[ownerName] = UniqueWrite
	bc.ownerOf[borrowName] = ownerName
}

// createSubslice creates a derived borrow (subslice) from an existing view/span
func (bc *BorrowChecker) createSubslice(sourceBorrowName, subsliceName string) {
	ownerName, exists := bc.ownerOf[sourceBorrowName]
	if !exists {
		bc.addError(fmt.Sprintf("cannot create subslice '%s': source '%s' is not a borrow", subsliceName, sourceBorrowName))
		return
	}

	// Subslice shares the same owner
	bc.ownerOf[subsliceName] = ownerName
	// No state change - subslices don't create new borrows
}
