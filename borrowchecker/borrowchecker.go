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

// borrowKind represents the kind of borrow (view or span)
type borrowKind int

const (
	BorrowView borrowKind = iota // []T - read-only view
	BorrowSpan                   // [*]T - writable span
)

// Region represents a memory region for a borrow
// Used for region-level disjointness checks (v2 feature)
type Region struct {
	Offset int64 // Start offset in elements (0-based)
	Length int64 // Length in elements
	// If Offset or Length is -1, it means the value is not a compile-time constant
	// and we cannot prove disjointness
}

// borrowInfo tracks information about an active borrow
type borrowInfo struct {
	owner      string     // The owner variable name
	kind       borrowKind // Whether this is a view or span
	blockDepth int        // Block depth where this borrow was created
	region     *Region    // Optional: region information for disjointness checks (nil if unknown)
}

// BorrowChecker tracks borrow states and enforces borrowing rules
type BorrowChecker struct {
	// ownerStates maps owned array variable names to their current borrow state
	ownerStates map[string]BorrowState

	// ownerOf maps borrow variable names (views/spans) to their owner variable names
	// This is kept for backward compatibility and quick lookups
	ownerOf map[string]string

	// activeBorrows tracks all active borrows with their metadata
	activeBorrows map[string]borrowInfo

	// errors collects borrow checker errors
	errors []string

	// currentBlock tracks the current block scope for lexical borrowing
	// In v1, borrows cannot escape their creation block
	currentBlockDepth int
}

// New creates a new borrow checker
func New() *BorrowChecker {
	return &BorrowChecker{
		ownerStates:   make(map[string]BorrowState),
		ownerOf:       make(map[string]string),
		activeBorrows: make(map[string]borrowInfo),
		errors:        []string{},
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
	bc.activeBorrows = make(map[string]borrowInfo)
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
	case *ast.FunctionStatement:
		bc.checkFunctionStatement(s, env)
	case *ast.WhileStatement:
		bc.checkWhileStatement(s, env)
	case *ast.AssignmentStatement:
		bc.checkAssignmentStatement(s, env)
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

// checkFunctionStatement handles function definitions with local scope
// Functions create a new scope for borrow checking - borrows created inside
// cannot escape the function, and local variables can be owners
func (bc *BorrowChecker) checkFunctionStatement(stmt *ast.FunctionStatement, env *typechecker.TypeEnvironment) {
	// Get the function's local environment from the typechecker
	// The typechecker creates an enclosed environment for function parameters
	// We need to access that environment to check local variables

	// For now, we'll create a fresh borrow checker state for the function
	// This ensures borrows created inside the function don't affect outer scope
	// and vice versa

	// Save current state
	savedOwnerStates := make(map[string]BorrowState)
	for k, v := range bc.ownerStates {
		savedOwnerStates[k] = v
	}
	savedActiveBorrows := make(map[string]borrowInfo)
	for k, v := range bc.activeBorrows {
		savedActiveBorrows[k] = v
	}
	savedOwnerOf := make(map[string]string)
	for k, v := range bc.ownerOf {
		savedOwnerOf[k] = v
	}
	savedBlockDepth := bc.currentBlockDepth

	// Reset to function-local state
	// We keep the outer environment for type lookups, but start fresh for borrows
	bc.currentBlockDepth = 0

	// Check function parameters - they might be owners
	// The typechecker should have registered them in the function's environment
	// We need to get that environment - for now, we'll check types from the AST
	funcEnv := typechecker.NewEnclosedTypeEnvironment(env)

	// Register receiver if present
	if stmt.Receiver != nil {
		receiverType := bc.parseTypeFromAST(stmt.Receiver.Type, env)
		if receiverType != nil {
			if arrType, ok := receiverType.(*typechecker.ArrayType); ok {
				if !arrType.IsSlice && !arrType.IsSpan && arrType.Length >= 0 {
					// Receiver is an owned array
					bc.ownerStates[stmt.Receiver.Name.Value] = Free
				}
			}
			funcEnv.SetType(stmt.Receiver.Name.Value, receiverType)
		}
	}

	// Register parameters
	for _, param := range stmt.Parameters {
		paramType := bc.parseTypeFromAST(param.Type, env)
		if paramType != nil {
			if arrType, ok := paramType.(*typechecker.ArrayType); ok {
				if !arrType.IsSlice && !arrType.IsSpan && arrType.Length >= 0 {
					// Parameter is an owned array
					bc.ownerStates[param.Name.Value] = Free
				}
			}
			funcEnv.SetType(param.Name.Value, paramType)
		}
	}

	// Check function body
	// The body is an Expression - check it directly
	// If it's a block expression, it will be handled by checkExpression
	bc.checkExpression(stmt.Body, funcEnv)

	// At function end, all borrows created in the function are dropped
	// This happens automatically when we restore state

	// Restore outer state
	bc.ownerStates = savedOwnerStates
	bc.activeBorrows = savedActiveBorrows
	bc.ownerOf = savedOwnerOf
	bc.currentBlockDepth = savedBlockDepth
}

// parseTypeFromAST parses a type expression from the AST
// This is a helper to extract type information when we don't have the typechecker's environment
func (bc *BorrowChecker) parseTypeFromAST(typeExpr ast.Expression, env *typechecker.TypeEnvironment) typechecker.Type {
	// Try to get type from environment first (if it was already type-checked)
	if ident, ok := typeExpr.(*ast.Identifier); ok {
		if scheme, ok := env.Get(ident.Value); ok {
			return scheme.Type
		}
	}

	// For array types, try to parse from IndexExpression
	if indexExpr, ok := typeExpr.(*ast.IndexExpression); ok {
		elementType := bc.parseTypeFromAST(indexExpr.Left, env)
		if elementType == nil {
			return nil
		}

		if intLit, ok := indexExpr.Index.(*ast.IntegerLiteral); ok {
			// Fixed-size array: [N]T
			return &typechecker.ArrayType{
				Length:      intLit.Value,
				IsSlice:     false,
				IsSpan:      false,
				ElementType: elementType,
			}
		} else if ident, ok := indexExpr.Index.(*ast.Identifier); ok {
			if ident.Value == "*" {
				// Span type: [*]T
				return &typechecker.ArrayType{
					Length:      -1,
					IsSlice:     false,
					IsSpan:      true,
					ElementType: elementType,
				}
			} else if ident.Value == "" {
				// Slice type: []T
				return &typechecker.ArrayType{
					Length:      -1,
					IsSlice:     true,
					IsSpan:      false,
					ElementType: elementType,
				}
			}
		}
	}

	// For primitive types
	if ident, ok := typeExpr.(*ast.Identifier); ok {
		switch ident.Value {
		case "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64":
			return &typechecker.PrimitiveType{Name: ident.Value}
		case "string":
			return &typechecker.StringType{}
		case "Bool":
			return &typechecker.BoolType{}
		}
	}

	return nil
}

// checkWhileStatement handles while loops
func (bc *BorrowChecker) checkWhileStatement(stmt *ast.WhileStatement, env *typechecker.TypeEnvironment) {
	// Check condition
	bc.checkExpression(stmt.Condition, env)

	// Check body (which is a BlockStatement)
	bc.checkBlockStatement(stmt.Body, env)
}

// checkAssignmentStatement handles assignments
func (bc *BorrowChecker) checkAssignmentStatement(stmt *ast.AssignmentStatement, env *typechecker.TypeEnvironment) {
	// Check the value being assigned
	bc.checkExpression(stmt.Value, env)

	// Check if we're assigning to an owner (which might be borrowed)
	// The left-hand side is an expression (could be identifier, index, etc.)
	bc.checkExpression(stmt.Name, env)
}

// dropBorrowsInCurrentBlock removes borrows created in the current block
// and recomputes owner states based on remaining active borrows
func (bc *BorrowChecker) dropBorrowsInCurrentBlock() {
	// Remove borrows created in this block
	for name, info := range bc.activeBorrows {
		if info.blockDepth == bc.currentBlockDepth {
			delete(bc.activeBorrows, name)
			delete(bc.ownerOf, name)
		}
	}

	// Recompute owner states from remaining active borrows
	// Start by marking all owners as Free
	for owner := range bc.ownerStates {
		bc.ownerStates[owner] = Free
	}

	// Scan remaining borrows and set SharedRead/UniqueWrite appropriately
	// With v2 region-level disjointness, we can have multiple spans if regions are disjoint
	hasViews := make(map[string]bool)
	hasSpans := make(map[string]bool)
	
	for _, info := range bc.activeBorrows {
		switch info.kind {
		case BorrowSpan:
			hasSpans[info.owner] = true
		case BorrowView:
			hasViews[info.owner] = true
		}
	}
	
	// Set owner states based on remaining borrows
	for owner := range bc.ownerStates {
		if hasViews[owner] && hasSpans[owner] {
			// This shouldn't happen if we enforce correctly, but handle it
			bc.addError(fmt.Sprintf("owner '%s' has both views and spans (should be impossible)", owner))
		} else if hasSpans[owner] {
			// Has spans (may be multiple if regions are disjoint)
			bc.ownerStates[owner] = UniqueWrite
		} else if hasViews[owner] {
			// Has views
			bc.ownerStates[owner] = SharedRead
		}
		// If neither, state remains Free (set above)
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
	// Use type information from the environment to classify the variable
	typeScheme, ok := env.Get(varName)
	if ok && typeScheme != nil {
		typ := typeScheme.Type
		if arrayType, ok := typ.(*typechecker.ArrayType); ok {
			if !arrayType.IsSlice && !arrayType.IsSpan && arrayType.Length >= 0 {
				// This is an owned array [N]T - initialize its borrow state
				bc.ownerStates[varName] = Free
			}
			// Views ([]T) and spans ([*]T) are tracked as borrows, not owners
		}
	} else if vd.Type != nil {
		// Type wasn't in environment yet - try to parse it from AST
		// This is a fallback for when type checking hasn't run yet
		// In practice, borrow checking should run after type checking
		// For now, we can't determine the type without the typechecker
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
	case *ast.Identifier:
		// Check if this is using an owner while it's borrowed
		bc.checkIdentifierUse(e.Value, env)
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
		// Note: Function bodies are Expressions, but they're handled in checkFunctionStatement
	}
}

// extractConstantInt extracts a constant integer value from an expression
// Returns the value and true if it's a compile-time constant, or 0, false otherwise
func (bc *BorrowChecker) extractConstantInt(expr ast.Expression, ownerLength int64) (int64, bool) {
	if expr == nil {
		return 0, true // nil means default (0 for low, len for high)
	}
	
	if intLit, ok := expr.(*ast.IntegerLiteral); ok {
		val := intLit.Value
		// Handle negative indices: if val < 0, convert to len + val
		if val < 0 {
			if ownerLength < 0 {
				// Can't normalize negative index without knowing length
				return 0, false
			}
			val = ownerLength + val
		}
		return val, true
	}
	
	// Not a constant - can't prove disjointness
	return 0, false
}

// extractSliceRegion extracts region information from a slice expression
// Returns region and true if bounds are compile-time constants, or nil, false otherwise
func (bc *BorrowChecker) extractSliceRegion(slice *ast.SliceExpression, ownerLength int64) (*Region, bool) {
	// Extract low bound
	low, lowIsConst := bc.extractConstantInt(slice.Low, ownerLength)
	if !lowIsConst && slice.Low != nil {
		return nil, false
	}
	
	// Extract high bound
	high, highIsConst := bc.extractConstantInt(slice.High, ownerLength)
	if !highIsConst && slice.High != nil {
		return nil, false
	}
	
	// Handle defaults
	if slice.Low == nil {
		low = 0
	}
	if slice.High == nil {
		if ownerLength < 0 {
			return nil, false // Can't compute default high without length
		}
		high = ownerLength
	}
	
	// Validate bounds
	if low < 0 || high < low {
		return nil, false // Invalid bounds
	}
	
	return &Region{
		Offset: low,
		Length: high - low,
	}, true
}

// checkSliceExpression checks slice operations for borrow creation
func (bc *BorrowChecker) checkSliceExpression(slice *ast.SliceExpression, env *typechecker.TypeEnvironment, targetVar string) {
	// Check the sequence being sliced (the array/view/span)
	bc.checkExpression(slice.Seq, env)

	// According to the spec, slicing an owned array [N]T creates a View borrow
	// Slicing a View/[]T or Span/[*]T creates a derived subslice (no new borrow)

	// Extract owner from slice.Seq - only returns non-empty for true owners
	ownerName := bc.extractOwnerName(slice.Seq)
	if ownerName != "" {
		// This is slicing an owned array - creates a View borrow
		if targetVar != "" {
			// Try to extract region information for disjointness checks
			var region *Region
			if scheme, ok := env.Get(ownerName); ok {
				if arrType, ok := scheme.Type.(*typechecker.ArrayType); ok && arrType.Length >= 0 {
					// We know the owner's length - try to extract constant bounds
					if r, ok := bc.extractSliceRegion(slice, arrType.Length); ok {
						region = r
					}
				}
			}
			bc.createViewBorrowWithRegion(ownerName, targetVar, region)
		}
		return
	}

	// Not an owner - check if it's a view/span being sliced (subslice)
	if ident, ok := slice.Seq.(*ast.Identifier); ok {
		// Check if this identifier is a borrow
		if sourceInfo, isBorrow := bc.activeBorrows[ident.Value]; isBorrow {
			// This is a subslice - share the same owner
			if targetVar != "" {
				// Try to compute the new region from the source region
				var newRegion *Region
				if sourceInfo.region != nil {
					// We have source region info - compute new region
					// For now, we can't compute this without knowing the source's offset
					// This would require tracking the full region chain
					// For v2, we'll track relative offsets
					newRegion = nil // Can't compute without more info
				}
				bc.createSubsliceWithRegion(ident.Value, targetVar, newRegion)
			}
			return
		}
		
		// Check type from environment to determine if this should be a borrow
		// Use type information to classify the identifier
		if scheme, ok := env.Get(ident.Value); ok {
			if arrType, ok := scheme.Type.(*typechecker.ArrayType); ok {
				if arrType.IsSlice {
					// This is a []T (view) - treat as existing borrow for subslice
					if targetVar != "" {
						// We need to find the owner - for now, treat as subslice of unknown source
						// In a full implementation, we'd track the source borrow
						bc.addError(fmt.Sprintf("cannot create subslice '%s': source '%s' is a view but owner is unknown", targetVar, ident.Value))
					}
					return
				} else if arrType.IsSpan {
					// This is a [*]T (span) - treat as existing borrow for subslice
					if targetVar != "" {
						bc.addError(fmt.Sprintf("cannot create subslice '%s': source '%s' is a span but owner is unknown", targetVar, ident.Value))
					}
					return
				}
			}
		}
	}
}

// extractOwnerName extracts the owner variable name from an expression
// Returns empty string if the expression is not an owned array reference
// This only returns non-empty for true owners (variables in ownerStates)
func (bc *BorrowChecker) extractOwnerName(expr ast.Expression) string {
	switch e := expr.(type) {
	case *ast.Identifier:
		// Only return non-empty if this is a true owner (has borrow state tracked)
		if _, exists := bc.ownerStates[e.Value]; exists {
			return e.Value
		}
		// Not an owner - could be a borrow or other variable
		return ""
	case *ast.PrefixExpression:
		// Handle *arr (pointer dereference for view()/span() calls)
		if e.Operator == "*" {
			if ident, ok := e.Right.(*ast.Identifier); ok {
				// Only return non-empty if the dereferenced identifier is an owned array
				if _, exists := bc.ownerStates[ident.Value]; exists {
					return ident.Value
				}
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
	// Check if this is a call to view(), span(), subslice(), view_as(), or span_as()
	if ident, ok := call.Function.(*ast.Identifier); ok {
		switch ident.Value {
		case "view":
			bc.checkViewCall(call, env, targetVar)
		case "span":
			bc.checkSpanCall(call, env, targetVar)
		case "subslice":
			bc.checkSubsliceCall(call, env, targetVar)
		case "view_as":
			bc.checkViewAsCall(call, env, targetVar)
		case "span_as":
			bc.checkSpanAsCall(call, env, targetVar)
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
		// view() creates a view of the entire array - region is [0, length)
		var region *Region
		if scheme, ok := env.Get(ownerName); ok {
			if arrType, ok := scheme.Type.(*typechecker.ArrayType); ok && arrType.Length >= 0 {
				region = &Region{
					Offset: 0,
					Length: arrType.Length,
				}
			}
		}
		bc.createViewBorrowWithRegion(ownerName, targetVar, region)
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
		// span() creates a span of the entire array - region is [0, length)
		var region *Region
		if scheme, ok := env.Get(ownerName); ok {
			if arrType, ok := scheme.Type.(*typechecker.ArrayType); ok && arrType.Length >= 0 {
				region = &Region{
					Offset: 0,
					Length: arrType.Length,
				}
			}
		}
		bc.createSpanBorrowWithRegion(ownerName, targetVar, region)
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

// checkViewAsCall handles view_as() calls: creates a derived view borrow with different element type
func (bc *BorrowChecker) checkViewAsCall(call *ast.InvocationExpression, env *typechecker.TypeEnvironment, targetVar string) {
	if len(call.Arguments) != 1 {
		bc.addError("view_as() expects exactly one argument")
		return
	}

	// The argument should be an existing view ([]T)
	// view_as reinterprets the view but doesn't create a new borrow from the owner
	if ident, ok := call.Arguments[0].(*ast.Identifier); ok {
		// Check if this is an existing borrow
		if sourceInfo, exists := bc.activeBorrows[ident.Value]; exists {
			if sourceInfo.kind == BorrowView {
				// This is a view - create a derived view borrow (like subslice)
				if targetVar != "" {
					bc.createSubslice(ident.Value, targetVar)
				}
			} else {
				bc.addError("view_as() argument must be a view ([]T), got span ([*]T)")
			}
		} else {
			// Check type from environment
			if scheme, ok := env.Get(ident.Value); ok {
				if arrType, ok := scheme.Type.(*typechecker.ArrayType); ok {
					if arrType.IsSlice {
						// This is a []T but not tracked - might be from outer scope
						// For now, we'll allow it but can't track the owner
						bc.addError(fmt.Sprintf("view_as() argument '%s' is a view but owner is unknown (may be from outer scope)", ident.Value))
					} else {
						bc.addError("view_as() argument must be a view ([]T)")
					}
				}
			}
		}
	} else {
		bc.addError("view_as() argument must be a view variable")
	}
}

// checkSpanAsCall handles span_as() calls: creates a derived span borrow with different element type
func (bc *BorrowChecker) checkSpanAsCall(call *ast.InvocationExpression, env *typechecker.TypeEnvironment, targetVar string) {
	if len(call.Arguments) != 1 {
		bc.addError("span_as() expects exactly one argument")
		return
	}

	// The argument should be an existing span ([*]T)
	// span_as reinterprets the span but doesn't create a new borrow from the owner
	if ident, ok := call.Arguments[0].(*ast.Identifier); ok {
		// Check if this is an existing borrow
		if sourceInfo, exists := bc.activeBorrows[ident.Value]; exists {
			if sourceInfo.kind == BorrowSpan {
				// This is a span - create a derived span borrow (like subslice)
				if targetVar != "" {
					bc.createSubslice(ident.Value, targetVar)
				}
			} else {
				bc.addError("span_as() argument must be a span ([*]T), got view ([]T)")
			}
		} else {
			// Check type from environment
			if scheme, ok := env.Get(ident.Value); ok {
				if arrType, ok := scheme.Type.(*typechecker.ArrayType); ok {
					if arrType.IsSpan {
						// This is a [*]T but not tracked - might be from outer scope
						bc.addError(fmt.Sprintf("span_as() argument '%s' is a span but owner is unknown (may be from outer scope)", ident.Value))
					} else {
						bc.addError("span_as() argument must be a span ([*]T)")
					}
				}
			}
		}
	} else {
		bc.addError("span_as() argument must be a span variable")
	}
}

// checkIdentifierUse checks if an identifier is being used while its owner is borrowed
// This enforces that owners cannot be used directly while they have active borrows
func (bc *BorrowChecker) checkIdentifierUse(name string, env *typechecker.TypeEnvironment) {
	// Check if this is an owner
	state, isOwner := bc.ownerStates[name]
	if !isOwner {
		// Not an owner - could be a borrow or other variable, no restriction
		return
	}

	// This is an owner - check if it's being used while borrowed
	if state == UniqueWrite {
		// Owner has an active writable span - disallow direct use
		bc.addError(fmt.Sprintf("cannot use owner '%s' while it has an active writable span", name))
		return
	}

	// For SharedRead state, we might allow reads but disallow writes
	// For now, we'll be conservative and allow reads but could be more restrictive
	// This can be refined based on the memory model requirements
}

// createViewBorrow creates a read-only borrow (view) from an owner
func (bc *BorrowChecker) createViewBorrow(ownerName, borrowName string) {
	bc.createViewBorrowWithRegion(ownerName, borrowName, nil)
}

// createViewBorrowWithRegion creates a read-only borrow (view) from an owner with region information
func (bc *BorrowChecker) createViewBorrowWithRegion(ownerName, borrowName string, region *Region) {
	state := bc.ownerStates[ownerName]
	if state == UniqueWrite {
		bc.addError(fmt.Sprintf("cannot create view '%s' from '%s': owner has active writable borrow", borrowName, ownerName))
		return
	}

	// Transition to SharedRead if not already
	bc.ownerStates[ownerName] = SharedRead
	bc.ownerOf[borrowName] = ownerName
	
	// Track this borrow with metadata
	bc.activeBorrows[borrowName] = borrowInfo{
		owner:      ownerName,
		kind:       BorrowView,
		blockDepth: bc.currentBlockDepth,
		region:     region,
	}
}

// createSpanBorrow creates a unique writable borrow (span) from an owner
func (bc *BorrowChecker) createSpanBorrow(ownerName, borrowName string) {
	bc.createSpanBorrowWithRegion(ownerName, borrowName, nil)
}

// regionsOverlap checks if two regions overlap
// Returns true if the regions overlap, false if they are disjoint
func (bc *BorrowChecker) regionsOverlap(r1, r2 *Region) bool {
	if r1 == nil || r2 == nil {
		// If either region is unknown, assume they might overlap (conservative)
		return true
	}
	
	// Two regions [off1, off1+len1) and [off2, off2+len2) overlap if:
	// off1 < off2+len2 && off2 < off1+len1
	return r1.Offset < r2.Offset+r2.Length && r2.Offset < r1.Offset+r1.Length
}

// createSpanBorrowWithRegion creates a unique writable borrow (span) from an owner with region information
// This implements v2 region-level disjointness: multiple spans are allowed if their regions are provably disjoint
func (bc *BorrowChecker) createSpanBorrowWithRegion(ownerName, borrowName string, region *Region) {
	state := bc.ownerStates[ownerName]
	
	// Check for existing spans on the same owner
	existingSpans := []borrowInfo{}
	for _, info := range bc.activeBorrows {
		if info.owner == ownerName && info.kind == BorrowSpan {
			existingSpans = append(existingSpans, info)
		}
	}
	
	if len(existingSpans) > 0 {
		// We have existing spans - check if regions are disjoint
		if region != nil {
			// We have region information - check disjointness
			allDisjoint := true
			for _, existing := range existingSpans {
				if existing.region != nil {
					if bc.regionsOverlap(region, existing.region) {
						allDisjoint = false
						break
					}
				} else {
					// Existing span has unknown region - can't prove disjointness
					allDisjoint = false
					break
				}
			}
			
			if allDisjoint {
				// All regions are disjoint - allow multiple spans
				// Don't change owner state - we track multiple spans now
				bc.ownerOf[borrowName] = ownerName
				bc.activeBorrows[borrowName] = borrowInfo{
					owner:      ownerName,
					kind:       BorrowSpan,
					blockDepth: bc.currentBlockDepth,
					region:     region,
				}
				return
			}
		}
		
		// Can't prove disjointness - fall back to v1 behavior (reject)
		bc.addError(fmt.Sprintf("cannot create span '%s' from '%s': owner has active span borrows (state: %s). Use disjoint regions to allow multiple spans", borrowName, ownerName, state))
		return
	}
	
	// No existing spans - check for views
	if state == SharedRead {
		bc.addError(fmt.Sprintf("cannot create span '%s' from '%s': owner has active read-only views", borrowName, ownerName))
		return
	}
	
	// Transition to UniqueWrite (or keep Free if we're allowing multiple disjoint spans)
	if state == Free {
		bc.ownerStates[ownerName] = UniqueWrite
	}
	bc.ownerOf[borrowName] = ownerName
	
	// Track this borrow with metadata
	bc.activeBorrows[borrowName] = borrowInfo{
		owner:      ownerName,
		kind:       BorrowSpan,
		blockDepth: bc.currentBlockDepth,
		region:     region,
	}
}

// createSubslice creates a derived borrow (subslice) from an existing view/span
func (bc *BorrowChecker) createSubslice(sourceBorrowName, subsliceName string) {
	bc.createSubsliceWithRegion(sourceBorrowName, subsliceName, nil)
}

// createSubsliceWithRegion creates a derived borrow (subslice) from an existing view/span with region information
func (bc *BorrowChecker) createSubsliceWithRegion(sourceBorrowName, subsliceName string, newRegion *Region) {
	sourceInfo, exists := bc.activeBorrows[sourceBorrowName]
	if !exists {
		bc.addError(fmt.Sprintf("cannot create subslice '%s': source '%s' is not a borrow", subsliceName, sourceBorrowName))
		return
	}

	// Subslice shares the same owner and kind, created at same block depth
	// If we have region info, use it; otherwise inherit from source
	region := newRegion
	if region == nil {
		region = sourceInfo.region // Inherit region from source
	}
	
	bc.ownerOf[subsliceName] = sourceInfo.owner
	bc.activeBorrows[subsliceName] = borrowInfo{
		owner:      sourceInfo.owner,
		kind:       sourceInfo.kind, // Subslice preserves view/span kind
		blockDepth: sourceInfo.blockDepth,
		region:     region,
	}
	// No state change - subslices don't create new borrows from the owner
}
