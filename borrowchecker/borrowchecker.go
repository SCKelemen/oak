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
	// UniqueWrite means one or more writable borrows (Span/[*]T)
	// With region-level disjointness, multiple spans can coexist if regions don't overlap
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
	// nil *Region means the region is unknown (not a compile-time constant)
	// and we cannot prove disjointness
}

// borrowInfo tracks information about an active borrow
type borrowInfo struct {
	owner      string     // The owner variable name
	kind       borrowKind // Whether this is a view or span
	blockDepth int        // Block depth where this borrow was created
	region     *Region    // Exact absolute owner region, or nil when not statically known
	origin     ast.Node   // Source expression that created this borrow, when known
	parent     string     // Immediate source borrow for a derived view/span
	// reborrows lists live writable children, in creation order. While non-empty,
	// direct use of this span is suspended; siblings coexist only when their
	// regions are statically proven pairwise disjoint.
	reborrows []string
}

// BorrowChecker tracks borrow states and enforces borrowing rules
type BorrowChecker struct {
	staticStringFunctions map[string]bool
	globalWrites          map[string]map[string]bool
	globalOwners          map[string]bool
	// ownerStates maps owned array variable names to their current borrow state
	ownerStates map[string]BorrowState

	// ownerOf maps borrow variable names (views/spans) to their owner variable names
	// This is kept for backward compatibility and quick lookups
	ownerOf map[string]string

	// activeBorrows tracks all active borrows with their metadata
	activeBorrows map[string]borrowInfo

	// diagnostics are the first-class borrow-checking result. Errors() remains
	// a compatibility projection for older callers and tests.
	diagnostics *diagnosticsState

	// currentBlock tracks the current block scope for lexical borrowing
	// In v1, borrows cannot escape their creation block
	currentBlockDepth int

	// pendingReturn is the region contract of the function being checked
	// (borrowchecker/regions.go): its body's result must borrow from the
	// named parameter, checked while the body's borrows are still live.
	pendingReturn *regionContract
	// initializers and payloadBindings are the static shape of the function
	// being checked (borrowchecker/regions.go, collectStatics): what each
	// local was declared as and what each match payload binding projects.
	initializers    map[string]ast.Expression
	payloadBindings map[string]payloadBinding

	// unsafeDepth tracks lexical unsafe-block nesting (Oak.Unsafe.Scope).
	// Inside an unsafe boundary the checker may admit exactly the
	// writable-disjointness assumption, recording it as an auditable
	// warning; every other invariant remains checked.
	unsafeDepth int
	// consumedOwners names the Buffer bindings c.disown has handed back
	// (docs/spec/92-ffi.md section 2.8); any later use is rejected.
	consumedOwners map[string]bool
}

// New creates a new borrow checker
func New() *BorrowChecker {
	return &BorrowChecker{
		ownerStates:   make(map[string]BorrowState),
		ownerOf:       make(map[string]string),
		activeBorrows: make(map[string]borrowInfo),
		diagnostics:   newDiagnosticsState(),
	}
}

// Errors returns a compatibility text projection of first-class diagnostics.
func (bc *BorrowChecker) Errors() []string {
	return bc.diagnostics.errorStrings()
}

// ClearErrors clears all borrow diagnostics.
func (bc *BorrowChecker) ClearErrors() {
	bc.diagnostics.clear()
}

// addError is the migration fallback for borrow checks that have not yet been
// assigned a specific stable code. New checks should call reportBorrow.
func (bc *BorrowChecker) addError(msg string) {
	bc.reportBorrow(nil, CodeBorrowGeneric, msg)
}

// CheckProgram performs borrow checking on a program
func (bc *BorrowChecker) CheckProgram(program *ast.Program, env *typechecker.TypeEnvironment) {
	bc.ClearErrors()
	bc.ownerStates = make(map[string]BorrowState)
	bc.ownerOf = make(map[string]string)
	bc.activeBorrows = make(map[string]borrowInfo)
	bc.currentBlockDepth = 0
	bc.unsafeDepth = 0
	bc.consumedOwners = make(map[string]bool)
	bc.staticStringFunctions = make(map[string]bool)
	bc.collectGlobalWrites(program, env)
	for _, statement := range program.Statements {
		if fn, ok := statement.(*ast.FunctionStatement); ok && fn.Name != nil && literalStringResult(fn.Body) {
			bc.staticStringFunctions[fn.Name.Value] = true
		}
	}

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
	case *ast.IfStatement:
		bc.checkIfStatement(s, env)
	case *ast.AssignmentStatement:
		bc.checkAssignmentStatement(s, env)
	case *ast.UnsafeBlock:
		bc.checkUnsafeBlock(s, env)
	case *ast.IndexAssignmentStatement:
		bc.checkIndexAssignmentStatement(s, env)
	default:
		// Other statement types don't affect borrowing
	}
}

// checkUnsafeBlock checks an unsafe boundary (Oak.Unsafe): the body is
// checked like any block — unsafe does not disable checking — but while the
// boundary is open, the writable-disjointness obligation may be admitted as
// a recorded assumption instead of proven.
func (bc *BorrowChecker) checkUnsafeBlock(stmt *ast.UnsafeBlock, env *typechecker.TypeEnvironment) {
	if stmt == nil || stmt.Body == nil {
		return
	}
	bc.unsafeDepth++
	bc.checkBlockStatement(stmt.Body, env)
	bc.unsafeDepth--
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
	// The function body block: its result's provenance is checked while the
	// locals it may be bound through are still live.
	if bc.pendingReturn != nil && bc.currentBlockDepth == 1 && !bc.pendingReturn.checked {
		bc.checkReturnedProvenance((&ast.BlockExpression{Block: block}).Result(), bc.pendingReturn, env)
	}
}

// checkFunctionStatement handles function definitions with local scope
// Functions create a new lexical scope for borrow checking:
// - Borrows created inside the function do not affect outer scope (state is restored)
// - Functions can observe and respect outer borrows (they see current ownerStates/activeBorrows)
// - Local variables (parameters, receiver) can be owners
// - Function-local borrows are dropped when the function returns
func (bc *BorrowChecker) checkFunctionStatement(stmt *ast.FunctionStatement, env *typechecker.TypeEnvironment) {
	// Extern bindings have no Oak body and their c.* signatures carry no
	// borrowable owners: foreign pointers are opaque (docs/spec/92-ffi.md).
	if stmt.ExternSymbol != "" {
		return
	}

	// Save current borrow checker state
	// We snapshot state so borrows created inside don't leak out, but functions
	// can still see and respect outer borrows (e.g., can't take a span of an
	// outer owner that already has a view)

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
	savedPendingReturn := bc.pendingReturn
	savedInitializers, savedPayloads := bc.initializers, bc.payloadBindings
	bc.initializers, bc.payloadBindings = collectStatics(stmt.Body)

	// Reset to function-local state
	// We keep the outer environment for type lookups, but start fresh for borrows
	bc.currentBlockDepth = 0

	// Check function parameters - they might be owners
	// Check for nil function statement or name
	if stmt == nil || stmt.Name == nil {
		return
	}

	// The typechecker should have registered them in the function's environment
	// We need to get that environment - for now, we'll check types from the AST
	funcEnv := typechecker.NewEnclosedTypeEnvironment(env)

	// Register receiver if present
	if stmt.Receiver != nil && stmt.Receiver.Name != nil {
		receiverType := bc.parseTypeFromAST(stmt.Receiver.Type, funcEnv)
		bc.checkAggregateType(stmt.Receiver.Type, receiverType, env, false)
		bc.registerBorrowParameter(stmt.Receiver.Name.Value, receiverType, stmt.Receiver.Type)
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

	// Register parameters. A record parameter carrying borrows is admitted
	// when the signature gives it a region (docs/spec/50-borrowing.md
	// section 8c): its fields become borrows of synthetic owners like a
	// view parameter's; without a region it fails closed as any aggregate.
	regions := paramRegions(stmt, env)
	for index, param := range stmt.Parameters {
		paramType := bc.parseTypeFromAST(param.Type, funcEnv)
		if scheme, ok := env.Get(stmt.Name.Value); ok && scheme != nil {
			if fn, ok := scheme.Type.(*typechecker.FunctionType); ok && index < len(fn.Parameters) {
				paramType = fn.Parameters[index]
			}
		}
		if index < len(regions) && regions[index] != "" && !isDirectBorrowType(paramType) && env.ContainsBorrowStorage(paramType) {
			if bc.registerRegionAggregateParameter(param.Name.Value, paramType, param.Type, env) {
				funcEnv.SetType(param.Name.Value, paramType)
				continue
			}
		}
		bc.checkAggregateType(param.Type, paramType, env, false)
		bc.registerBorrowParameter(param.Name.Value, paramType, param.Type)
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

	// Escape discipline (docs/spec/50-borrowing.md section 5, Oak.Escape):
	// a borrow may not outlive the owner that proves its lifetime. A
	// region-indexed signature (section 8c, borrowchecker/regions.go) names
	// the parameter whose owner outlives the call and is checked by
	// provenance instead; every other view/span return is rejected.
	bc.pendingReturn = bc.returnContractFor(stmt, env)
	if bc.pendingReturn == nil {
		bc.checkBorrowEscape(stmt, env)
	}

	// Check function body. A block body arrives as an ast.BlockExpression
	// carrying every statement; checkExpression applies block scoping to it
	// and checks the returned provenance before the block's borrows drop.
	// An expression body is checked here, with the parameters still live.
	bc.checkExpression(stmt.Body, funcEnv)
	if bc.pendingReturn != nil {
		bc.checkReturnedProvenance(stmt.Body, bc.pendingReturn, funcEnv)
	}

	// At function end, all borrows created in the function are dropped
	// This happens automatically when we restore state

	// Restore outer state
	bc.ownerStates = savedOwnerStates
	bc.activeBorrows = savedActiveBorrows
	bc.ownerOf = savedOwnerOf
	bc.currentBlockDepth = savedBlockDepth
	bc.pendingReturn = savedPendingReturn
	bc.initializers, bc.payloadBindings = savedInitializers, savedPayloads
}

// checkBorrowEscape rejects function signatures that would let a borrow
// escape the function proving its owner's lifetime. Implementation of
// docs/spec/50-borrowing.md section 5: initially, returning a borrow is
// rejected outright; Oak.Escape proves the underlying discipline (dropping
// scope-local borrows on exit preserves owner liveness, an escaping borrow of
// a scope-local owner dangles) and that escapes of longer-lived owners are
// the sound headroom future region-indexed signatures can claim.
func (bc *BorrowChecker) checkBorrowEscape(stmt *ast.FunctionStatement, env *typechecker.TypeEnvironment) {
	resultType := env.CheckedExpressionType(stmt.Body)
	scheme, ok := env.Get(stmt.Name.Value)
	if ok && scheme != nil {
		if fnType, ok := scheme.Type.(*typechecker.FunctionType); ok {
			resultType = fnType.ReturnType
		}
	}
	kind := returnedBorrowKind(resultType, make(map[typechecker.Type]bool))
	if _, text := resultType.(*typechecker.StringType); text && literalStringResult(stmt.Body) {
		return
	}
	if kind == "" && env.ContainsBorrowStorage(resultType) {
		kind = "borrow"
	}
	if kind == "" {
		return
	}
	var origin ast.Node = stmt.ReturnType
	if origin == nil {
		origin = stmt.Name
	}
	d := bc.reportBorrow(origin, CodeBorrowEscape,
		fmt.Sprintf("function %q returns a value containing a %s, which would let a borrow escape its owner's scope", stmt.Name.Value, kind))
	d.AddNote("borrows are lexically scoped: a view or span may not outlive the function that proves its owner's lifetime")
	d.AddHelp("return owned data, or take a caller-provided span to fill; region-indexed signatures that prove the owner outlives the call are a planned extension")
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
			}
			// Note: []T slice syntax is not represented as IndexExpression with empty identifier
			// This branch is dead code - slice types should be parsed from the type environment
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

// checkIfStatement checks the conditional's condition and both branches.
// Branches are checked in sequence against the same incoming state: a
// borrow created inside one branch is block-scoped and released at the
// branch's end, and conservative sequential checking over-approximates
// (never under-approximates) the set of live borrows.
func (bc *BorrowChecker) checkIfStatement(stmt *ast.IfStatement, env *typechecker.TypeEnvironment) {
	bc.checkExpression(stmt.Condition, env)
	if stmt.Consequence != nil {
		bc.checkBlockStatement(stmt.Consequence, env)
	}
	switch alternative := stmt.Alternative.(type) {
	case *ast.IfStatement:
		bc.checkIfStatement(alternative, env)
	case *ast.BlockStatement:
		bc.checkBlockStatement(alternative, env)
	}
}

// checkAssignmentStatement handles assignments
func (bc *BorrowChecker) checkAssignmentStatement(stmt *ast.AssignmentStatement, env *typechecker.TypeEnvironment) {
	bc.checkAggregateStorage(stmt.Value, env, false)
	if isDirectBorrowType(env.CheckedExpressionType(stmt.Value)) {
		bc.reportBorrow(stmt.Name, CodeBorrowReassign, "borrowed values require a new binding and cannot be assigned into an existing binding")
		return
	}
	// Borrows are immutable bindings - cannot reassign a variable that currently holds a view/span
	if info, exists := bc.activeBorrows[stmt.Name.Value]; exists {
		d := bc.reportBorrow(stmt.Name, CodeBorrowReassign,
			fmt.Sprintf("borrow %q cannot be reassigned", stmt.Name.Value))
		bc.addBorrowContext(d, stmt.Name.Value, info,
			"this binding already carries borrowed access")
		d.AddNote("views and spans are non-owning access paths tied to their backing owner")
		d.AddHelp("create a new view/span binding, or end the current borrow before reusing the name")
		return
	}

	// Check the value being assigned
	// If this creates a borrow (e.g., view(&arr) or subslice(v)), pass the target variable
	// so the borrow is tracked correctly
	bc.checkExpression(stmt.Value, env, stmt.Name.Value)

	// Check if we're assigning to an owner (which might be borrowed)
	// The left-hand side is an Identifier (assignment target)
	// This is a write operation
	bc.checkIdentifierUse(stmt.Name, stmt.Name.Value, env, true)
}

// checkIndexAssignmentStatement checks s[i] = value: writing through a span
// is a use of that borrow (suspended-reborrow rules apply); writing an owned
// array element directly is an owner write (view exclusivity applies).
func (bc *BorrowChecker) checkIndexAssignmentStatement(stmt *ast.IndexAssignmentStatement, env *typechecker.TypeEnvironment) {
	if stmt == nil || stmt.Target == nil {
		return
	}
	bc.checkAggregateStorage(stmt.Value, env, true)
	bc.checkExpression(stmt.Value, env)
	bc.checkExpression(stmt.Target.Index, env)
	if ident, ok := stmt.Target.Left.(*ast.Identifier); ok {
		bc.checkIdentifierUse(ident, ident.Value, env, true)
		return
	}
	bc.checkExpression(stmt.Target.Left, env)
}

// dropBorrowsInCurrentBlock removes borrows created in the current block
// and recomputes owner states based on remaining active borrows
func (bc *BorrowChecker) dropBorrowsInCurrentBlock() {
	for name, info := range bc.activeBorrows {
		if info.blockDepth == bc.currentBlockDepth {
			bc.dropBorrow(name)
		}
	}

	bc.recomputeOwnerStatesFromActiveBorrows()
}

// dropBorrow removes one borrow and releases its slot in the parent's live
// reborrow list; the parent becomes directly usable once that list empties.
func (bc *BorrowChecker) dropBorrow(name string) {
	info, exists := bc.activeBorrows[name]
	if !exists {
		return
	}
	if info.parent != "" {
		if parent, ok := bc.activeBorrows[info.parent]; ok {
			parent.reborrows = removeName(parent.reborrows, name)
			bc.activeBorrows[info.parent] = parent
		}
	}
	delete(bc.activeBorrows, name)
	delete(bc.ownerOf, name)
}

// removeName removes the first occurrence of name, preserving creation order.
func removeName(names []string, name string) []string {
	for i, candidate := range names {
		if candidate == name {
			return append(names[:i], names[i+1:]...)
		}
	}
	return names
}

// recomputeOwnerStatesFromActiveBorrows recomputes owner states based on active borrows
// This is used both when dropping borrows at block end and when reassigning borrow variables
func (bc *BorrowChecker) recomputeOwnerStatesFromActiveBorrows() {
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
	// (Oak.BorrowStateRefinement.ownerStateFor: the recompute rule).
	for owner := range bc.ownerStates {
		state, ok := ownerStateFor(hasViews[owner], hasSpans[owner])
		if !ok {
			// The impossible state has no abstract representation
			// (Oak.BorrowStateRefinement.both_kinds_flagged).
			bc.addError(fmt.Sprintf("owner '%s' has both views and spans (should be impossible)", owner))
			continue
		}
		bc.ownerStates[owner] = state
	}
}

// checkVariableDeclaration checks variable declarations for borrow creation
func (bc *BorrowChecker) checkVariableDeclaration(vd *ast.VariableDeclaration, env *typechecker.TypeEnvironment) {
	varName := vd.Name.Value
	// A local record holding views or spans is admitted when every borrow
	// it carries is accounted for (borrowchecker/aggregate_storage.go); the
	// binding then borrows those owners itself. Anything else fails closed.
	declared := env.CheckedDeclarationType(vd)
	if !bc.bindAggregateBorrows(varName, declared, vd.Value, env) {
		// A region-indexed call binds its result through the call itself
		// (borrowchecker/regions.go); anything else fails closed.
		if _, _, _, isRegionCall := regionCallResult(vd.Value, env); !isRegionCall {
			bc.checkAggregateType(vd.Name, declared, env, false)
		}
	}

	// Check if the value expression creates a borrow (check before we register the variable)
	if vd.Value != nil {
		bc.checkExpression(vd.Value, env, varName)
	}
	if _, text := env.CheckedDeclarationType(vd).(*typechecker.StringType); text {
		valueType := env.CheckedExpressionType(vd.Value)
		_, stringValue := valueType.(*typechecker.StringType)
		// Do not cascade lifetime errors from an already ill-typed initializer.
		if _, tracked := bc.activeBorrows[varName]; !tracked && (valueType == nil || stringValue) {
			bc.reportBorrow(vd.Name, CodeBorrowEscape, "string binding requires a literal or a tracked string borrow")
		}
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
		if _, isBuffer := typ.(*typechecker.BufferType); isBuffer {
			// An owned foreign buffer is an owner of runtime length
			// (docs/spec/92-ffi.md section 2.8).
			bc.ownerStates[varName] = Free
		}
	} else if vd.Type != nil {
		// Function-local declarations are not in the surviving global
		// environment; classify owners from the checker's recorded
		// declaration type (which resolves every element type, tagged
		// unions included), falling back to the declared type's syntax.
		declared := env.CheckedDeclarationType(vd)
		if declared == nil {
			declared = bc.parseTypeFromAST(vd.Type, env)
		}
		if _, isBuffer := declared.(*typechecker.BufferType); isBuffer {
			bc.ownerStates[varName] = Free
		}
		if arrType, ok := declared.(*typechecker.ArrayType); ok {
			if !arrType.IsSlice && !arrType.IsSpan && arrType.Length >= 0 {
				bc.ownerStates[varName] = Free
			}
		}
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
		// This is a read operation (not an assignment target)
		bc.checkIdentifierUse(e, e.Value, env, false)
		if targetVar != "" {
			if source, tracked := bc.activeBorrows[e.Value]; tracked {
				bc.createSubsliceWithRegion(e.Value, targetVar, source.region, e)
			}
		}
	case *ast.StringLiteral:
		if targetVar != "" {
			bc.createViewBorrowWithRegion("$literal:"+targetVar, targetVar, nil, e)
		}
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
	case *ast.MatchExpression:
		bc.checkExpression(e.Scrutinee, env)
		scrutinee, _ := fieldPath(e.Scrutinee)
		for _, arm := range e.Arms {
			// A variant pattern's payload binding reborrows what the
			// scrutinee carries under that variant, for the arm only
			// (docs/spec/50-borrowing.md section 8c).
			variant, ok := arm.Pattern.(*ast.VariantPattern)
			if ok && scrutinee != "" && variant.Variant != nil {
				if binding, isBinding := variant.Payload.(*ast.BindingPattern); isBinding && binding.Name != nil {
					bc.currentBlockDepth++
					bc.bindPayload(scrutinee, variant.Variant.Value, binding.Name.Value, arm.Pattern)
					bc.checkExpression(arm.Body, env)
					bc.dropBorrowsInCurrentBlock()
					bc.currentBlockDepth--
					continue
				}
			}
			bc.checkExpression(arm.Body, env)
		}
		if targetVar != "" && literalStringResult(e) {
			bc.createViewBorrowWithRegion("$literal-match:"+targetVar, targetVar, nil, e)
		}
	case *ast.RecordLiteral:
		for _, field := range e.Fields {
			bc.checkExpression(field, env)
		}
	case *ast.ArrayLiteral:
		for _, element := range e.Elements {
			bc.checkExpression(element, env)
		}
	case *ast.VariantExpression:
		bc.checkExpression(e.Payload, env)
	case *ast.FunctionLiteral:
		body := &ast.BlockExpression{Block: e.Body}
		if len(bc.activeBorrows) != 0 {
			bc.reportBorrow(e, CodeBorrowEscape, "function literals in a borrow scope require capture-lifetime analysis")
		}
		if fn, ok := env.CheckedExpressionType(e).(*typechecker.FunctionType); ok && env.ContainsBorrowStorage(fn.ReturnType) && !literalStringResult(body) {
			bc.reportBorrow(e, CodeBorrowEscape, "function literal cannot return borrowed storage")
		}
		bc.checkExpression(body, env)
	case *ast.BlockExpression:
		// A block in expression position (most importantly a function block
		// body): statements are checked under block scoping, so borrows
		// created inside are dropped when the block ends.
		if e.Block != nil {
			bc.checkBlockStatement(e.Block, env)
		}
	default:
		// Other expressions don't create borrows
		// Note: Function bodies are Expressions, but they're handled in checkFunctionStatement
		// If the body contains nested statements (e.g., in let expressions), those would need
		// to be handled by the expression's own checking logic
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

	// Validate bounds against the sequence whose indices these are.
	if low < 0 || high < low || ownerLength < 0 || high > ownerLength {
		return nil, false
	}

	return &Region{
		Offset: low,
		Length: high - low,
	}, true
}

// checkSliceExpression checks slice operations for borrow creation
func (bc *BorrowChecker) checkSliceExpression(slice *ast.SliceExpression, env *typechecker.TypeEnvironment, targetVar string) {
	// A borrow named as the sequence of a bound slice is a derivation source,
	// not a direct use: deriving a disjoint sibling from a suspended parent is
	// legal, and createSubsliceWithRegion is the single authority for whether
	// the derivation is allowed. Every other sequence takes the normal use check.
	seqIdent, seqIsIdent := slice.Seq.(*ast.Identifier)
	var sourceInfo borrowInfo
	seqIsBorrow := false
	if seqIsIdent {
		sourceInfo, seqIsBorrow = bc.activeBorrows[seqIdent.Value]
	}
	if !seqIsBorrow || targetVar == "" {
		bc.checkExpression(slice.Seq, env)
	}

	// Check slice bounds expressions for any borrow-sensitive operations
	if slice.Low != nil {
		bc.checkExpression(slice.Low, env)
	}
	if slice.High != nil {
		bc.checkExpression(slice.High, env)
	}

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
			bc.createViewBorrowWithRegion(ownerName, targetVar, region, slice)
		}
		return
	}

	// Not an owner - check if it's a view/span being sliced (subslice)
	if seqIsIdent {
		ident := seqIdent
		if seqIsBorrow {
			if targetVar != "" {
				var newRegion *Region
				if sourceInfo.region != nil {
					if relative, ok := bc.extractSliceRegion(slice, sourceInfo.region.Length); ok {
						if absolute, ok := deriveRegion(sourceInfo.region, relative); ok {
							newRegion = absolute
						}
					}
				}
				bc.createSubsliceWithRegion(ident.Value, targetVar, newRegion, slice)
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
		// Handle *arr (pointer dereference) and &arr (address-of) for view()/span() calls
		if e.Operator == "*" || e.Operator == "&" {
			if ident, ok := e.Right.(*ast.Identifier); ok {
				// Only return non-empty if the identifier is an owned array
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
	bc.checkCallGlobalWrites(call, env)
	// An Objective-C message send (docs/spec/92-ffi.md section 2.12) calls
	// the runtime under a signature the program asserts for the selector's
	// implementation: the same kind of contract c.fn_at records, under the
	// same code, so `admit OAK-B0122` accepts both and nothing else does.
	if signature, isSend := typechecker.MessageSendCallee(call.Function); isSend {
		d := bc.reportForeignFunctionAssumption(call,
			"message send contract assumed: the selector's implementation has the bracketed signature, with the receiver and selector as its two leading pointer parameters",
			"c.msg_send")
		d.AddNote("the assumption is the sender's, as for an extern prototype (docs/spec/92-ffi.md section 2.12); every argument passes exactly the declared boundary types, and the receiver and selector are opaque c.Ptr values")
		_ = signature
	}
	// A borrow named as the first argument of a bound derive builtin is a
	// derivation source, not a direct use; createSubsliceWithRegion is the
	// single authority for whether the derivation is allowed.
	skipDerivationSource := false
	if ident, ok := call.Function.(*ast.Identifier); ok && targetVar != "" && len(call.Arguments) > 0 {
		switch ident.Value {
		case "subslice", "view_as", "span_as":
			if firstIdent, ok := call.Arguments[0].(*ast.Identifier); ok {
				_, skipDerivationSource = bc.activeBorrows[firstIdent.Value]
			}
		case "view", "span":
			// &owner in a borrow-creation position is not a direct use of the
			// owner; createViewBorrowWithRegion/createSpanBorrowWithRegion is
			// the single authority for whether the borrow is allowed.
			skipDerivationSource = bc.extractOwnerName(call.Arguments[0]) != ""
		}
	}

	// 1. Check arguments FIRST under the pre-call state
	// This ensures that argument validation happens before any borrow state changes
	//
	// A string view conversion written directly as an argument
	// (`f(str_bytes("x"))`, `f(str_bytes(name))`) is a temporary with the
	// call's extent (F9): it borrows its literal or tracked string source
	// like a named view would, is dropped when the call returns, and never
	// outlives the callee, which cannot return a view (OAK-B0109).
	var temporaries []string
	defer func() {
		for _, name := range temporaries {
			bc.dropBorrow(name)
		}
		if len(temporaries) > 0 {
			bc.recomputeOwnerStatesFromActiveBorrows()
		}
	}()
	for i, arg := range call.Arguments {
		if inner, ok := arg.(*ast.InvocationExpression); ok && isStringViewConversion(inner) {
			name := fmt.Sprintf("$argument:%d:%p", i, call)
			bc.checkStringViewCall(inner, env, name)
			temporaries = append(temporaries, name)
			continue
		}
		// A boundary span (docs/spec/92-ffi.md section 2.5.2) is a read use
		// of the view's owner, or a write use of the span's owner, for the
		// extent of the foreign call — the rule an Oak callee taking []T or
		// [*]T already gets. The pointer never outlives the call: the form
		// has no type and the typechecker admits it in no other position.
		if operand, mutable, isSpan := boundarySpanOperand(arg, env); isSpan {
			bc.checkIdentifierUse(operand, operand.Value, env, mutable)
			continue
		}
		// A C string from Oak bytes (docs/spec/92-ffi.md section 2.5.3) is a
		// read use of the view's owner for the extent of the foreign call;
		// a literal operand borrows nothing.
		if operand, isLiteral, isCString := cStringOperand(arg, env); isCString {
			if !isLiteral {
				bc.checkIdentifierUse(operand, operand.Value, env, false)
			}
			continue
		}
		// An argument vector (docs/spec/92-ffi.md section 2.5.6) reads the
		// strings' owner and writes the slots' owner for the extent of the
		// foreign call; an out-parameter (section 2.5.7) writes its local.
		if bytes, slots, isArgv := argvOperands(arg, env); isArgv {
			bc.checkIdentifierUse(bytes, bytes.Value, env, false)
			bc.checkIdentifierUse(slots, slots.Value, env, true)
			continue
		}
		if operand, isOut := outOperand(arg, env); isOut {
			bc.checkIdentifierUse(operand, operand.Value, env, true)
			continue
		}
		// A borrow-carrying record may be passed to a parameter that
		// declares its region (docs/spec/50-borrowing.md section 8c) when
		// the argument's borrows are tracked; otherwise aggregates fail
		// closed.
		regionAccepted := false
		if callee, isIdent := call.Function.(*ast.Identifier); isIdent && regionParameterAccepts(callee.Value, i, env) {
			if _, traced := bc.sourceBorrows(arg, env); traced {
				regionAccepted = true
			}
		}
		if !regionAccepted {
			bc.checkAggregateStorage(arg, env, false)
		}
		if i == 0 && skipDerivationSource {
			continue
		}
		bc.checkExpression(arg, env)
	}

	// An inbound buffer borrow (docs/spec/92-ffi.md section 2.7): the
	// binding borrows a foreign owner that lives exactly as long as the
	// enclosing block, so the view or span is dropped at the block's end
	// and cannot escape it, and the assumption the program makes about the
	// runtime's memory is recorded where every other unsafe assumption is.
	// A foreign function pointer (docs/spec/92-ffi.md section 2.10): the
	// binding names a function at an address the program vouches for;
	// the contract is recorded like the foreign-buffer one, under its own
	// code, so a module accepts it explicitly (`admit OAK-B0122`).
	if typechecker.ForeignFunctionAtCall(call) && targetVar != "" {
		d := bc.reportForeignFunctionAssumption(call,
			fmt.Sprintf("foreign function contract assumed for %q: the pointer is a function of the annotated signature, callable until the block ends", targetVar),
			targetVar)
		d.AddNote("the assumption is the binding author's, as for an extern prototype (docs/spec/92-ffi.md section 2.10); a NULL pointer traps at c.fn_at, and every call passes exactly the annotated argument types")
		return
	}
	if member, _, isForeign := typechecker.ForeignBorrowCall(call); isForeign && targetVar != "" {
		if member == "own" {
			// An owned foreign buffer (docs/spec/92-ffi.md section 2.8):
			// the binding is an owner, registered by its declaration; the
			// contract lasts until c.disown hands the memory back.
			d := bc.reportUnsafeAssumption(call,
				fmt.Sprintf("foreign buffer contract assumed for owner %q: the pointer addresses the given count of elements, valid and unaliased until c.disown(%s)", targetVar, targetVar),
				targetVar, nil, "", nil)
			d.AddNote("the assumption is the binding author's, as for an extern prototype (docs/spec/92-ffi.md section 2.8); indexing through its views and spans stays bounds-checked against the count")
			return
		}
		owner := "$foreign:" + targetVar
		if member == "borrow" || member == "borrow_string" {
			bc.createViewBorrowWithRegion(owner, targetVar, nil, call)
		} else {
			bc.createSpanBorrowWithRegion(owner, targetVar, nil, call)
		}
		contract := fmt.Sprintf("foreign buffer contract assumed for %q: the pointer addresses the given count of elements, valid and unaliased for writes until the block ends", targetVar)
		if member == "borrow_string" {
			// An inbound C string (docs/spec/92-ffi.md section 2.7.1): the
			// count is the terminator's offset, read at runtime.
			contract = fmt.Sprintf("foreign buffer contract assumed for %q: the pointer addresses a NUL-terminated string that stays valid and unwritten until the block ends", targetVar)
		}
		d := bc.reportUnsafeAssumption(call, contract, targetVar, nil, "", nil)
		d.AddNote("the assumption is the binding author's, as for an extern prototype (docs/spec/92-ffi.md section 2.7); indexing stays bounds-checked against the count")
		return
	}
	// c.disown(b) hands a buffer's memory back (docs/spec/92-ffi.md section
	// 2.8): rejected while any view or span of it is live, and the binding
	// is consumed afterward.
	if owner, isDisown := foreignDisownOperand(call); isDisown {
		if bc.consumedOwners[owner] {
			bc.reportBorrow(call, CodeResourceUsedAfterConsume,
				fmt.Sprintf("buffer %q was already handed back by c.disown", owner))
			return
		}
		for _, kind := range []borrowKind{BorrowSpan, BorrowView} {
			if borrowName, info, live := bc.firstActiveBorrow(owner, kind); live {
				d := bc.reportBorrow(call, CodeBorrowGeneric,
					fmt.Sprintf("buffer %q cannot be handed back while borrow %q is live", owner, borrowName))
				bc.addBorrowContext(d, borrowName, info, fmt.Sprintf("borrow %q still reads the buffer's memory", borrowName))
				d.AddHelp("let the view or span leave scope before c.disown")
				return
			}
		}
		bc.consumedOwners[owner] = true
		return
	}
	// A custody transition (docs/spec/92-ffi.md section 2.8.5) moves the
	// buffer: rejected while any borrow of it is live, and the old binding
	// is consumed; the result is the same resource under its new name.
	if owner, isTransition := custodyTransitionOperand(call, env); isTransition {
		if bc.consumedOwners[owner] {
			bc.reportBorrow(call, CodeResourceUsedAfterConsume,
				fmt.Sprintf("buffer %q was already moved or handed back", owner))
			return
		}
		for _, kind := range []borrowKind{BorrowSpan, BorrowView} {
			if borrowName, info, live := bc.firstActiveBorrow(owner, kind); live {
				d := bc.reportBorrow(call, CodeBorrowGeneric,
					fmt.Sprintf("buffer %q cannot change custody while borrow %q is live", owner, borrowName))
				bc.addBorrowContext(d, borrowName, info, fmt.Sprintf("borrow %q still reads the buffer's memory", borrowName))
				d.AddHelp("let the view or span leave scope before the transition")
				return
			}
		}
		bc.consumedOwners[owner] = true
		return
	}
	// 2. Then apply borrow-sensitive builtins
	// Arguments are already validated, so we can safely create borrows
	if ident, ok := call.Function.(*ast.Identifier); ok {
		switch ident.Value {
		case "str_from_utf8", "str_bytes":
			bc.checkStringViewCall(call, env, targetVar)
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
		if targetVar != "" && bc.staticStringFunctions[ident.Value] {
			bc.createViewBorrowWithRegion("$literal-call:"+targetVar, targetVar, nil, call)
		}
		// A region-indexed function (docs/spec/50-borrowing.md section 8c):
		// the binding reborrows the argument in the region position.
		if targetVar != "" {
			bc.bindRegionCall(call, targetVar, env)
		}
	}

	// For other non-builtin functions, the arg walk above is all we need.
}

// boundarySpanOperand recognizes `c.span_of(v)` / `c.span_mut_of(s)` in
// argument position (docs/spec/92-ffi.md section 2.5): the named operand and
// whether the foreign callee may write through it. A local binding named `c`
// shadows the library, as for every library call.
func boundarySpanOperand(arg ast.Expression, env *typechecker.TypeEnvironment) (operand *ast.Identifier, mutable, ok bool) {
	call, isCall := arg.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 1 {
		return nil, false, false
	}
	access, isAccess := call.Function.(*ast.IndexExpression)
	if !isAccess {
		return nil, false, false
	}
	library, isIdent := access.Left.(*ast.Identifier)
	member, memberIsIdent := access.Index.(*ast.Identifier)
	if !isIdent || !memberIsIdent || library.Value != "c" {
		return nil, false, false
	}
	if _, bound := env.Get("c"); bound {
		return nil, false, false
	}
	switch member.Value {
	case "span_of", "span_mut_of":
	default:
		return nil, false, false
	}
	operand, isIdent = call.Arguments[0].(*ast.Identifier)
	if !isIdent {
		return nil, false, false
	}
	return operand, member.Value == "span_mut_of", true
}

// cStringOperand recognizes `c.cstr(v)` in argument position
// (docs/spec/92-ffi.md section 2.5.3): the named view operand, or a literal
// (isLiteral) that borrows nothing. A local binding named `c` shadows the
// library, as for every other library call.
func cStringOperand(arg ast.Expression, env *typechecker.TypeEnvironment) (operand *ast.Identifier, isLiteral, ok bool) {
	call, isCall := arg.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != 1 {
		return nil, false, false
	}
	access, isAccess := call.Function.(*ast.IndexExpression)
	if !isAccess {
		return nil, false, false
	}
	library, isIdent := access.Left.(*ast.Identifier)
	member, memberIsIdent := access.Index.(*ast.Identifier)
	if !isIdent || !memberIsIdent || library.Value != "c" || member.Value != "cstr" {
		return nil, false, false
	}
	if _, bound := env.Get("c"); bound {
		return nil, false, false
	}
	if _, literal := call.Arguments[0].(*ast.StringLiteral); literal {
		return nil, true, true
	}
	operand, isIdent = call.Arguments[0].(*ast.Identifier)
	if !isIdent {
		return nil, false, false
	}
	return operand, false, true
}

// cLibraryMemberCall recognizes `c.<member>(...)` in argument position when
// no local binding named `c` shadows the library, returning the call.
func cLibraryMemberCall(arg ast.Expression, member string, arity int, env *typechecker.TypeEnvironment) (*ast.InvocationExpression, bool) {
	call, isCall := arg.(*ast.InvocationExpression)
	if !isCall || len(call.Arguments) != arity {
		return nil, false
	}
	access, isAccess := call.Function.(*ast.IndexExpression)
	if !isAccess {
		return nil, false
	}
	library, isIdent := access.Left.(*ast.Identifier)
	name, nameIsIdent := access.Index.(*ast.Identifier)
	if !isIdent || !nameIsIdent || library.Value != "c" || name.Value != member {
		return nil, false
	}
	if _, bound := env.Get("c"); bound {
		return nil, false
	}
	return call, true
}

// argvOperands recognizes `c.argv_of(bytes, slots)` in argument position
// (docs/spec/92-ffi.md section 2.5.6): the named view and span operands.
func argvOperands(arg ast.Expression, env *typechecker.TypeEnvironment) (bytes, slots *ast.Identifier, ok bool) {
	call, isArgv := cLibraryMemberCall(arg, "argv_of", 2, env)
	if !isArgv {
		return nil, nil, false
	}
	bytes, bytesIsIdent := call.Arguments[0].(*ast.Identifier)
	slots, slotsIsIdent := call.Arguments[1].(*ast.Identifier)
	if !bytesIsIdent || !slotsIsIdent {
		return nil, nil, false
	}
	return bytes, slots, true
}

// outOperand recognizes `c.out(x)` in argument position (docs/spec/92-ffi.md
// section 2.5.7): the named local the foreign callee writes.
func outOperand(arg ast.Expression, env *typechecker.TypeEnvironment) (operand *ast.Identifier, ok bool) {
	call, isOut := cLibraryMemberCall(arg, "out", 1, env)
	if !isOut {
		return nil, false
	}
	operand, isIdent := call.Arguments[0].(*ast.Identifier)
	if !isIdent {
		return nil, false
	}
	return operand, true
}

// checkViewCall handles view() calls: creates a read-only borrow
func (bc *BorrowChecker) checkViewCall(call *ast.InvocationExpression, env *typechecker.TypeEnvironment, targetVar string) {
	if len(call.Arguments) != 1 {
		bc.addError("view() expects exactly one argument")
		return
	}

	// The argument should be a pointer to an owned array: *[N]T
	// Note: extractOwnerName only handles direct &owner or *owner patterns
	ownerName := bc.extractOwnerName(call.Arguments[0])
	if ownerName == "" {
		bc.addError("view() argument must be &owner of an owned array")
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
		bc.createViewBorrowWithRegion(ownerName, targetVar, region, call)
	}
}

// checkSpanCall handles span() calls: creates a unique writable borrow
func (bc *BorrowChecker) checkSpanCall(call *ast.InvocationExpression, env *typechecker.TypeEnvironment, targetVar string) {
	if len(call.Arguments) != 1 {
		bc.addError("span() expects exactly one argument")
		return
	}

	// The argument should be a pointer to an owned array: *[N]T
	// Note: extractOwnerName only handles direct &owner or *owner patterns
	ownerName := bc.extractOwnerName(call.Arguments[0])
	if ownerName == "" {
		bc.addError("span() argument must be &owner of an owned array")
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
		bc.createSpanBorrowWithRegion(ownerName, targetVar, region, call)
	}
}

// checkSubsliceCall handles subslice() calls: creates a derived borrow
func (bc *BorrowChecker) checkSubsliceCall(call *ast.InvocationExpression, env *typechecker.TypeEnvironment, targetVar string) {
	if len(call.Arguments) != 3 {
		bc.addError("subslice() expects exactly three arguments (view/span, start, len)")
		return
	}

	// The source is a view/span binding, or a borrow field of a record
	// binding (cursor.data — docs/spec/50-borrowing.md sections 8b, 8c).
	sourceName, ok := fieldPath(call.Arguments[0])
	if !ok {
		bc.addError("subslice() first argument must be a view or span variable")
		return
	}
	if targetVar == "" {
		return
	}
	sourceInfo, exists := bc.activeBorrows[sourceName]
	if !exists {
		bc.createSubsliceWithRegion(sourceName, targetVar, nil, call)
		return
	}

	var region *Region
	if sourceInfo.region != nil {
		start, startOK := call.Arguments[1].(*ast.IntegerLiteral)
		length, lengthOK := call.Arguments[2].(*ast.IntegerLiteral)
		if startOK && lengthOK && start.Value >= 0 && length.Value >= 0 {
			relative := &Region{Offset: start.Value, Length: length.Value}
			if absolute, ok := deriveRegion(sourceInfo.region, relative); ok {
				region = absolute
			}
		}
	}
	bc.createSubsliceWithRegion(sourceName, targetVar, region, call)
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
					bc.createSubsliceWithRegion(ident.Value, targetVar, nil, call)
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
					bc.createSubsliceWithRegion(ident.Value, targetVar, nil, call)
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
// isWrite indicates if this is a write operation (assignment target)
func (bc *BorrowChecker) checkIdentifierUse(node ast.Node, name string, env *typechecker.TypeEnvironment, isWrite bool) {
	if bc.consumedOwners[name] {
		d := bc.reportBorrow(node, CodeResourceUsedAfterConsume,
			fmt.Sprintf("buffer %q cannot be used after c.disown handed its memory back", name))
		d.AddHelp("create a new buffer with c.own, or move the use before c.disown")
		return
	}
	if info, isBorrow := bc.activeBorrows[name]; isBorrow && len(info.reborrows) > 0 {
		title := fmt.Sprintf("writable span %q is suspended by reborrow %q", name, info.reborrows[0])
		if len(info.reborrows) > 1 {
			title = fmt.Sprintf("writable span %q is suspended by %d live reborrows", name, len(info.reborrows))
		}
		d := bc.reportBorrow(node, CodeBorrowSuspended, title)
		for _, childName := range info.reborrows {
			if child, ok := bc.activeBorrows[childName]; ok {
				bc.addBorrowContext(d, childName, child,
					fmt.Sprintf("reborrow %q temporarily holds part of this writable authority", childName))
			}
		}
		d.AddHelp("use the child spans, or let them leave scope before using the parent span again")
		return
	}

	// Check if this is an owner
	state, isOwner := bc.ownerStates[name]
	if !isOwner {
		// Not an owner - could be a borrow or other variable, no restriction
		return
	}

	// This is an owner - check if it's being used while borrowed.
	if state == UniqueWrite {
		d := bc.reportBorrow(node, CodeOwnerUsedDuringSpan,
			fmt.Sprintf("owner %q cannot be used while writable access is active", name))
		if borrowName, info, ok := bc.firstActiveBorrow(name, BorrowSpan); ok {
			bc.addBorrowContext(d, borrowName, info,
				fmt.Sprintf("writable span %q keeps exclusive access here", borrowName))
		}
		d.AddHelp("use the existing span for access, or let it leave scope before using the owner directly")
		return
	}

	if state == SharedRead && isWrite {
		d := bc.reportBorrow(node, CodeOwnerWrittenDuringView,
			fmt.Sprintf("owner %q cannot be written while read-only views are active", name))
		if borrowName, info, ok := bc.firstActiveBorrow(name, BorrowView); ok {
			bc.addBorrowContext(d, borrowName, info,
				fmt.Sprintf("read-only view %q observes this owner", borrowName))
		}
		d.AddHelp("finish using the views before mutating the owner")
		return
	}

	// SharedRead + read operation: allowed (multiple readers can coexist).
}

// The owner-state decision procedures below are maintained as line-for-line
// transliterations of spec/lean/Oak/BorrowStateRefinement.lean, which proves
// them sound and complete against the abstract ownership transitions of
// Oak.Borrowing (view admission ↔ acquireRead, span-core admission ↔
// acquireWrite, recompute ↔ release targets).

// admitViewBorrow: a read-only view is admitted unless a writer holds the
// owner (Oak.BorrowStateRefinement.admitView).
func admitViewBorrow(state BorrowState) bool {
	return state != UniqueWrite
}

// admitSpanBorrowCore: the single-writer core admits a writable span only
// from the free state (Oak.BorrowStateRefinement.admitSpanCore). The
// disjoint multi-span and unsafe-admission extensions layer on top and are
// refined separately (Oak.ReborrowRefinement, Oak.Unsafe).
func admitSpanBorrowCore(state BorrowState) bool {
	return state == Free
}

// ownerStateFor recomputes an owner's state from its remaining live borrows
// (Oak.BorrowStateRefinement.ownerStateFor). Both kinds live at once is the
// flagged impossible case.
func ownerStateFor(hasViews, hasSpans bool) (BorrowState, bool) {
	switch {
	case hasViews && hasSpans:
		return Free, false
	case hasSpans:
		return UniqueWrite, true
	case hasViews:
		return SharedRead, true
	default:
		return Free, true
	}
}

// createViewBorrow creates a read-only borrow (view) from an owner
func (bc *BorrowChecker) createViewBorrow(ownerName, borrowName string) {
	bc.createViewBorrowWithRegion(ownerName, borrowName, nil, nil)
}

// createViewBorrowWithRegion creates a read-only borrow (view) from an owner with region information.
func (bc *BorrowChecker) createViewBorrowWithRegion(ownerName, borrowName string, region *Region, origin ast.Node) {
	if bc.consumedOwners[ownerName] {
		bc.reportBorrow(origin, CodeResourceUsedAfterConsume,
			fmt.Sprintf("buffer %q cannot be borrowed after c.disown handed its memory back", ownerName))
		return
	}
	state := bc.ownerStates[ownerName]
	if !admitViewBorrow(state) {
		d := bc.reportBorrow(origin, CodeViewConflictsWithSpan,
			fmt.Sprintf("view %q cannot be created while %q has writable access", borrowName, ownerName))
		if existingName, info, ok := bc.firstActiveBorrow(ownerName, BorrowSpan); ok {
			bc.addBorrowContext(d, existingName, info,
				fmt.Sprintf("writable span %q already has exclusive access", existingName))
		}
		d.AddHelp("end the writable span before creating a read-only view")
		return
	}

	// Transition to SharedRead if not already.
	bc.ownerStates[ownerName] = SharedRead
	bc.ownerOf[borrowName] = ownerName

	// Track this borrow with metadata.
	bc.activeBorrows[borrowName] = borrowInfo{
		owner:      ownerName,
		kind:       BorrowView,
		blockDepth: bc.currentBlockDepth,
		region:     region,
		origin:     origin,
	}
}

// createSpanBorrow creates a unique writable borrow (span) from an owner
func (bc *BorrowChecker) createSpanBorrow(ownerName, borrowName string) {
	bc.createSpanBorrowWithRegion(ownerName, borrowName, nil, nil)
}

// createSpanBorrowWithRegion creates a unique writable borrow (span) from an owner with region information.
// Multiple spans are allowed only when every active writable region is provably disjoint.
func (bc *BorrowChecker) createSpanBorrowWithRegion(ownerName, borrowName string, region *Region, origin ast.Node) {
	if bc.consumedOwners[ownerName] {
		bc.reportBorrow(origin, CodeResourceUsedAfterConsume,
			fmt.Sprintf("buffer %q cannot be borrowed after c.disown handed its memory back", ownerName))
		return
	}
	state := bc.ownerStates[ownerName]
	spanNames := bc.activeBorrowNames(ownerName, BorrowSpan)

	if len(spanNames) > 0 {
		var conflictName string
		var conflict borrowInfo
		allDisjoint := region != nil
		if allDisjoint {
			for _, existingName := range spanNames {
				existing := bc.activeBorrows[existingName]
				if existing.region == nil || regionsOverlap(region, existing.region) {
					allDisjoint = false
					conflictName = existingName
					conflict = existing
					break
				}
			}
		} else {
			conflictName = spanNames[0]
			conflict = bc.activeBorrows[conflictName]
		}

		if allDisjoint || bc.unsafeDepth > 0 {
			if !allDisjoint {
				// Oak.Unsafe: inside an unsafe boundary the unprovable
				// writable-disjointness obligation is admitted, not proven.
				var existingRegion *Region
				if conflict.owner != "" {
					existingRegion = conflict.region
				}
				d := bc.reportUnsafeAssumption(origin,
					fmt.Sprintf("unsafe assumption: writable span %q is assumed disjoint from existing writable access to %q", borrowName, ownerName),
					borrowName, region, conflictName, existingRegion)
				d.AddNote(fmt.Sprintf("requested region: %s", describeRegion(region)))
				if conflictName != "" {
					bc.addBorrowContext(d, conflictName, conflict,
						fmt.Sprintf("existing span %q covers %s", conflictName, describeRegion(conflict.region)))
				}
				d.AddNote("Oak cannot prove the writable regions are disjoint; this unsafe block takes responsibility for that fact")
			}
			bc.ownerOf[borrowName] = ownerName
			bc.activeBorrows[borrowName] = borrowInfo{
				owner:      ownerName,
				kind:       BorrowSpan,
				blockDepth: bc.currentBlockDepth,
				region:     region,
				origin:     origin,
			}
			return
		}

		d := bc.reportBorrow(origin, CodeSpanOverlap,
			fmt.Sprintf("writable span %q may overlap existing writable access to %q", borrowName, ownerName))
		d.AddNote(fmt.Sprintf("requested region: %s", describeRegion(region)))
		if conflictName != "" {
			bc.addBorrowContext(d, conflictName, conflict,
				fmt.Sprintf("existing span %q covers %s", conflictName, describeRegion(conflict.region)))
		}
		if region == nil || (conflictName != "" && conflict.region == nil) {
			d.AddNote("Oak could not prove the writable regions are disjoint, so it rejects the alias conservatively")
		}
		d.AddHelp("split the owner into statically disjoint regions before taking multiple writable spans")
		return
	}

	if state == SharedRead {
		d := bc.reportBorrow(origin, CodeSpanConflictsWithView,
			fmt.Sprintf("writable span %q cannot be created while %q has read-only views", borrowName, ownerName))
		if existingName, info, ok := bc.firstActiveBorrow(ownerName, BorrowView); ok {
			bc.addBorrowContext(d, existingName, info,
				fmt.Sprintf("read-only view %q is still active", existingName))
		}
		d.AddHelp("finish using the views before requesting writable access")
		return
	}

	if admitSpanBorrowCore(state) {
		bc.ownerStates[ownerName] = UniqueWrite
	}
	bc.ownerOf[borrowName] = ownerName
	bc.activeBorrows[borrowName] = borrowInfo{
		owner:      ownerName,
		kind:       BorrowSpan,
		blockDepth: bc.currentBlockDepth,
		region:     region,
		origin:     origin,
	}
}

// createSubslice creates a conservative derived borrow when exact region facts are unavailable.
func (bc *BorrowChecker) createSubslice(sourceBorrowName, subsliceName string) {
	bc.createSubsliceWithRegion(sourceBorrowName, subsliceName, nil, nil)
}

// createSubsliceWithRegion creates a derived borrow. Writable derivations are
// reborrows: each live child suspends direct use of its parent span, and
// sibling reborrows may coexist only when their regions are statically proven
// pairwise disjoint. Unknown regions fail closed and admit no siblings.
func (bc *BorrowChecker) createSubsliceWithRegion(sourceBorrowName, subsliceName string, newRegion *Region, origin ast.Node) {
	sourceInfo, exists := bc.activeBorrows[sourceBorrowName]
	if !exists {
		bc.addError(fmt.Sprintf("cannot create subslice '%s': source '%s' is not a borrow", subsliceName, sourceBorrowName))
		return
	}
	if origin == nil {
		origin = sourceInfo.origin
	}

	if sourceInfo.kind == BorrowSpan {
		siblingNames := make([]string, 0, len(sourceInfo.reborrows))
		siblingRegions := make([]*Region, 0, len(sourceInfo.reborrows))
		for _, siblingName := range sourceInfo.reborrows {
			sibling, ok := bc.activeBorrows[siblingName]
			if !ok {
				continue
			}
			siblingNames = append(siblingNames, siblingName)
			siblingRegions = append(siblingRegions, sibling.region)
		}
		if conflict, ok := admitReborrow(siblingRegions, newRegion); !ok {
			siblingName := siblingNames[conflict]
			sibling := bc.activeBorrows[siblingName]
			if bc.unsafeDepth > 0 {
				// Oak.Unsafe: the unprovable sibling-disjointness obligation
				// is admitted inside an unsafe boundary, not proven.
				d := bc.reportUnsafeAssumption(origin,
					fmt.Sprintf("unsafe assumption: writable reborrow %q is assumed disjoint from live reborrow %q of span %q", subsliceName, siblingName, sourceBorrowName),
					subsliceName, newRegion, siblingName, sibling.region)
				d.AddNote(fmt.Sprintf("requested region: %s", describeRegion(newRegion)))
				bc.addBorrowContext(d, siblingName, sibling,
					fmt.Sprintf("reborrow %q is still live here", siblingName))
				d.AddNote("Oak cannot prove the reborrowed regions are disjoint; this unsafe block takes responsibility for that fact")
			} else {
				d := bc.reportBorrow(origin, CodeReborrowOverlap,
					fmt.Sprintf("writable reborrow %q may overlap live reborrow %q of span %q", subsliceName, siblingName, sourceBorrowName))
				d.AddNote(fmt.Sprintf("requested region: %s", describeRegion(newRegion)))
				bc.addBorrowContext(d, siblingName, sibling,
					fmt.Sprintf("reborrow %q is still live here", siblingName))
				if newRegion == nil || sibling.region == nil {
					d.AddNote("Oak could not prove the reborrowed regions are disjoint, so it rejects the alias conservatively")
				}
				d.AddHelp("reborrow statically disjoint regions, or let the live child span leave scope first")
				return
			}
		}
		sourceInfo.reborrows = append(sourceInfo.reborrows, subsliceName)
		bc.activeBorrows[sourceBorrowName] = sourceInfo
	}
	bc.ownerOf[subsliceName] = sourceInfo.owner
	bc.activeBorrows[subsliceName] = borrowInfo{
		owner:      sourceInfo.owner,
		kind:       sourceInfo.kind,
		blockDepth: bc.currentBlockDepth,
		region:     newRegion,
		origin:     origin,
		parent:     sourceBorrowName,
	}
}

// foreignDisownOperand recognizes `c.disown(b)` and names the buffer
// binding (docs/spec/92-ffi.md section 2.8). A local named `c` would have
// made this an ordinary call, which the typechecker never accepts here.
// custodyTransitionOperand recognizes a call to an extern binding that
// returns a Buffer and names the Buffer binding it moves.
func custodyTransitionOperand(call *ast.InvocationExpression, env *typechecker.TypeEnvironment) (string, bool) {
	callee, isIdent := call.Function.(*ast.Identifier)
	if !isIdent || env == nil {
		return "", false
	}
	scheme, bound := env.Get(callee.Value)
	if !bound || scheme == nil {
		return "", false
	}
	fn, isFn := scheme.Type.(*typechecker.FunctionType)
	if !isFn {
		return "", false
	}
	if _, returnsBuffer := fn.ReturnType.(*typechecker.BufferType); !returnsBuffer {
		return "", false
	}
	for i, arg := range call.Arguments {
		ident, isIdent := arg.(*ast.Identifier)
		if !isIdent {
			continue
		}
		if i < len(fn.Parameters) {
			if _, isBuffer := fn.Parameters[i].(*typechecker.BufferType); isBuffer {
				return ident.Value, true
			}
		}
	}
	return "", false
}

func foreignDisownOperand(call *ast.InvocationExpression) (string, bool) {
	access, isAccess := call.Function.(*ast.IndexExpression)
	if !isAccess || len(call.Arguments) != 1 {
		return "", false
	}
	base, isIdent := access.Left.(*ast.Identifier)
	member, memberIsIdent := access.Index.(*ast.Identifier)
	if !isIdent || !memberIsIdent || base.Value != "c" || member.Value != "disown" {
		return "", false
	}
	owner, isOwner := call.Arguments[0].(*ast.Identifier)
	if !isOwner {
		return "", false
	}
	return owner.Value, true
}
