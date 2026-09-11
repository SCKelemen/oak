package borrowchecker

import (
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// Global writes are visible at call sites, where a local view may be live even
// though no borrow was live when the callee definition was checked. Unknown
// callees conservatively may write every global owner.
func (bc *BorrowChecker) collectGlobalWrites(program *ast.Program, env *typechecker.TypeEnvironment) {
	bc.globalWrites = make(map[string]map[string]bool)
	bc.globalOwners = make(map[string]bool)
	functions := make(map[string]*ast.FunctionStatement)
	calls := make(map[string]map[string]bool)
	for _, statement := range program.Statements {
		switch node := statement.(type) {
		case *ast.VariableDeclaration:
			if array, ok := env.CheckedDeclarationType(node).(*typechecker.ArrayType); ok && !array.IsSlice && !array.IsSpan {
				bc.globalOwners[node.Name.Value] = true
			}
		case *ast.FunctionStatement:
			functions[node.Name.Value] = node
		}
	}
	for name, fn := range functions {
		writes := make(map[string]bool)
		callees := make(map[string]bool)
		bc.globalWrites[name] = writes
		calls[name] = callees
		var walk func(ast.Node)
		mark := func(expr ast.Expression) {
			for {
				switch value := expr.(type) {
				case *ast.Identifier:
					if bc.globalOwners[value.Value] {
						writes[value.Value] = true
					}
					return
				case *ast.IndexExpression:
					expr = value.Left
				case *ast.PrefixExpression:
					expr = value.Right
				default:
					return
				}
			}
		}
		walk = func(node ast.Node) {
			switch value := node.(type) {
			case *ast.BlockExpression:
				if value.Block != nil {
					walk(value.Block)
				}
			case *ast.BlockStatement:
				if value == nil {
					return
				}
				for _, stmt := range value.Statements {
					walk(stmt)
				}
			case *ast.ExpressionStatement:
				walk(value.Expression)
			case *ast.VariableDeclaration:
				walk(value.Value)
			case *ast.AssignmentStatement:
				mark(value.Name)
				walk(value.Value)
			case *ast.IndexAssignmentStatement:
				mark(value.Target.Left)
				walk(value.Target)
				walk(value.Value)
			case *ast.InvocationExpression:
				if id, ok := value.Function.(*ast.Identifier); ok {
					callees[id.Value] = true
					if id.Value == "span" && len(value.Arguments) == 1 {
						mark(value.Arguments[0])
					}
				} else if env.CheckedSIMDOperation(value) == "" {
					callees["$indirect"] = true
				}
				for _, arg := range value.Arguments {
					walk(arg)
				}
			case *ast.IndexExpression:
				walk(value.Left)
				walk(value.Index)
			case *ast.SliceExpression:
				walk(value.Seq)
				walk(value.Low)
				walk(value.High)
			case *ast.PrefixExpression:
				walk(value.Right)
			case *ast.InfixExpression:
				walk(value.Left)
				walk(value.Right)
			case *ast.RecordLiteral:
				for _, field := range value.Fields {
					walk(field)
				}
			case *ast.ArrayLiteral:
				for _, element := range value.Elements {
					walk(element)
				}
			case *ast.VariantExpression:
				walk(value.Payload)
			case *ast.MatchExpression:
				walk(value.Scrutinee)
				for _, arm := range value.Arms {
					walk(arm.Body)
				}
			case *ast.WhileStatement:
				walk(value.Condition)
				walk(value.Body)
			case *ast.IfStatement:
				walk(value.Condition)
				walk(value.Consequence)
				if value.Alternative != nil {
					walk(value.Alternative)
				}
			case *ast.UnsafeBlock:
				walk(value.Body)
			case *ast.FunctionStatement:
				walk(value.Body)
			case *ast.FunctionLiteral:
				walk(value.Body)
			}
		}
		walk(fn.Body)
		if fn.ExternSymbol != "" {
			callees["$external"] = true
		}
	}
	changed := true
	for changed {
		changed = false
		for name, callees := range calls {
			for callee := range callees {
				effects, known := bc.globalWrites[callee]
				if !known {
					if pureBorrowBuiltin(callee) {
						continue
					}
					effects = bc.globalOwners
				}
				for owner := range effects {
					if !bc.globalWrites[name][owner] {
						bc.globalWrites[name][owner] = true
						changed = true
					}
				}
			}
		}
	}
}

func pureBorrowBuiltin(name string) bool {
	parts := strings.Split(name, "_")
	if len(parts) == 3 && scalarIntegerName(parts[0]) && scalarIntegerName(parts[2]) {
		switch parts[1] {
		case "trunc", "checked", "saturating", "bits", "round":
			return true
		}
	}
	// Floating-point intrinsics are pure (docs/spec/20-types.md section
	// 11.3.5); a program function of the same name has its own entry in
	// globalWrites and is consulted first.
	if typechecker.FloatIntrinsicName(name) {
		return true
	}
	switch name {
	case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64",
		"int", "uint", "uptr", "iptr", "f32", "f64", "byte", "rune",
		"len", "assert", "is_valid_utf8", "str_from_utf8", "str_bytes",
		"view", "span", "subslice", "view_as", "span_as",
		"address_of", "size_of", "align_of", "offset_of", "static_assert":
		return true
	}
	return false
}

func scalarIntegerName(name string) bool {
	switch name {
	case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "f32", "f64":
		return true
	}
	return false
}

func (bc *BorrowChecker) checkCallGlobalWrites(call *ast.InvocationExpression, env *typechecker.TypeEnvironment) {
	if env.CheckedSIMDOperation(call) != "" {
		return
	}
	effects := bc.globalOwners
	if name, ok := call.Function.(*ast.Identifier); ok {
		if known, exists := bc.globalWrites[name.Value]; exists {
			effects = known
		} else if pureBorrowBuiltin(name.Value) {
			return
		}
	}
	names := make([]string, 0, len(effects))
	for owner := range effects {
		names = append(names, owner)
	}
	sort.Strings(names)
	for _, owner := range names {
		bc.checkIdentifierUse(call, owner, env, true)
	}
}
