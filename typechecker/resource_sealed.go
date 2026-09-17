package typechecker

import (
	"fmt"
	"reflect"
	"sort"

	"github.com/SCKelemen/oak/ast"
)

// sealedValueTypes finds sealed values, including zero-initialized aggregate
// members. Borrowed spans/slices and pointer referents are not constructed by
// initializing their container. Unlike resource path enumeration this check
// has no depth cutoff and includes owned fixed arrays.
func (a *typedResourceAnalysis) sealedValueTypes(typ Type) map[string]string {
	found := make(map[string]string)
	records := make(map[*RecordType]bool)
	arrays := make(map[*ArrayType]bool)
	adts := make(map[string]bool)
	sums := make(map[Type]bool)
	var visit func(Type)
	visit = func(t Type) {
		if t == nil {
			return
		}
		if template, state, ok := a.typestateOf(t); ok && a.model.SealedInitialConstructors[template] != "" {
			found[template] = state
			return
		}
		switch v := t.(type) {
		case *RecordType:
			if v == nil || records[v] {
				return
			}
			records[v] = true
			for _, name := range v.orderedFieldNames() {
				visit(v.Fields[name])
			}
			return
		case *ArrayType:
			if v == nil || v.IsSpan || v.IsSlice || v.Length == 0 || arrays[v] {
				return
			}
			arrays[v] = true
			visit(v.ElementType)
			return
		case *UnionType:
			if v != nil && !sums[v] {
				sums[v] = true
				for _, member := range v.Types {
					visit(member)
				}
			}
			return
		case *IntersectionType:
			if v != nil && !sums[v] {
				sums[v] = true
				for _, member := range v.Types {
					visit(member)
				}
			}
			return
		}
		name, _, args, isADT := adtInstantiation(t)
		if !isADT || a.tc.adtTypes[name] == nil || adts[t.String()] {
			return
		}
		adts[t.String()] = true
		def := a.tc.adtTypes[name]
		bindings := make(map[string]Type, len(args))
		for i, parameter := range def.TypeParams {
			if i < len(args) {
				bindings[parameter] = args[i]
			}
		}
		for _, variant := range def.Variants {
			visit(a.tc.instantiatedVariantPayload(name, variant, bindings))
		}
	}
	visit(typ)
	return found
}

func (a *typedResourceAnalysis) sealedLiteralAllowed(fn *ast.FunctionStatement, template, state string, tail bool) bool {
	if fn == nil {
		return false
	}
	identity := functionIdentity(fn)
	op, known := a.contractOperation(identity)
	if !known || op.Trusted {
		return false
	}
	if identity == a.model.SealedInitialConstructors[template] {
		return op.ReturnsFresh && state == a.model.Initials[template]
	}
	if !tail {
		// A transition may rebuild its result, not mint an independently
		// bound local handle that flow would register as fresh authority.
		return false
	}
	// A transition reconstructs the same consumed resource at its target;
	// another protocol's same-spelled state grants no construction right.
	if !op.ReturnsAlias || op.AliasesArgument < 0 || op.AliasesArgument >= len(fn.Parameters) ||
		op.parameterMode(op.AliasesArgument) != ResourceParameterConsumed {
		return false
	}
	parameter := fn.Parameters[op.AliasesArgument]
	if parameter == nil {
		return false
	}
	source, _, ok := a.typestateOf(a.tc.parseTypeExpression(parameter.Type))
	if !ok || source != template {
		return false
	}
	for _, target := range op.Targets {
		if target == state {
			return true
		}
	}
	return false
}

// checkSealedResourceConstruction is a pre-flow construction gate, not a
// memory-ownership proof. Check all value syntax, including globals; a nested
// closure never inherits its enclosing constructor's permission. Type-shape
// declarations are not value constructions.
func (tc *TypeChecker) checkSealedResourceConstruction(program *ast.Program, model ResourceModel) {
	if len(model.SealedInitialConstructors) == 0 {
		return
	}
	a := &typedResourceAnalysis{tc: tc, model: model}
	reportZero := func(node ast.Node, typ Type) {
		templates := a.sealedValueTypes(typ)
		names := make([]string, 0, len(templates))
		for name := range templates {
			names = append(names, name)
		}
		sort.Strings(names)
		for _, name := range names {
			tc.addResourceDiagnosticWithCode(node, CodeResourceTypestateConstruction,
				fmt.Sprintf("a sealed %s handle cannot be zero-initialized; use %s and the protocol's transitions", name, model.SealedInitialConstructors[name]))
		}
	}
	topFunctions := make(map[*ast.FunctionStatement]bool)
	definitions := make(map[string][]*ast.FunctionStatement)
	for _, stmt := range program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok {
			topFunctions[fn] = true
			identity := functionIdentity(fn)
			definitions[identity] = append(definitions[identity], fn)
		}
	}
	constructors := make(map[string]bool)
	for _, constructor := range model.SealedInitialConstructors {
		constructors[constructor] = true
	}
	constructorNames := make([]string, 0, len(constructors))
	for constructor := range constructors {
		constructorNames = append(constructorNames, constructor)
	}
	sort.Strings(constructorNames)
	for _, constructor := range constructorNames {
		matches := definitions[constructor]
		if len(matches) != 1 || matches[0].Body == nil || matches[0].ExternSymbol != "" || matches[0].AsmBacked {
			tc.addResourceDiagnosticWithCode(program, CodeResourceTypestateConstruction,
				fmt.Sprintf("sealed initial constructor %q requires one checked Oak body, not an absent, foreign, or assembly-backed definition", constructor))
		}
	}
	// Shared syntax must be checked in each callable context; deduplicating
	// solely by node could lend a constructor's permission to another body.
	type visitKey struct {
		node ast.Node
		fn   *ast.FunctionStatement
		tail bool
	}
	seen := make(map[visitKey]bool)
	var visit func(reflect.Value, *ast.FunctionStatement, bool)
	visit = func(value reflect.Value, fn *ast.FunctionStatement, tail bool) {
		if !value.IsValid() {
			return
		}
		switch value.Kind() {
		case reflect.Interface:
			if !value.IsNil() {
				visit(value.Elem(), fn, tail)
			}
		case reflect.Ptr:
			if value.IsNil() {
				return
			}
			if node, ok := value.Interface().(ast.Node); ok {
				key := visitKey{node, fn, tail}
				if seen[key] {
					return
				}
				seen[key] = true
				switch n := node.(type) {
				case *ast.ADTType:
					return
				case *ast.FunctionStatement:
					fn = nil
					if topFunctions[n] {
						fn = n
					}
				case *ast.FunctionLiteral:
					fn = nil
				case *ast.RecordLiteral:
					typ := tc.env.CheckedExpressionType(n)
					if template, state, ok := a.typestateOf(typ); ok && model.SealedInitialConstructors[template] != "" && !a.sealedLiteralAllowed(fn, template, state, tail) {
						tc.addResourceDiagnosticWithCode(n, CodeResourceTypestateConstruction,
							fmt.Sprintf("a sealed %s[%s] cannot be constructed here; use %s or a checked same-resource transition", template, state, model.SealedInitialConstructors[template]))
					}
					if record, ok := typ.(*RecordType); ok {
						for _, name := range record.orderedFieldNames() {
							if n.Fields[name] == nil {
								reportZero(n, record.Fields[name])
							}
						}
					}
				case *ast.VariableDeclaration:
					if n.Value == nil {
						typ := tc.env.CheckedDeclarationType(n)
						if typ == nil && n.Type != nil {
							typ = tc.parseTypeExpression(n.Type)
						}
						reportZero(n, typ)
					}
				case *ast.ArrayLiteral:
					if array, ok := tc.env.CheckedExpressionType(n).(*ArrayType); ok && !array.IsSpan && !array.IsSlice && int64(len(n.Elements)) < array.Length {
						reportZero(n, array.ElementType)
					}
				}
			}
			visit(value.Elem(), fn, tail)
		case reflect.Struct:
			// Tokens and semantic contexts are not syntax and may have back
			// references. Walk only structures owned by the AST package.
			if value.Type().PkgPath() != reflect.TypeOf(ast.Program{}).PkgPath() {
				return
			}
			if block, ok := value.Interface().(ast.BlockStatement); ok {
				for i, stmt := range block.Statements {
					visit(reflect.ValueOf(stmt), fn, tail && i == len(block.Statements)-1)
				}
				return
			}
			for i := 0; i < value.NumField(); i++ {
				if value.Type().Field(i).IsExported() {
					field := value.Type().Field(i).Name
					childTail := false
					switch value.Interface().(type) {
					case ast.FunctionStatement:
						childTail = field == "Body"
					case ast.BlockExpression:
						childTail = tail && field == "Block"
					case ast.ExpressionStatement:
						childTail = tail && field == "Expression"
					case ast.MatchExpression:
						childTail = tail && field == "Arms"
					case ast.MatchArm:
						childTail = tail && field == "Body"
					case ast.VariantExpression:
						childTail = tail && field == "Payload"
					}
					visit(value.Field(i), fn, childTail)
				}
			}
		case reflect.Slice:
			for i := 0; i < value.Len(); i++ {
				visit(value.Index(i), fn, tail)
			}
		case reflect.Map:
			if value.Type().Key().Kind() == reflect.String {
				keys := value.MapKeys()
				sort.Slice(keys, func(i, j int) bool { return keys[i].String() < keys[j].String() })
				for _, key := range keys {
					visit(value.MapIndex(key), fn, tail)
				}
			}
		}
	}
	visit(reflect.ValueOf(program), nil, false)
}
