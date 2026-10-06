package borrowchecker

// Multiple-region records keep one provenance contract per borrowed field.
// This increment admits read-only record fields and one source path per region.
// Regions are compile-time metadata; the existing borrow state still enforces
// owner lifetime and exclusivity after a call.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

type regionSourcePath struct {
	parameter int
	path      string
}

func sourcePathFor(sig typechecker.RegionSignature, region string) (regionSourcePath, bool) {
	found := regionSourcePath{parameter: -1}
	for i, paths := range sig.ParamPaths {
		for path, r := range paths {
			if r != region {
				continue
			}
			if found.parameter >= 0 {
				return regionSourcePath{}, false
			}
			found = regionSourcePath{i, path}
		}
	}
	return found, found.parameter >= 0
}

func sortedRegionPaths(paths map[string]string) []string {
	keys := make([]string, 0, len(paths))
	for path := range paths {
		keys = append(keys, path)
	}
	sort.Strings(keys)
	return keys
}

func (bc *BorrowChecker) multipleRegionContract(stmt *ast.FunctionStatement, fn *typechecker.FunctionType, sig typechecker.RegionSignature, env *typechecker.TypeEnvironment) *regionContract {
	contract := &regionContract{function: stmt.Name.Value, fieldOwners: map[string]string{}}
	fail := func(note string) *regionContract {
		d := bc.reportBorrow(stmt.Name, CodeReturnedBorrowRegion, fmt.Sprintf("function %q has an unsupported multiple-region contract", stmt.Name.Value))
		d.AddNote(note)
		contract.checked = true
		return contract
	}
	validate := func(typ typechecker.Type, paths map[string]string) bool {
		fields, complete := borrowFieldsOf(typ, env)
		if !complete || len(fields) != len(paths) {
			return false
		}
		for _, field := range fields {
			if field.kind != BorrowView || paths[field.path] == "" {
				return false
			}
		}
		return true
	}
	for i, typ := range fn.Parameters {
		if i >= len(sig.ParamPaths) || !validate(typ, sig.ParamPaths[i]) {
			return fail("each borrowed parameter field must be a read-only view with an explicit region; mutable fields and unsupported aggregate shapes are not admitted")
		}
	}
	if !validate(fn.ReturnType, sig.ReturnPaths) {
		return fail("each borrowed result field must be a read-only view with an explicit region; mutable fields and unsupported aggregate shapes are not admitted")
	}
	for _, path := range sortedRegionPaths(sig.ReturnPaths) {
		source, ok := sourcePathFor(sig, sig.ReturnPaths[path])
		if !ok || source.parameter >= len(stmt.Parameters) || stmt.Parameters[source.parameter].Name == nil {
			return fail(fmt.Sprintf("result path %q must name exactly one parameter borrow path through its region %s", path, sig.ReturnPaths[path]))
		}
		contract.fieldOwners[path] = withPrefix(parameterOwnerPrefix+stmt.Parameters[source.parameter].Name.Value, source.path)
	}
	return contract
}

func projectRegionPath(expr ast.Expression, path string) ast.Expression {
	if path == "" {
		return expr
	}
	for _, field := range strings.Split(path, ".") {
		expr = &ast.IndexExpression{Left: expr, Index: &ast.Identifier{Value: field}, Dot: true}
	}
	return expr
}

// regionFieldArgument selects the exact argument path corresponding to a
// returned field. Never substitute the whole argument for an unknown path.
func regionFieldArgument(call *ast.InvocationExpression, path string, env *typechecker.TypeEnvironment) (ast.Expression, bool) {
	id, ok := call.Function.(*ast.Identifier)
	if !ok {
		return nil, false
	}
	_, sig, ok := regionSignatureFor(id.Value, env)
	if !ok || !sig.FieldSensitive {
		return nil, false
	}
	region := sig.ReturnPaths[path]
	if region == "" {
		return nil, false
	}
	source, ok := sourcePathFor(sig, region)
	if !ok || source.parameter >= len(call.Arguments) {
		return nil, false
	}
	return projectRegionPath(call.Arguments[source.parameter], source.path), true
}

// fieldProvenance traces a selected field, including after a nested block's
// lexical borrows have ended. The recursion bound makes cyclic initializers
// fail closed. Unlike whole-value provenance, it never unions sibling fields.
func (bc *BorrowChecker) fieldProvenance(expr ast.Expression, path string, env *typechecker.TypeEnvironment, depth int) (map[string]bool, bool) {
	if expr == nil || depth > 64 {
		return nil, false
	}
	recur := func(e ast.Expression, p string) (map[string]bool, bool) {
		return bc.fieldProvenance(e, p, env, depth+1)
	}
	if name, ok := fieldPath(expr); ok {
		if info, tracked := bc.activeBorrows[withPrefix(name, path)]; tracked {
			return map[string]bool{info.owner: true}, true
		}
	}
	switch e := expr.(type) {
	case *ast.Identifier:
		if value := bc.initializers[e.Value]; value != nil {
			return recur(value, path)
		}
	case *ast.IndexExpression:
		if e.Dot {
			if field, ok := e.Index.(*ast.Identifier); ok {
				return recur(e.Left, withPrefix(field.Value, path))
			}
		}
	case *ast.RecordLiteral:
		field, rest, _ := strings.Cut(path, ".")
		if path != "" {
			return recur(e.Fields[field], rest)
		}
	case *ast.BlockExpression:
		return recur(e.Result(), path)
	case *ast.MatchExpression:
		owners := map[string]bool{}
		if len(e.Arms) == 0 {
			return nil, false
		}
		for _, arm := range e.Arms {
			sub, ok := recur(arm.Body, path)
			if !ok {
				return nil, false
			}
			for owner := range sub {
				owners[owner] = true
			}
		}
		return owners, true
	case *ast.InvocationExpression:
		if arg, ok := regionFieldArgument(e, path, env); ok {
			return recur(arg, "")
		}
		if id, ok := e.Function.(*ast.Identifier); ok {
			if _, sig, has := regionSignatureFor(id.Value, env); has && sig.FieldSensitive {
				return nil, false
			}
		}
	}
	if path == "" {
		return bc.provenanceOwners(expr, env)
	}
	return nil, false
}

// fieldSources is the live caller-side counterpart of fieldProvenance.
func (bc *BorrowChecker) fieldSources(expr ast.Expression, path string, env *typechecker.TypeEnvironment, depth int) ([]borrowSource, bool) {
	if expr == nil || depth > 64 {
		return nil, false
	}
	recur := func(e ast.Expression, p string) ([]borrowSource, bool) { return bc.fieldSources(e, p, env, depth+1) }
	if name, ok := fieldPath(expr); ok {
		name = withPrefix(name, path)
		if info, tracked := bc.activeBorrows[name]; tracked {
			return []borrowSource{{name: name, kind: info.kind}}, true
		}
	}
	switch e := expr.(type) {
	case *ast.IndexExpression:
		if e.Dot {
			if field, ok := e.Index.(*ast.Identifier); ok {
				return recur(e.Left, withPrefix(field.Value, path))
			}
		}
	case *ast.RecordLiteral:
		field, rest, _ := strings.Cut(path, ".")
		if path != "" {
			return recur(e.Fields[field], rest)
		}
	case *ast.InvocationExpression:
		if arg, ok := regionFieldArgument(e, path, env); ok {
			return recur(arg, "")
		}
		if id, ok := e.Function.(*ast.Identifier); ok {
			if _, sig, has := regionSignatureFor(id.Value, env); has && sig.FieldSensitive {
				return nil, false
			}
		}
	}
	if path == "" {
		return bc.sourceBorrows(expr, env)
	}
	return nil, false
}

func (bc *BorrowChecker) bindMultipleRegionCall(call *ast.InvocationExpression, target string, sig typechecker.RegionSignature, env *typechecker.TypeEnvironment) bool {
	// Resolve every field before changing borrow state.
	type binding struct {
		path   string
		source borrowSource
	}
	var bindings []binding
	for _, path := range sortedRegionPaths(sig.ReturnPaths) {
		sources, ok := bc.fieldSources(call, path, env, 0)
		if !ok || len(sources) != 1 || sources[0].kind != BorrowView {
			bc.reportBorrow(call, CodeReturnedBorrowRegion, fmt.Sprintf("cannot trace read-only result path %q of the multiple-region call", path))
			return true
		}
		bindings = append(bindings, binding{path, sources[0]})
	}
	for _, b := range bindings {
		name := withPrefix(target, b.path)
		if b.source.isOwner {
			bc.createViewBorrowWithRegion(b.source.name, name, bc.wholeOwnerRegion(b.source.name, env), call)
		} else {
			bc.createSubsliceWithRegion(b.source.name, name, nil, call)
		}
	}
	return true
}

// multipleRegionExpression identifies expressions that need field-sensitive
// binding, including projections wrapped in slicing or derivation builtins.
func (bc *BorrowChecker) multipleRegionExpression(expr ast.Expression, env *typechecker.TypeEnvironment) bool {
	if typ, ok := env.CheckedExpressionType(expr).(*typechecker.RecordType); ok {
		if rec, ok := env.RegionRecord(typ.Name); ok && rec.FieldSensitive {
			return true
		}
	}
	switch e := expr.(type) {
	case *ast.IndexExpression:
		return bc.multipleRegionExpression(e.Left, env)
	case *ast.SliceExpression:
		return bc.multipleRegionExpression(e.Seq, env)
	case *ast.InvocationExpression:
		if id, ok := e.Function.(*ast.Identifier); ok {
			if _, sig, has := regionSignatureFor(id.Value, env); has && sig.FieldSensitive {
				return true
			}
		}
		for _, arg := range e.Arguments {
			if bc.multipleRegionExpression(arg, env) {
				return true
			}
		}
	case *ast.BlockExpression:
		return bc.multipleRegionExpression(e.Result(), env)
	case *ast.MatchExpression:
		for _, arm := range e.Arms {
			if bc.multipleRegionExpression(arm.Body, env) {
				return true
			}
		}
	}
	return false
}

func (bc *BorrowChecker) bindMultipleRegionProjection(expr ast.Expression, target string, env *typechecker.TypeEnvironment) {
	sources, ok := bc.fieldSources(expr, "", env, 0)
	if !ok || len(sources) != 1 || sources[0].kind != BorrowView {
		bc.reportBorrow(expr, CodeReturnedBorrowRegion, "cannot trace a read-only borrow derived from a multiple-region record")
		return
	}
	source := sources[0]
	if source.isOwner {
		bc.createViewBorrowWithRegion(source.name, target, bc.wholeOwnerRegion(source.name, env), expr)
	} else {
		bc.createSubsliceWithRegion(source.name, target, nil, expr)
	}
}
