package borrowchecker

// Region-indexed borrowed returns (docs/spec/50-borrowing.md section 8c).
// A function may return a view, a span, or a record carrying them when its
// signature names the parameter region the result borrows from: elided —
// a `[]T` return with exactly one `[]T` parameter of that element type, or
// `[*]T` with one `[*]T` — or explicit through region parameters
// (`frame[R]: (buf: View[u8, R]): View[u8, R]`, `Cursor[R]`), erased by the
// type checker into the side table read here. The parameter's owner
// outlives the call (`Oak.Escape.return_param_borrow_wf`), so the callee's
// obligation is provenance: the result must borrow that parameter and
// nothing else, or OAK-B0113 names what it borrows instead. At the caller
// the result is a reborrow of the argument (`Oak.Escape.reborrow_wf`):
// same owners, same kinds, bound at the caller's block depth, so every
// exclusivity and scope rule applies to it as to a borrow taken directly.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

const parameterOwnerPrefix = "$parameter:"

// elidedRegion is the name of the region an elided signature implies.
const elidedRegion = "$elided"

// regionCandidate is the elision rule: a `[]T` return with exactly one
// `[]T` parameter of the same element type, or `[*]T` with exactly one
// `[*]T`, names that parameter as the region. Variadic functions have no
// candidate — the bundled trailing view is caller-stack storage that lives
// only for the call.
func regionCandidate(fn *typechecker.FunctionType) (int, bool) {
	if fn == nil || fn.Variadic {
		return -1, false
	}
	ret, isArray := fn.ReturnType.(*typechecker.ArrayType)
	if !isArray || (!ret.IsSlice && !ret.IsSpan) || ret.ElementType == nil {
		return -1, false
	}
	candidate := -1
	for i, param := range fn.Parameters {
		p, ok := param.(*typechecker.ArrayType)
		if !ok || p.IsSlice != ret.IsSlice || p.IsSpan != ret.IsSpan || p.ElementType == nil || !p.ElementType.Equals(ret.ElementType) {
			continue
		}
		if candidate >= 0 {
			return -1, false
		}
		candidate = i
	}
	return candidate, candidate >= 0
}

// functionType looks up a declared function's checked type.
func functionType(name string, env *typechecker.TypeEnvironment) *typechecker.FunctionType {
	scheme, ok := env.Get(name)
	if !ok || scheme == nil {
		return nil
	}
	fn, isFn := scheme.Type.(*typechecker.FunctionType)
	if !isFn {
		return nil
	}
	return fn
}

// regionSignatureFor is a function's effective region signature: the
// declared one when it has region parameters, else the elided one.
func regionSignatureFor(name string, env *typechecker.TypeEnvironment) (*typechecker.FunctionType, typechecker.RegionSignature, bool) {
	fn := functionType(name, env)
	if fn == nil {
		return nil, typechecker.RegionSignature{}, false
	}
	if sig, declared := env.RegionSignature(name); declared {
		return fn, sig, true
	}
	idx, ok := regionCandidate(fn)
	if !ok {
		return fn, typechecker.RegionSignature{}, false
	}
	sig := typechecker.RegionSignature{Regions: []string{elidedRegion}, Params: make([]string, len(fn.Parameters)), Return: elidedRegion}
	sig.Params[idx] = elidedRegion
	return fn, sig, true
}

// borrowField is one borrow-carrying field of a record type, flattened to
// a dotted path.
type borrowField struct {
	path string
	kind borrowKind
}

// recordBorrowFields lists a record type's view and span fields in
// declaration order, nested records flattened.
func recordBorrowFields(rt *typechecker.RecordType, prefix string) []borrowField {
	var fields []borrowField
	names := rt.Order
	if len(names) == 0 {
		for name := range rt.Fields {
			names = append(names, name)
		}
		sort.Strings(names)
	}
	for _, name := range names {
		switch ft := rt.Fields[name].(type) {
		case *typechecker.ArrayType:
			if ft.IsSpan {
				fields = append(fields, borrowField{path: prefix + name, kind: BorrowSpan})
			} else if ft.IsSlice {
				fields = append(fields, borrowField{path: prefix + name, kind: BorrowView})
			}
		case *typechecker.RecordType:
			fields = append(fields, recordBorrowFields(ft, prefix+name+".")...)
		}
	}
	return fields
}

// returnKind classifies a region-indexed return type.
type returnKind int

const (
	returnsView returnKind = iota
	returnsSpan
	returnsRecord
)

// regionContract is what a function's body owes its signature: the owners
// of the return region, and the shape of the returned value.
type regionContract struct {
	function string
	region   string
	kind     returnKind
	owners   map[string]bool
	checked  bool
}

// paramRegions reports the region each parameter of a declared function
// carries (empty when the function has no region structure).
func paramRegions(stmt *ast.FunctionStatement, env *typechecker.TypeEnvironment) []string {
	if stmt == nil || stmt.Name == nil {
		return nil
	}
	_, sig, ok := regionSignatureFor(stmt.Name.Value, env)
	if !ok {
		return nil
	}
	return sig.Params
}

// returnContractFor validates a function's region signature and builds
// the contract its body is checked against. nil means the signature has no
// region-indexed return and the conservative escape rule applies. An
// invalid signature is reported here and yields a contract that is
// already discharged, so the escape rule does not report it twice.
func (bc *BorrowChecker) returnContractFor(stmt *ast.FunctionStatement, env *typechecker.TypeEnvironment) *regionContract {
	if stmt == nil || stmt.Name == nil {
		return nil
	}
	fn, sig, ok := regionSignatureFor(stmt.Name.Value, env)
	if !ok || sig.Return == "" {
		return nil
	}
	var origin ast.Node = stmt.ReturnType
	if origin == nil {
		origin = stmt.Name
	}
	contract := &regionContract{function: stmt.Name.Value, region: sig.Return, owners: map[string]bool{}}
	invalid := func(title, note string) *regionContract {
		d := bc.reportBorrow(origin, CodeReturnedBorrowRegion, title)
		d.AddNote(note)
		contract.checked = true
		return contract
	}
	var recordFields []borrowField
	switch ret := fn.ReturnType.(type) {
	case *typechecker.ArrayType:
		switch {
		case ret.IsSpan:
			contract.kind = returnsSpan
		case ret.IsSlice:
			contract.kind = returnsView
		default:
			return nil
		}
	case *typechecker.RecordType:
		if !env.ContainsBorrowStorage(ret) {
			return nil
		}
		rec, declared := env.RegionRecord(ret.Name)
		if !declared || len(rec.Regions) != 1 {
			return invalid(fmt.Sprintf("function %q returns record %q with borrows but no single declared region", stmt.Name.Value, ret.Name),
				"a record that crosses a call carries its borrows in exactly one region parameter (Cursor[R]: type = struct { data: View[u8, R], ... })")
		}
		contract.kind = returnsRecord
		recordFields = recordBorrowFields(ret, "")
	default:
		return nil
	}
	labeled := 0
	for i, region := range sig.Params {
		if region != sig.Return || i >= len(fn.Parameters) || i >= len(stmt.Parameters) || stmt.Parameters[i].Name == nil {
			continue
		}
		labeled++
		name := stmt.Parameters[i].Name.Value
		switch pt := fn.Parameters[i].(type) {
		case *typechecker.ArrayType:
			if contract.kind == returnsView && !pt.IsSlice {
				return invalid(fmt.Sprintf("function %q returns a view from region %s, but parameter %q gives that region a span", stmt.Name.Value, displayRegion(sig.Return), name),
					"a read-only result cannot be derived from a writable span in this increment; return a span, or take a view")
			}
			if contract.kind == returnsSpan && !pt.IsSpan {
				return invalid(fmt.Sprintf("function %q returns a span from region %s, but parameter %q gives that region a read-only view", stmt.Name.Value, displayRegion(sig.Return), name),
					"writable access cannot be derived from a read-only view")
			}
			contract.owners[parameterOwnerPrefix+name] = true
		case *typechecker.RecordType:
			for _, field := range recordBorrowFields(pt, "") {
				contract.owners[parameterOwnerPrefix+name+"."+field.path] = true
			}
		}
	}
	if labeled == 0 {
		return invalid(fmt.Sprintf("function %q returns a borrow in region %s, which names no parameter", stmt.Name.Value, displayRegion(sig.Return)),
			"a returned borrow must come from a parameter's owner; give a view, span, or record parameter this region")
	}
	if labeled > 1 {
		return invalid(fmt.Sprintf("function %q gives region %s to %d parameters", stmt.Name.Value, displayRegion(sig.Return), labeled),
			"a region names exactly one parameter in this increment; the caller must know which argument the result borrows")
	}
	if len(contract.owners) == 0 {
		return invalid(fmt.Sprintf("function %q: region %s labels a parameter that carries no borrow", stmt.Name.Value, displayRegion(sig.Return)),
			"only view, span, and region-carrying record parameters can be a region's source")
	}
	_ = recordFields
	return contract
}

func displayRegion(region string) string {
	if region == elidedRegion {
		return "(elided)"
	}
	return region
}

// registerRegionRecordParameter registers a record parameter's borrow
// fields as borrows of synthetic owners, one per field path.
func (bc *BorrowChecker) registerRegionRecordParameter(name string, rt *typechecker.RecordType, origin ast.Node) {
	for _, field := range recordBorrowFields(rt, "") {
		owner := parameterOwnerPrefix + name + "." + field.path
		if field.kind == BorrowSpan {
			bc.createSpanBorrowWithRegion(owner, name+"."+field.path, nil, origin)
		} else {
			bc.createViewBorrowWithRegion(owner, name+"."+field.path, nil, origin)
		}
	}
}

// checkReturnedProvenance is the callee's obligation: every borrow the
// result carries must come from the contract's region. Runs while the
// body's borrows are still live.
func (bc *BorrowChecker) checkReturnedProvenance(result ast.Expression, contract *regionContract, env *typechecker.TypeEnvironment) {
	if contract == nil || contract.checked {
		return
	}
	contract.checked = true
	if result == nil {
		return
	}
	owners, ok := bc.provenanceOwners(result, env)
	if ok && len(owners) > 0 {
		outside := []string{}
		for owner := range owners {
			if !contract.owners[owner] {
				outside = append(outside, owner)
			}
		}
		if len(outside) == 0 {
			return
		}
		sort.Strings(outside)
		d := bc.reportBorrow(result, CodeReturnedBorrowRegion,
			fmt.Sprintf("function %q returns a borrow outside its region %s", contract.function, displayRegion(contract.region)))
		for _, owner := range outside {
			d.AddNote(fmt.Sprintf("the result borrows %s, which does not outlive the call", describeOwner(owner)))
		}
		d.AddHelp("return borrows of the region's parameter only (the parameter, a subslice of it, a local bound from it, or its fields), or return owned data")
		return
	}
	d := bc.reportBorrow(result, CodeReturnedBorrowRegion,
		fmt.Sprintf("function %q returns a borrow whose source the checker cannot trace", contract.function))
	d.AddNote("the returned expression is not a view, span, subslice, slice, field, record literal, or conditional over those whose sources are tracked")
	d.AddHelp("bind the borrow first and return the binding")
}

// describeOwner renders a synthetic or real owner name for a diagnostic.
func describeOwner(owner string) string {
	if strings.HasPrefix(owner, parameterOwnerPrefix) {
		rest := owner[len(parameterOwnerPrefix):]
		if dot := strings.IndexByte(rest, '.'); dot >= 0 {
			return fmt.Sprintf("field %q of parameter %q", rest[dot+1:], rest[:dot])
		}
		return fmt.Sprintf("parameter %q", rest)
	}
	if owner != "" && owner[0] == '$' {
		return "a temporary"
	}
	return fmt.Sprintf("local owner %q", owner)
}

// fieldPath renders a dotted field access chain rooted at an identifier.
func fieldPath(expr ast.Expression) (string, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		return e.Value, true
	case *ast.IndexExpression:
		if !e.Dot {
			return "", false
		}
		field, isIdent := e.Index.(*ast.Identifier)
		if !isIdent {
			return "", false
		}
		base, ok := fieldPath(e.Left)
		if !ok {
			return "", false
		}
		return base + "." + field.Value, true
	}
	return "", false
}

// aggregateBorrowNames lists the tracked borrows a record binding carries
// (binding.field...), sorted.
func (bc *BorrowChecker) aggregateBorrowNames(binding string) []string {
	prefix := binding + "."
	var names []string
	for name := range bc.activeBorrows {
		if strings.HasPrefix(name, prefix) {
			names = append(names, name)
		}
	}
	sort.Strings(names)
	return names
}

// provenanceOwners traces a borrow-valued expression to the set of owners
// it borrows: a tracked binding or field, a record binding's fields,
// `view(&owner)`/`span(&owner)`, a subslice or reinterpretation of a traced
// borrow, a slice expression, a record literal (its borrow fields), a
// conditional whose arms are all traced, a block's result, or a
// region-indexed call through its region argument.
func (bc *BorrowChecker) provenanceOwners(expr ast.Expression, env *typechecker.TypeEnvironment) (map[string]bool, bool) {
	owners := map[string]bool{}
	merge := func(sub map[string]bool) {
		for owner := range sub {
			owners[owner] = true
		}
	}
	switch e := expr.(type) {
	case *ast.Identifier:
		if info, tracked := bc.activeBorrows[e.Value]; tracked {
			return map[string]bool{info.owner: true}, true
		}
		if names := bc.aggregateBorrowNames(e.Value); len(names) > 0 {
			for _, name := range names {
				owners[bc.activeBorrows[name].owner] = true
			}
			return owners, true
		}
		if _, isOwner := bc.ownerStates[e.Value]; isOwner {
			return map[string]bool{e.Value: true}, true
		}
		return nil, false
	case *ast.IndexExpression:
		if !e.Dot {
			return nil, false
		}
		path, ok := fieldPath(e)
		if !ok {
			return nil, false
		}
		if info, tracked := bc.activeBorrows[path]; tracked {
			return map[string]bool{info.owner: true}, true
		}
		if names := bc.aggregateBorrowNames(path); len(names) > 0 {
			for _, name := range names {
				owners[bc.activeBorrows[name].owner] = true
			}
			return owners, true
		}
		return nil, false
	case *ast.SliceExpression:
		if ident, isIdent := e.Seq.(*ast.Identifier); isIdent {
			if _, isOwner := bc.ownerStates[ident.Value]; isOwner {
				return map[string]bool{ident.Value: true}, true
			}
		}
		return bc.provenanceOwners(e.Seq, env)
	case *ast.BlockExpression:
		return bc.provenanceOwners(e.Result(), env)
	case *ast.MatchExpression:
		if len(e.Arms) == 0 {
			return nil, false
		}
		for _, arm := range e.Arms {
			sub, ok := bc.provenanceOwners(arm.Body, env)
			if !ok {
				return nil, false
			}
			merge(sub)
		}
		return owners, true
	case *ast.RecordLiteral:
		for _, field := range e.FieldOrder {
			fieldType := env.CheckedExpressionType(field.Value)
			if fieldType == nil || !env.ContainsBorrowStorage(fieldType) {
				continue
			}
			sub, ok := bc.provenanceOwners(field.Value, env)
			if !ok {
				return nil, false
			}
			merge(sub)
		}
		return owners, true
	case *ast.InvocationExpression:
		callee, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return nil, false
		}
		switch callee.Value {
		case "view", "span":
			if len(e.Arguments) == 1 {
				if owner := bc.extractOwnerName(e.Arguments[0]); owner != "" {
					return map[string]bool{owner: true}, true
				}
			}
			return nil, false
		case "subslice", "view_as", "span_as":
			if len(e.Arguments) >= 1 {
				return bc.provenanceOwners(e.Arguments[0], env)
			}
			return nil, false
		}
		if _, sig, ok := regionSignatureFor(callee.Value, env); ok && sig.Return != "" {
			for i, region := range sig.Params {
				if region == sig.Return && i < len(e.Arguments) {
					return bc.provenanceOwners(e.Arguments[i], env)
				}
			}
		}
		return nil, false
	}
	return nil, false
}

// regionCallResult reports whether a call yields a region-indexed borrow
// and, if so, its callee and the region argument.
func regionCallResult(expr ast.Expression, env *typechecker.TypeEnvironment) (callee string, regionArg ast.Expression, fn *typechecker.FunctionType, ok bool) {
	call, isCall := expr.(*ast.InvocationExpression)
	if !isCall {
		return "", nil, nil, false
	}
	ident, isIdent := call.Function.(*ast.Identifier)
	if !isIdent {
		return "", nil, nil, false
	}
	fn, sig, has := regionSignatureFor(ident.Value, env)
	if !has || sig.Return == "" {
		return "", nil, nil, false
	}
	for i, region := range sig.Params {
		if region == sig.Return && i < len(call.Arguments) {
			return ident.Value, call.Arguments[i], fn, true
		}
	}
	return "", nil, nil, false
}

// regionParameterAccepts reports whether the callee's parameter at index i
// carries a region, so a borrow-carrying record may be passed to it.
func regionParameterAccepts(callee string, i int, env *typechecker.TypeEnvironment) bool {
	_, sig, ok := regionSignatureFor(callee, env)
	return ok && i < len(sig.Params) && sig.Params[i] != ""
}

// borrowSource is one live borrow, or an owner about to be borrowed, that
// a region argument denotes at the caller.
type borrowSource struct {
	name    string // borrow name, or owner name when isOwner
	kind    borrowKind
	isOwner bool
}

// sourceBorrows resolves a region argument to the caller's live borrows
// (or owners) it denotes.
func (bc *BorrowChecker) sourceBorrows(expr ast.Expression, env *typechecker.TypeEnvironment) ([]borrowSource, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		if info, tracked := bc.activeBorrows[e.Value]; tracked {
			return []borrowSource{{name: e.Value, kind: info.kind}}, true
		}
		names := bc.aggregateBorrowNames(e.Value)
		if len(names) == 0 {
			return nil, false
		}
		sources := make([]borrowSource, 0, len(names))
		for _, name := range names {
			sources = append(sources, borrowSource{name: name, kind: bc.activeBorrows[name].kind})
		}
		return sources, true
	case *ast.IndexExpression:
		if !e.Dot {
			return nil, false
		}
		path, ok := fieldPath(e)
		if !ok {
			return nil, false
		}
		if info, tracked := bc.activeBorrows[path]; tracked {
			return []borrowSource{{name: path, kind: info.kind}}, true
		}
		names := bc.aggregateBorrowNames(path)
		if len(names) == 0 {
			return nil, false
		}
		sources := make([]borrowSource, 0, len(names))
		for _, name := range names {
			sources = append(sources, borrowSource{name: name, kind: bc.activeBorrows[name].kind})
		}
		return sources, true
	case *ast.SliceExpression:
		if ident, isIdent := e.Seq.(*ast.Identifier); isIdent {
			if _, isOwner := bc.ownerStates[ident.Value]; isOwner {
				return []borrowSource{{name: ident.Value, kind: BorrowView, isOwner: true}}, true
			}
		}
		return bc.sourceBorrows(e.Seq, env)
	case *ast.InvocationExpression:
		callee, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return nil, false
		}
		switch callee.Value {
		case "view", "span":
			if len(e.Arguments) != 1 {
				return nil, false
			}
			owner := bc.extractOwnerName(e.Arguments[0])
			if owner == "" {
				return nil, false
			}
			kind := BorrowView
			if callee.Value == "span" {
				kind = BorrowSpan
			}
			return []borrowSource{{name: owner, kind: kind, isOwner: true}}, true
		case "subslice", "view_as", "span_as":
			if len(e.Arguments) < 1 {
				return nil, false
			}
			return bc.sourceBorrows(e.Arguments[0], env)
		}
		if _, regionArg, _, ok := regionCallResult(e, env); ok {
			return bc.sourceBorrows(regionArg, env)
		}
		return nil, false
	}
	return nil, false
}

// bindRegionCall is the caller's side: a binding initialized from a
// region-indexed call becomes a reborrow of the region argument — one
// borrow per source of the result's kind, or per borrow field of a
// returned record. Reports whether the call was region-indexed.
func (bc *BorrowChecker) bindRegionCall(call *ast.InvocationExpression, targetVar string, env *typechecker.TypeEnvironment) bool {
	callee, regionArg, fn, ok := regionCallResult(call, env)
	if !ok {
		return false
	}
	fail := func(title string) bool {
		d := bc.reportBorrow(regionArg, CodeReturnedBorrowRegion, title)
		d.AddNote("the result of a region-indexed call borrows the argument's owners; the argument must be a tracked view, span, or record binding, view(&owner) or span(&owner), a subslice or slice of one, or another region-indexed call")
		d.AddHelp("bind the borrow first, then pass the binding")
		return true
	}
	sources, traced := bc.sourceBorrows(regionArg, env)
	if !traced || len(sources) == 0 {
		return fail(fmt.Sprintf("cannot bind %q: the region argument of %q is not a traceable borrow", targetVar, callee))
	}
	derive := func(name string, kind borrowKind) bool {
		count := 0
		for _, source := range sources {
			if source.kind != kind {
				continue
			}
			borrowName := name
			if count > 0 {
				borrowName = fmt.Sprintf("%s#%d", name, count)
			}
			count++
			switch {
			case source.isOwner && kind == BorrowSpan:
				bc.createSpanBorrowWithRegion(source.name, borrowName, bc.wholeOwnerRegion(source.name, env), call)
			case source.isOwner:
				bc.createViewBorrowWithRegion(source.name, borrowName, bc.wholeOwnerRegion(source.name, env), call)
			default:
				bc.createSubsliceWithRegion(source.name, borrowName, nil, call)
			}
		}
		return count > 0
	}
	switch ret := fn.ReturnType.(type) {
	case *typechecker.ArrayType:
		kind := BorrowView
		if ret.IsSpan {
			kind = BorrowSpan
		}
		if !derive(targetVar, kind) {
			return fail(fmt.Sprintf("cannot bind %q: the region argument of %q carries no %s", targetVar, callee, kindName(kind)))
		}
	case *typechecker.RecordType:
		for _, field := range recordBorrowFields(ret, "") {
			if !derive(targetVar+"."+field.path, field.kind) {
				return fail(fmt.Sprintf("cannot bind %q: field %q needs a %s and the region argument of %q carries none", targetVar, field.path, kindName(field.kind), callee))
			}
		}
	}
	return true
}

func kindName(kind borrowKind) string {
	if kind == BorrowSpan {
		return "span"
	}
	return "view"
}
