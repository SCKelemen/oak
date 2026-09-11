package typechecker

// Region parameters (docs/spec/50-borrowing.md section 8c). A region names
// the owner a borrow comes from; it is a type parameter in the surface
// syntax — `frame[R]: (buf: View[u8, R], at: u32): View[u8, R]`,
// `Cursor[R]: type = struct { data: View[u8, R], pos: u32 }` — and erased
// here before checking: `View[T, R]` becomes `[]T`, `Span[T, R]` becomes
// `[*]T`, a region argument to a region-carrying record is dropped, and the
// region-only type parameters leave the declaration. What remains is the
// program the type checker, the backends, and the interpreter already
// understand; the region structure is kept in a side table the borrow
// checker reads through the type environment. Regions are phantom: nothing
// at run time depends on them.

import (
	"reflect"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// RegionSignature is a function's region structure after erasure.
type RegionSignature struct {
	Regions []string // declared region parameters, in order
	Params  []string // the region each parameter's type carries ("" for none)
	Return  string   // the region the return type carries ("" for none)
}

// RegionRecord is a record type's region structure after erasure.
type RegionRecord struct {
	Regions   []string          // declared region parameters, in order
	Positions []int             // their indices in the original parameter list
	Fields    map[string]string // borrow-carrying field -> region
}

type regionInfo struct {
	functions map[string]RegionSignature
	records   map[string]RegionRecord
}

// RegionSignature reports a function's declared region structure.
func (e *TypeEnvironment) RegionSignature(name string) (RegionSignature, bool) {
	info := e.borrowMetadata()
	if info == nil || info.regions == nil {
		return RegionSignature{}, false
	}
	sig, ok := info.regions.functions[name]
	return sig, ok
}

// RegionRecord reports a record type's declared region structure.
func (e *TypeEnvironment) RegionRecord(name string) (RegionRecord, bool) {
	info := e.borrowMetadata()
	if info == nil || info.regions == nil {
		return RegionRecord{}, false
	}
	rec, ok := info.regions.records[name]
	return rec, ok
}

func (tc *TypeChecker) regions() *regionInfo {
	// The metadata lives on the root environment; specializations may run
	// in an enclosed scope, so resolve through the chain.
	info := tc.env.borrowMetadata()
	if info == nil {
		return &regionInfo{functions: map[string]RegionSignature{}, records: map[string]RegionRecord{}}
	}
	if info.regions == nil {
		info.regions = &regionInfo{functions: map[string]RegionSignature{}, records: map[string]RegionRecord{}}
	}
	return info.regions
}

// copyRegionSignature gives a specialization its template's regions.
func (tc *TypeChecker) copyRegionSignature(template, specialized string) {
	info := tc.regions()
	if sig, ok := info.functions[template]; ok {
		info.functions[specialized] = sig
	}
}

// eraseRegions rewrites every region-parameterized declaration in place and
// records the side table. Records first (a function's signature may apply
// them), iterated to a fixpoint so a record may carry another's region.
func (tc *TypeChecker) eraseRegions(program *ast.Program) {
	info := tc.regions()
	for changed := true; changed; {
		changed = false
		for _, stmt := range program.Statements {
			adt, ok := stmt.(*ast.ADTType)
			if !ok || adt.Name == nil || len(adt.TypeParams) == 0 || len(adt.Variants) != 1 || adt.Variants[0].Literal == nil {
				continue
			}
			recordLit, isRecord := adt.Variants[0].Literal.(*ast.RecordLiteral)
			if !isRecord {
				continue
			}
			if tc.eraseRecordRegions(adt, recordLit, info) {
				changed = true
			}
		}
	}
	for _, stmt := range program.Statements {
		if fn, ok := stmt.(*ast.FunctionStatement); ok && fn.Name != nil && fn.Receiver == nil && len(fn.TypeParams) > 0 {
			tc.eraseFunctionRegions(fn, info)
		}
	}
}

// regionParameters selects the type parameters that occur in the given type
// expressions only in region positions (and at least once).
func regionParameters(params []*ast.TypeParameter, types []ast.Expression, records map[string]RegionRecord) map[string]bool {
	regions := map[string]bool{}
	for _, tp := range params {
		if tp == nil || tp.Name == nil || tp.Constraint != nil {
			continue
		}
		name := tp.Name.Value
		regionUses, valueUses := 0, 0
		for _, t := range types {
			r, v := countRegionUses(t, name, records)
			regionUses += r
			valueUses += v
		}
		if regionUses > 0 && valueUses == 0 {
			regions[name] = true
		}
	}
	return regions
}

// countRegionUses counts occurrences of name in region positions and in
// every other position of a type expression.
func countRegionUses(expr ast.Expression, name string, records map[string]RegionRecord) (regionUses, valueUses int) {
	switch e := expr.(type) {
	case nil:
		return 0, 0
	case *ast.Identifier:
		if e.Value == name {
			return 0, 1
		}
		return 0, 0
	case *ast.IndexExpression:
		if isArrayTypeSyntax(e) {
			r, v := countRegionUses(e.Left, name, records)
			r2, v2 := countRegionUses(e.Index, name, records)
			return r + r2, v + v2
		}
		head, args, ok := lenientFlattenApplication(e)
		if !ok {
			return 0, 0
		}
		positions := map[int]bool{}
		switch {
		case (head == "View" || head == "Span") && len(args) == 2:
			positions[1] = true
		default:
			if rec, isRegionRecord := records[head]; isRegionRecord {
				for _, p := range rec.Positions {
					positions[p] = true
				}
			}
		}
		for i, arg := range args {
			if positions[i] {
				if ident, isIdent := arg.(*ast.Identifier); isIdent && ident.Value == name {
					regionUses++
					continue
				}
			}
			r, v := countRegionUses(arg, name, records)
			regionUses += r
			valueUses += v
		}
		return regionUses, valueUses
	case *ast.RecordLiteral:
		for _, field := range e.FieldOrder {
			r, v := countRegionUses(field.Value, name, records)
			regionUses += r
			valueUses += v
		}
		return regionUses, valueUses
	case *ast.FunctionTypeExpression:
		for _, p := range e.Parameters {
			r, v := countRegionUses(p, name, records)
			regionUses += r
			valueUses += v
		}
		r, v := countRegionUses(e.Return, name, records)
		return regionUses + r, valueUses + v
	case *ast.InfixExpression:
		r, v := countRegionUses(e.Left, name, records)
		r2, v2 := countRegionUses(e.Right, name, records)
		return r + r2, v + v2
	}
	return 0, 0
}

// eraseRegionType rewrites one type expression: View/Span applications
// become array syntax, region arguments to region records are dropped.
// Returns the rewritten expression and the region the top-level type
// carries, if any.
func eraseRegionType(expr ast.Expression, regions map[string]bool, records map[string]RegionRecord) (ast.Expression, string) {
	switch e := expr.(type) {
	case *ast.IndexExpression:
		if isArrayTypeSyntax(e) {
			left, _ := eraseRegionType(e.Left, regions, records)
			e.Left = left
			return e, ""
		}
		head, args, ok := lenientFlattenApplication(e)
		if !ok {
			return e, ""
		}
		regionArg := func(arg ast.Expression) (string, bool) {
			ident, isIdent := arg.(*ast.Identifier)
			if !isIdent || !regions[ident.Value] {
				return "", false
			}
			return ident.Value, true
		}
		if (head == "View" || head == "Span") && len(args) == 2 {
			if region, isRegion := regionArg(args[1]); isRegion {
				element, _ := eraseRegionType(args[0], regions, records)
				marker := ""
				if head == "Span" {
					marker = "*"
				}
				return &ast.IndexExpression{Token: e.Token, Left: element, Index: &ast.Identifier{Token: e.Token, Value: marker}}, region
			}
			return e, ""
		}
		rec, isRegionRecord := records[head]
		if !isRegionRecord {
			// An ordinary application (Result[Frame[R], E], Option[View[u8, R]])
			// carries the region its arguments carry.
			carried := ""
			for i := range args {
				var region string
				args[i], region = eraseRegionType(args[i], regions, records)
				if carried == "" {
					carried = region
				}
			}
			return rebuildApplication(e, head, args), carried
		}
		region := ""
		kept := make([]ast.Expression, 0, len(args))
		positions := map[int]bool{}
		for _, p := range rec.Positions {
			positions[p] = true
		}
		for i, arg := range args {
			if positions[i] {
				if r, isRegion := regionArg(arg); isRegion {
					if region == "" {
						region = r
					}
					continue
				}
			}
			rewritten, _ := eraseRegionType(arg, regions, records)
			kept = append(kept, rewritten)
		}
		return rebuildApplication(e, head, kept), region
	case *ast.RecordLiteral:
		for i := range e.FieldOrder {
			rewritten, _ := eraseRegionType(e.FieldOrder[i].Value, regions, records)
			e.FieldOrder[i].Value = rewritten
			e.Fields[e.FieldOrder[i].Name] = rewritten
		}
		return e, ""
	case *ast.FunctionTypeExpression:
		for i := range e.Parameters {
			e.Parameters[i], _ = eraseRegionType(e.Parameters[i], regions, records)
		}
		e.Return, _ = eraseRegionType(e.Return, regions, records)
		return e, ""
	case *ast.InfixExpression:
		e.Left, _ = eraseRegionType(e.Left, regions, records)
		e.Right, _ = eraseRegionType(e.Right, regions, records)
		return e, ""
	}
	return expr, ""
}

// rebuildApplication re-forms Name[args...] (or the bare name).
func rebuildApplication(original *ast.IndexExpression, head string, args []ast.Expression) ast.Expression {
	var result ast.Expression = &ast.Identifier{Token: original.Token, Value: head}
	for _, arg := range args {
		result = &ast.IndexExpression{Token: original.Token, Left: result, Index: arg}
	}
	return result
}

// eraseRecordRegions erases a record's region parameters; reports whether
// it erased any.
func (tc *TypeChecker) eraseRecordRegions(adt *ast.ADTType, recordLit *ast.RecordLiteral, info *regionInfo) bool {
	fieldTypes := make([]ast.Expression, 0, len(recordLit.FieldOrder))
	for _, field := range recordLit.FieldOrder {
		fieldTypes = append(fieldTypes, field.Value)
	}
	regions := regionParameters(adt.TypeParams, fieldTypes, info.records)
	if len(regions) == 0 {
		return false
	}
	rec := RegionRecord{Fields: map[string]string{}}
	remaining := make([]*ast.TypeParameter, 0, len(adt.TypeParams))
	for i, tp := range adt.TypeParams {
		if regions[tp.Name.Value] {
			rec.Regions = append(rec.Regions, tp.Name.Value)
			rec.Positions = append(rec.Positions, i)
			continue
		}
		remaining = append(remaining, tp)
	}
	adt.TypeParams = remaining
	for i := range recordLit.FieldOrder {
		field := &recordLit.FieldOrder[i]
		rewritten, region := eraseRegionType(field.Value, regions, info.records)
		field.Value = rewritten
		recordLit.Fields[field.Name] = rewritten
		if region != "" {
			rec.Fields[field.Name] = region
		}
	}
	info.records[adt.Name.Value] = rec
	return true
}

// eraseFunctionRegions erases a function's region parameters and records
// its signature; local declarations in the body that spell a region are
// rewritten too.
func (tc *TypeChecker) eraseFunctionRegions(fn *ast.FunctionStatement, info *regionInfo) {
	types := make([]ast.Expression, 0, len(fn.Parameters)+1)
	for _, p := range fn.Parameters {
		types = append(types, p.Type)
	}
	types = append(types, fn.ReturnType)
	regions := regionParameters(fn.TypeParams, types, info.records)
	if len(regions) == 0 {
		return
	}
	sig := RegionSignature{Params: make([]string, len(fn.Parameters))}
	remaining := make([]*ast.TypeParameter, 0, len(fn.TypeParams))
	for _, tp := range fn.TypeParams {
		if regions[tp.Name.Value] {
			sig.Regions = append(sig.Regions, tp.Name.Value)
			continue
		}
		remaining = append(remaining, tp)
	}
	fn.TypeParams = remaining
	for i, p := range fn.Parameters {
		p.Type, sig.Params[i] = eraseRegionType(p.Type, regions, info.records)
	}
	fn.ReturnType, sig.Return = eraseRegionType(fn.ReturnType, regions, info.records)
	if fn.Body != nil {
		eraseRegionsInDeclarations(reflect.ValueOf(fn.Body), regions, info.records)
	}
	info.functions[fn.Name.Value] = sig
}

// eraseRegionsInDeclarations rewrites the declared types of local bindings
// anywhere inside a body.
func eraseRegionsInDeclarations(value reflect.Value, regions map[string]bool, records map[string]RegionRecord) {
	switch value.Kind() {
	case reflect.Ptr, reflect.Interface:
		if value.IsNil() {
			return
		}
		if value.CanInterface() {
			if vd, ok := value.Interface().(*ast.VariableDeclaration); ok && vd.Type != nil {
				vd.Type, _ = eraseRegionType(vd.Type, regions, records)
			}
		}
		eraseRegionsInDeclarations(value.Elem(), regions, records)
	case reflect.Struct:
		if value.Type() == reflect.TypeOf(token.Token{}) {
			return
		}
		for i := 0; i < value.NumField(); i++ {
			field := value.Field(i)
			if field.CanSet() || field.Kind() == reflect.Ptr || field.Kind() == reflect.Interface || field.Kind() == reflect.Slice {
				eraseRegionsInDeclarations(field, regions, records)
			}
		}
	case reflect.Slice:
		for i := 0; i < value.Len(); i++ {
			eraseRegionsInDeclarations(value.Index(i), regions, records)
		}
	case reflect.Map:
		for _, key := range value.MapKeys() {
			eraseRegionsInDeclarations(value.MapIndex(key), regions, records)
		}
	}
}
