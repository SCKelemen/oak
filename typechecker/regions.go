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
	Regions        []string            // declared region parameters, in order
	Params         []string            // the region each parameter's type carries ("" for none)
	Return         string              // the region the return type carries ("" for none)
	ParamPaths     []map[string]string // borrow path -> instantiated region, before erasure
	ReturnPaths    map[string]string
	FieldSensitive bool // a signature mentions a record with multiple regions
}

// RegionRecord is a record type's region structure after erasure.
type RegionRecord struct {
	Regions        []string          // declared region parameters, in order
	Positions      []int             // their indices in the original parameter list
	Fields         map[string]string // borrow-carrying field -> region
	Paths          map[string]string // full borrow path -> declared region
	FieldSensitive bool
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
	// Discover metadata before mutating any declarations. Otherwise a record
	// declared before a nested record can lose its first region when a later
	// pass discovers and erases its remaining region parameters.
	for pass := 0; pass < len(program.Statements); pass++ {
		changed := false
		for _, stmt := range program.Statements {
			adt, ok := stmt.(*ast.ADTType)
			if !ok || adt.Name == nil || len(adt.TypeParams) == 0 || len(adt.Variants) != 1 {
				continue
			}
			literal, ok := adt.Variants[0].Literal.(*ast.RecordLiteral)
			if !ok {
				continue
			}
			rec, regions := recordRegionInfo(adt, literal, info)
			if len(regions) > 0 && !reflect.DeepEqual(info.records[adt.Name.Value], rec) {
				info.records[adt.Name.Value] = rec
				changed = true
			}
		}
		if !changed {
			break
		}
	}
	for _, stmt := range program.Statements {
		adt, ok := stmt.(*ast.ADTType)
		if !ok || adt.Name == nil || len(adt.TypeParams) == 0 || len(adt.Variants) != 1 {
			continue
		}
		if literal, ok := adt.Variants[0].Literal.(*ast.RecordLiteral); ok {
			tc.eraseRecordRegions(adt, literal, info)
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
func recordRegionInfo(adt *ast.ADTType, recordLit *ast.RecordLiteral, info *regionInfo) (RegionRecord, map[string]bool) {
	fieldTypes := make([]ast.Expression, 0, len(recordLit.FieldOrder))
	for _, field := range recordLit.FieldOrder {
		fieldTypes = append(fieldTypes, field.Value)
	}
	regions := regionParameters(adt.TypeParams, fieldTypes, info.records)
	rec := RegionRecord{Fields: map[string]string{}, Paths: map[string]string{}, FieldSensitive: len(regions) > 1}
	for i, tp := range adt.TypeParams {
		if regions[tp.Name.Value] {
			rec.Regions = append(rec.Regions, tp.Name.Value)
			rec.Positions = append(rec.Positions, i)
		}
	}
	for _, field := range recordLit.FieldOrder {
		paths, sensitive := regionTypePaths(field.Value, info.records)
		rec.FieldSensitive = rec.FieldSensitive || sensitive
		for path, region := range paths {
			name := field.Name
			if path != "" {
				name += "." + path
			}
			rec.Paths[name] = region
		}
		// Legacy Fields keeps the first carried region without erasing the AST.
		region := firstTypeRegion(field.Value, regions, info.records)
		if region != "" {
			rec.Fields[field.Name] = region
		}
	}
	return rec, regions
}

func (tc *TypeChecker) eraseRecordRegions(adt *ast.ADTType, recordLit *ast.RecordLiteral, info *regionInfo) bool {
	rec, ok := info.records[adt.Name.Value]
	if !ok {
		return false
	}
	regions := map[string]bool{}
	for _, r := range rec.Regions {
		regions[r] = true
	}
	remaining := make([]*ast.TypeParameter, 0, len(adt.TypeParams))
	for _, tp := range adt.TypeParams {
		if !regions[tp.Name.Value] {
			remaining = append(remaining, tp)
		}
	}
	adt.TypeParams = remaining
	for i := range recordLit.FieldOrder {
		field := &recordLit.FieldOrder[i]
		field.Value, _ = eraseRegionType(field.Value, regions, info.records)
		recordLit.Fields[field.Name] = field.Value
	}
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
	sig := RegionSignature{Params: make([]string, len(fn.Parameters)), ParamPaths: make([]map[string]string, len(fn.Parameters))}
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
		paths, sensitive := regionTypePaths(p.Type, info.records)
		sig.ParamPaths[i] = paths
		sig.FieldSensitive = sig.FieldSensitive || sensitive
		p.Type, sig.Params[i] = eraseRegionType(p.Type, regions, info.records)
	}
	var sensitive bool
	sig.ReturnPaths, sensitive = regionTypePaths(fn.ReturnType, info.records)
	sig.FieldSensitive = sig.FieldSensitive || sensitive
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

// regionTypePaths captures field substitutions before erasure. Unsupported
// wrappers retain the field-sensitive flag but no paths, so the borrow checker
// can reject incomplete contracts rather than collapse independent regions.
func regionTypePaths(expr ast.Expression, records map[string]RegionRecord) (map[string]string, bool) {
	e, ok := expr.(*ast.IndexExpression)
	if !ok || isArrayTypeSyntax(e) {
		return nil, false
	}
	head, args, ok := lenientFlattenApplication(e)
	if !ok {
		return nil, false
	}
	if (head == "View" || head == "Span") && len(args) == 2 {
		if r, ok := args[1].(*ast.Identifier); ok {
			return map[string]string{"": r.Value}, false
		}
	}
	if rec, ok := records[head]; ok {
		substitution := map[string]string{}
		for i, pos := range rec.Positions {
			if pos < len(args) {
				if r, ok := args[pos].(*ast.Identifier); ok {
					substitution[rec.Regions[i]] = r.Value
				}
			}
		}
		paths := map[string]string{}
		for path, region := range rec.Paths {
			if r := substitution[region]; r != "" {
				paths[path] = r
			}
		}
		return paths, rec.FieldSensitive
	}
	sensitive := false
	for _, arg := range args {
		_, nested := regionTypePaths(arg, records)
		sensitive = sensitive || nested
	}
	return nil, sensitive
}

func firstTypeRegion(expr ast.Expression, regions map[string]bool, records map[string]RegionRecord) string {
	e, ok := expr.(*ast.IndexExpression)
	if !ok || isArrayTypeSyntax(e) {
		return ""
	}
	head, args, ok := lenientFlattenApplication(e)
	if !ok {
		return ""
	}
	positions := []int{}
	if (head == "View" || head == "Span") && len(args) == 2 {
		positions = []int{1}
	} else if rec, ok := records[head]; ok {
		positions = rec.Positions
	} else {
		for _, arg := range args {
			if r := firstTypeRegion(arg, regions, records); r != "" {
				return r
			}
		}
	}
	for _, pos := range positions {
		if pos < len(args) {
			if r, ok := args[pos].(*ast.Identifier); ok && regions[r.Value] {
				return r.Value
			}
		}
	}
	return ""
}
