package compiler

import (
	"fmt"
	"sort"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/packageapi"
	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// APISnapshot parses and checks the package, then projects its public semantic
// surface and observable representations into the deterministic format used by
// packageapi.Enforce. Oak has no private-declaration syntax yet, so every named
// package-level declaration is public in this version of the language.
func (comp Compilation) APISnapshot(version string) Stage[packageapi.Snapshot] {
	return comp.Check().Then(func(model *SemanticModel) (packageapi.Snapshot, error) {
		if _, err := packageapi.ParseVersion(version); err != nil {
			return packageapi.Snapshot{}, err
		}
		return buildAPISnapshot(comp.options.PackageName, version, model, comp.options)
	})
}

func buildAPISnapshot(packageName, version string, model *SemanticModel, options Options) (packageapi.Snapshot, error) {
	module, err := BuildTypeModel(model.PublicRoot)
	if err != nil {
		return packageapi.Snapshot{}, fmt.Errorf("semantic type projection failed: %w", err)
	}
	layouts, err := resolvePublicStructLayouts(model.PublicRoot, options)
	if err != nil {
		return packageapi.Snapshot{}, fmt.Errorf("public ABI projection failed: %w", err)
	}

	snapshot := packageapi.Snapshot{
		Package: packageName,
		Version: version,
		Exports: make(map[string]packageapi.Export),
	}
	for _, definition := range module.Definitions {
		kind := string(definition.Type.Kind)
		abi := ""
		if definition.Type.Kind == semir.TypeRecord && definition.Representation.Kind == semir.RepresentationRecord {
			kind = "struct"
			if layout, ok := layouts[definition.Name]; ok {
				abi = canonicalRecordABI(layout.representation, layout.spec)
			} else {
				var found bool
				abi, found, err = canonicalGenericStructABI(definition.Name, model.PublicRoot)
				if err != nil {
					return packageapi.Snapshot{}, err
				}
				if !found {
					return packageapi.Snapshot{}, fmt.Errorf("struct %q has no resolved public layout", definition.Name)
				}
			}
		}
		snapshot.Exports[definition.Name] = packageapi.Export{
			Kind: kind,
			Type: canonicalDefinitionType(definition.Type),
			ABI:  abi,
		}
	}

	for _, statement := range model.PublicRoot.Statements {
		var name, kind string
		switch declaration := statement.(type) {
		case *ast.FunctionStatement:
			if declaration.Receiver != nil || declaration.Name == nil {
				continue
			}
			name, kind = declaration.Name.Value, "function"
		case *ast.VariableDeclaration:
			if declaration.Name == nil {
				continue
			}
			name, kind = declaration.Name.Value, "value"
		default:
			continue
		}
		scheme, ok := model.TypeChecker.Env().Get(name)
		if function, isFunction := statement.(*ast.FunctionStatement); isFunction && (!ok || scheme == nil || scheme.Type == nil) {
			typeIdentity, err := canonicalFunctionDeclaration(function)
			if err != nil {
				return packageapi.Snapshot{}, fmt.Errorf("public function %q: %w", name, err)
			}
			snapshot.Exports[name] = packageapi.Export{Kind: kind, Type: typeIdentity}
			continue
		}
		if !ok || scheme == nil || scheme.Type == nil {
			return packageapi.Snapshot{}, fmt.Errorf("public %s %q has no checked type", kind, name)
		}
		snapshot.Exports[name] = packageapi.Export{Kind: kind, Type: canonicalScheme(scheme)}
	}
	return snapshot, nil
}

func canonicalFunctionDeclaration(function *ast.FunctionStatement) (string, error) {
	typeParameters := make([]string, 0, len(function.TypeParams))
	for _, parameter := range function.TypeParams {
		if parameter == nil || parameter.Name == nil {
			return "", fmt.Errorf("invalid type parameter")
		}
		part := parameter.Name.Value
		if parameter.Constraint != nil {
			constraint, err := canonicalTypeExpression(parameter.Constraint)
			if err != nil {
				return "", err
			}
			part += ":" + constraint
		}
		typeParameters = append(typeParameters, part)
	}
	parameters := make([]string, 0, len(function.Parameters))
	for _, parameter := range function.Parameters {
		if parameter == nil {
			return "", fmt.Errorf("invalid value parameter")
		}
		identity, err := canonicalTypeExpression(parameter.Type)
		if err != nil {
			return "", err
		}
		if parameter.Variadic {
			identity = "..." + identity
		}
		parameters = append(parameters, identity)
	}
	result := "()"
	if function.ReturnType != nil {
		var err error
		result, err = canonicalTypeExpression(function.ReturnType)
		if err != nil {
			return "", err
		}
	}
	prefix := ""
	if len(typeParameters) != 0 {
		prefix = "forall[" + strings.Join(typeParameters, ",") + "]."
	}
	return prefix + "fn(" + strings.Join(parameters, ",") + ")->" + result, nil
}

func canonicalTypeExpression(expression ast.Expression) (string, error) {
	switch value := expression.(type) {
	case *ast.RecordLiteral:
		names := make([]string, 0, len(value.Fields))
		for name := range value.Fields {
			names = append(names, name)
		}
		sort.Strings(names)
		fields := make([]string, 0, len(names))
		for _, name := range names {
			fieldType, err := canonicalTypeExpression(value.Fields[name])
			if err != nil {
				return "", err
			}
			fields = append(fields, name+":"+fieldType)
		}
		row := ""
		if value.Extension != nil {
			row = "|" + value.Extension.Value
		}
		return "record{" + strings.Join(fields, ",") + row + "}", nil
	case *ast.FunctionTypeExpression:
		parameters := make([]string, 0, len(value.Parameters))
		for _, parameter := range value.Parameters {
			identity, err := canonicalTypeExpression(parameter)
			if err != nil {
				return "", err
			}
			parameters = append(parameters, identity)
		}
		result := "()"
		if value.Return != nil {
			var err error
			result, err = canonicalTypeExpression(value.Return)
			if err != nil {
				return "", err
			}
		}
		return "fn(" + strings.Join(parameters, ",") + ")->" + result, nil
	case *ast.InfixExpression:
		if value.Operator == "&" || value.Operator == "|" {
			left, err := canonicalTypeExpression(value.Left)
			if err != nil {
				return "", err
			}
			right, err := canonicalTypeExpression(value.Right)
			if err != nil {
				return "", err
			}
			parts := []string{left, right}
			sort.Strings(parts)
			return strings.Join(parts, value.Operator), nil
		}
	}
	identity, err := semanticTypeName(expression)
	if err != nil {
		return "", err
	}
	return canonicalTypeText(identity), nil
}

func canonicalDefinitionType(typ semir.Type) string {
	parameters := make([]string, 0, len(typ.Parameters))
	for _, parameter := range typ.Parameters {
		constraint := canonicalIntersection(parameter.Constraint)
		if constraint == "" {
			parameters = append(parameters, parameter.Name)
		} else {
			parameters = append(parameters, parameter.Name+":"+constraint)
		}
	}
	prefix := string(typ.Kind)
	if len(parameters) != 0 {
		prefix += "[" + strings.Join(parameters, ",") + "]"
	}
	switch typ.Kind {
	case semir.TypeRecord:
		fields := append([]semir.Field(nil), typ.Fields...)
		sort.Slice(fields, func(i, j int) bool { return fields[i].Name < fields[j].Name })
		parts := make([]string, 0, len(fields))
		for _, field := range fields {
			parts = append(parts, field.Name+":"+canonicalTypeText(field.Type))
		}
		return prefix + "{" + strings.Join(parts, ",") + "}"
	case semir.TypeAlias:
		return prefix + "(" + canonicalTypeText(typ.Base) + ")"
	case semir.TypeSum:
		variants := make([]string, 0, len(typ.Variants))
		for _, variant := range typ.Variants {
			part := variant.Name
			if variant.Payload != "" {
				part += "(" + canonicalTypeText(variant.Payload) + ")"
			}
			if variant.Result != "" {
				part += "=>" + canonicalTypeText(variant.Result)
			}
			variants = append(variants, part)
		}
		return prefix + "{" + strings.Join(variants, "|") + "}"
	case semir.TypeInterface:
		methods := append([]semir.Method(nil), typ.Methods...)
		sort.Slice(methods, func(i, j int) bool { return methods[i].Name < methods[j].Name })
		parts := make([]string, 0, len(methods))
		for _, method := range methods {
			params := make([]string, 0, len(method.Parameters))
			for _, parameter := range method.Parameters {
				params = append(params, canonicalTypeText(parameter.Type))
			}
			parts = append(parts, method.Name+"("+strings.Join(params, ",")+")->"+canonicalTypeText(method.Return))
		}
		return prefix + "{" + strings.Join(parts, ";") + "}"
	default:
		return prefix
	}
}

func canonicalScheme(scheme *typechecker.TypeScheme) string {
	vars := append([]string(nil), scheme.TypeVars...)
	constraints := make([]string, 0, len(scheme.Constraints))
	for _, constraint := range scheme.Constraints {
		interfaces := append([]string(nil), constraint.Interfaces...)
		sort.Strings(interfaces)
		constraints = append(constraints, constraint.Var+":"+strings.Join(interfaces, "&"))
	}
	sort.Strings(constraints)
	prefix := ""
	if len(vars) != 0 {
		prefix = "forall[" + strings.Join(vars, ",") + "]."
	}
	if len(constraints) != 0 {
		prefix += "where[" + strings.Join(constraints, ",") + "]."
	}
	return prefix + canonicalCheckedType(scheme.Type)
}

func canonicalCheckedType(typ typechecker.Type) string {
	switch value := typ.(type) {
	case *typechecker.PrimitiveType:
		return canonicalTypeText(value.Name)
	case *typechecker.StringType:
		return value.String()
	case *typechecker.BoolType:
		return "Bool"
	case *typechecker.UnitType:
		return "()"
	case *typechecker.NeverType:
		return "never"
	case *typechecker.AnyType:
		return "any"
	case *typechecker.ADTType:
		return value.Name
	case *typechecker.NarrowedADTVariantType:
		args := make([]string, 0, len(value.TypeArgs))
		for _, arg := range value.TypeArgs {
			args = append(args, canonicalCheckedType(arg))
		}
		application := value.ADTName
		if len(args) != 0 {
			application += "[" + strings.Join(args, ",") + "]"
		}
		return application + "::" + value.VariantName
	case *typechecker.RecordType:
		names := make([]string, 0, len(value.Fields))
		for name := range value.Fields {
			names = append(names, name)
		}
		sort.Strings(names)
		fields := make([]string, 0, len(names))
		for _, name := range names {
			fields = append(fields, name+":"+canonicalCheckedType(value.Fields[name]))
		}
		row := ""
		if value.Open {
			row = "|" + value.Row
		}
		return "record{" + strings.Join(fields, ",") + row + "}"
	case *typechecker.InterfaceType:
		return value.Name
	case *typechecker.UnionType:
		return canonicalTypeSet("|", value.Types)
	case *typechecker.IntersectionType:
		return canonicalTypeSet("&", value.Types)
	case *typechecker.FieldAccessorType:
		return "." + value.Field
	case *typechecker.FunctionType:
		params := make([]string, 0, len(value.Parameters))
		for _, parameter := range value.Parameters {
			params = append(params, canonicalCheckedType(parameter))
		}
		if value.Variadic && len(params) != 0 {
			params[len(params)-1] = "..." + strings.TrimPrefix(params[len(params)-1], "[]")
		}
		return "fn(" + strings.Join(params, ",") + ")->" + canonicalCheckedType(value.ReturnType)
	case *typechecker.ArrayType:
		prefix := "[" + strconv.FormatInt(value.Length, 10) + "]"
		if value.IsSpan {
			prefix = "[*]"
		} else if value.IsSlice {
			prefix = "[]"
		}
		return prefix + canonicalCheckedType(value.ElementType)
	case *typechecker.GenericType:
		args := make([]string, 0, len(value.TypeArgs))
		for _, arg := range value.TypeArgs {
			args = append(args, canonicalCheckedType(arg))
		}
		return value.Name + "[" + strings.Join(args, ",") + "]"
	case *typechecker.TypeVar:
		if value.Name != "" {
			return value.Name
		}
		return "#" + strconv.Itoa(value.ID)
	case *typechecker.ConstIntType:
		return strconv.FormatInt(value.Value, 10)
	case *typechecker.AtomicType:
		return "Atomic[" + canonicalCheckedType(value.Element) + "]"
	case *typechecker.CType, *typechecker.SimdType, *typechecker.MmioRegisterType:
		return value.String()
	default:
		return typ.String()
	}
}

func canonicalTypeSet(separator string, types []typechecker.Type) string {
	parts := make([]string, 0, len(types))
	for _, typ := range types {
		parts = append(parts, canonicalCheckedType(typ))
	}
	sort.Strings(parts)
	return strings.Join(parts, separator)
}

func canonicalIntersection(text string) string {
	if text == "" {
		return ""
	}
	parts := strings.Split(text, " & ")
	for i := range parts {
		parts[i] = strings.TrimSpace(parts[i])
	}
	sort.Strings(parts)
	return strings.Join(parts, "&")
}

func canonicalTypeText(text string) string {
	text = strings.ReplaceAll(text, " ", "")
	if text == "byte" {
		return "u8"
	}
	if text == "rune" {
		return "u32"
	}
	return text
}

type resolvedRecordLayout struct {
	representation semir.Representation
	spec           semir.RecordLayoutSpec
}

func resolvePublicStructLayouts(program *ast.Program, options Options) (map[string]resolvedRecordLayout, error) {
	type pendingRecord struct {
		name   string
		record *ast.RecordLiteral
	}
	pending := make([]pendingRecord, 0)
	for _, statement := range program.Statements {
		declaration, ok := statement.(*ast.ADTType)
		if !ok || declaration.Name == nil || len(declaration.TypeParams) != 0 || len(declaration.Variants) != 1 {
			continue
		}
		record, ok := declaration.Variants[0].Literal.(*ast.RecordLiteral)
		if ok && record.Token.TokenKind == token.STRUCT {
			pending = append(pending, pendingRecord{name: declaration.Name.Value, record: record})
		}
	}
	resolved := make(map[string]resolvedRecordLayout)
	for len(pending) != 0 {
		progress := false
		next := pending[:0]
		for _, declaration := range pending {
			layout, spec, ok, err := resolveRecordLayout(declaration.record, resolved, options)
			if err != nil {
				return nil, fmt.Errorf("struct %q: %w", declaration.name, err)
			}
			if !ok {
				next = append(next, declaration)
				continue
			}
			resolved[declaration.name] = resolvedRecordLayout{representation: layout, spec: spec}
			progress = true
		}
		if !progress {
			names := make([]string, 0, len(next))
			for _, declaration := range next {
				names = append(names, declaration.name)
			}
			sort.Strings(names)
			return nil, fmt.Errorf("cannot resolve layouts for %s", strings.Join(names, ", "))
		}
		pending = next
	}
	return resolved, nil
}

func resolveRecordLayout(record *ast.RecordLiteral, resolved map[string]resolvedRecordLayout, options Options) (semir.Representation, semir.RecordLayoutSpec, bool, error) {
	fields := make([]semir.RecordFieldRepresentation, 0, len(record.FieldOrder))
	for _, field := range record.FieldOrder {
		representation, ok, err := fieldRepresentation(field, resolved, options)
		if err != nil {
			return semir.Representation{}, semir.RecordLayoutSpec{}, false, err
		}
		if !ok {
			return semir.Representation{}, semir.RecordLayoutSpec{}, false, nil
		}
		fields = append(fields, representation)
	}
	spec := semir.RecordLayoutSpec{}
	if record.Layout != nil {
		spec.Packed = record.Layout.Packed
		spec.Align = record.Layout.Align
	}
	layout, err := semir.RecordLayoutWithSpec(fields, spec)
	return layout, spec, err == nil, err
}

func fieldRepresentation(field ast.RecordField, resolved map[string]resolvedRecordLayout, options Options) (semir.RecordFieldRepresentation, bool, error) {
	representation, ok := naturalTypeRepresentation(field.Name, field.Value, resolved, options)
	if !ok {
		return semir.RecordFieldRepresentation{}, false, nil
	}
	if field.Align != 0 {
		if field.Align < representation.Alignment {
			return semir.RecordFieldRepresentation{}, false, fmt.Errorf("field %q alignment %d is below natural alignment %d", field.Name, field.Align, representation.Alignment)
		}
		representation.Alignment = field.Align
	}
	return representation, true, nil
}

func naturalTypeRepresentation(name string, expression ast.Expression, resolved map[string]resolvedRecordLayout, options Options) (semir.RecordFieldRepresentation, bool) {
	if indexed, ok := expression.(*ast.IndexExpression); ok {
		if base, isIdent := indexed.Left.(*ast.Identifier); isIdent && base.Value == "Atomic" {
			return naturalTypeRepresentation(name, indexed.Index, resolved, options)
		}
		if length, fixed := indexed.Index.(*ast.IntegerLiteral); fixed && length.Value >= 0 {
			element, ok := naturalTypeRepresentation(name, indexed.Left, resolved, options)
			if !ok {
				return semir.RecordFieldRepresentation{}, false
			}
			total := uint64(element.Size) * uint64(length.Value)
			if total > uint64(^uint32(0)) {
				return semir.RecordFieldRepresentation{}, false
			}
			return semir.RecordFieldRepresentation{Name: name, Size: uint32(total), Alignment: element.Alignment}, true
		}
	}
	identifier, ok := expression.(*ast.Identifier)
	if !ok {
		return semir.RecordFieldRepresentation{}, false
	}
	fixed := map[string]semir.RecordFieldRepresentation{
		"u8": {Size: 1, Alignment: 1}, "i8": {Size: 1, Alignment: 1}, "byte": {Size: 1, Alignment: 1},
		"u16": {Size: 2, Alignment: 2}, "i16": {Size: 2, Alignment: 2},
		"u32": {Size: 4, Alignment: 4}, "i32": {Size: 4, Alignment: 4}, "rune": {Size: 4, Alignment: 4}, "Bool": {Size: 4, Alignment: 4},
		"u64": {Size: 8, Alignment: 8}, "i64": {Size: 8, Alignment: 8},
	}
	if options.IntSize == 32 {
		fixed["int"], fixed["uint"] = fixed["i32"], fixed["u32"]
	} else {
		fixed["int"], fixed["uint"] = fixed["i64"], fixed["u64"]
	}
	if options.PtrSize == 32 {
		fixed["ptr"], fixed["uptr"] = fixed["u32"], fixed["u32"]
	} else {
		fixed["ptr"], fixed["uptr"] = fixed["u64"], fixed["u64"]
	}
	if representation, exists := fixed[identifier.Value]; exists {
		representation.Name = name
		return representation, true
	}
	if nested, exists := resolved[identifier.Value]; exists {
		return semir.RecordFieldRepresentation{Name: name, Size: nested.representation.Size, Alignment: nested.representation.Alignment}, true
	}
	return semir.RecordFieldRepresentation{}, false
}

func canonicalRecordABI(representation semir.Representation, spec semir.RecordLayoutSpec) string {
	parts := []string{
		"size=" + strconv.FormatUint(uint64(representation.Size), 10),
		"align=" + strconv.FormatUint(uint64(representation.Alignment), 10),
		"packed=" + strconv.FormatBool(spec.Packed),
		"declared-align=" + strconv.FormatUint(uint64(spec.Align), 10),
	}
	for _, field := range representation.Fields {
		parts = append(parts, field.Name+"@"+strconv.FormatUint(uint64(field.Offset), 10)+":"+strconv.FormatUint(uint64(field.Size), 10))
	}
	return strings.Join(parts, ";")
}

func canonicalGenericStructABI(name string, program *ast.Program) (string, bool, error) {
	for _, statement := range program.Statements {
		declaration, ok := statement.(*ast.ADTType)
		if !ok || declaration.Name == nil || declaration.Name.Value != name || len(declaration.TypeParams) == 0 || len(declaration.Variants) != 1 {
			continue
		}
		record, ok := declaration.Variants[0].Literal.(*ast.RecordLiteral)
		if !ok || record.Token.TokenKind != token.STRUCT {
			continue
		}
		spec := semir.RecordLayoutSpec{}
		if record.Layout != nil {
			spec.Packed = record.Layout.Packed
			spec.Align = record.Layout.Align
		}
		parts := []string{
			"generic=true",
			"packed=" + strconv.FormatBool(spec.Packed),
			"declared-align=" + strconv.FormatUint(uint64(spec.Align), 10),
		}
		for _, field := range record.FieldOrder {
			identity, err := canonicalTypeExpression(field.Value)
			if err != nil {
				return "", false, fmt.Errorf("struct %q field %q: %w", name, field.Name, err)
			}
			parts = append(parts, field.Name+":"+identity+":align="+strconv.FormatUint(uint64(field.Align), 10))
		}
		return strings.Join(parts, ";"), true, nil
	}
	return "", false, nil
}
