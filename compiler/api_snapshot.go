package compiler

import (
	"fmt"
	"sort"
	"strconv"
	"strings"
	"unicode"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/packageapi"
	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// APISnapshot parses and checks the package, then projects its public semantic
// surface and observable representations into the deterministic format used by
// packageapi.Enforce. Only declarations marked pub are public
// (docs/spec/83-modules.md section 6); visibility is never inferred from
// spelling (docs/spec/82-package-semver.md section 5).
func (comp Compilation) APISnapshot(version string) Stage[packageapi.Snapshot] {
	return comp.Check().Then(func(model *SemanticModel) (packageapi.Snapshot, error) {
		if _, err := packageapi.ParseVersion(version); err != nil {
			return packageapi.Snapshot{}, err
		}
		if model.Tree != nil && model.Tree.Modules != nil && len(model.Tree.Modules.NestedModules) != 0 {
			// Fail closed: a nested module's pub surface is part of the
			// module's API but is not yet projected as its own snapshot, so
			// an API claim over this package would be incomplete
			// (docs/spec/82-package-semver.md section 6).
			return packageapi.Snapshot{}, fmt.Errorf("package %s declares nested modules (%s); API snapshots do not yet cover nested modules — move them to directories to publish", comp.options.PackageName, strings.Join(model.Tree.Modules.NestedModules, ", "))
		}
		return buildAPISnapshot(comp.options.PackageName, version, model, comp.options)
	})
}

func buildAPISnapshot(packageName, version string, model *SemanticModel, options Options) (packageapi.Snapshot, error) {
	layouts, err := resolvePublicStructLayouts(model.PublicRoot, options)
	if err != nil {
		return packageapi.Snapshot{}, fmt.Errorf("public ABI projection failed: %w", err)
	}

	snapshot := packageapi.Snapshot{
		Package: packageName,
		Version: version,
		Exports: make(map[string]packageapi.Export),
	}
	for _, statement := range model.PublicRoot.Statements {
		var name, kind, typeIdentity string
		var concreteStruct bool
		switch declaration := statement.(type) {
		case *ast.ADTType:
			if declaration.Name == nil || !declaration.Exported {
				continue
			}
			name = declaration.Name.Value
			if declaration.Opaque {
				// pub(opaque) exports the name only: neither the definition
				// nor the layout is public API, so changing them is a patch
				// (docs/spec/83-modules.md section 6.2).
				kind, typeIdentity, concreteStruct = "opaque type", "opaque", false
				break
			}
			kind, typeIdentity, concreteStruct, err = canonicalADTDeclaration(declaration, model.TypeChecker)
		case *ast.InterfaceType:
			if declaration.Name == nil || !declaration.Exported {
				continue
			}
			name, kind = declaration.Name.Value, "interface"
			typeIdentity, err = canonicalInterfaceDeclaration(declaration)
		default:
			continue
		}
		if err != nil {
			return packageapi.Snapshot{}, fmt.Errorf("public type %q: %w", name, err)
		}
		abi := ""
		if concreteStruct {
			if layout, ok := layouts[name]; ok {
				abi = canonicalRecordABI(layout.representation, layout.spec)
			} else {
				var ok bool
				abi, ok, err = canonicalGenericStructABI(name, model.PublicRoot)
				if err != nil {
					return packageapi.Snapshot{}, err
				}
				if !ok {
					return packageapi.Snapshot{}, fmt.Errorf("struct %q has no resolved public layout", name)
				}
			}
		}
		snapshot.Exports[name] = packageapi.Export{
			Kind: kind,
			Type: typeIdentity,
			ABI:  abi,
		}
	}

	for _, statement := range model.PublicRoot.Statements {
		var name, kind string
		switch declaration := statement.(type) {
		case *ast.FunctionStatement:
			if declaration.Name == nil || !declaration.Exported {
				continue
			}
			if declaration.Receiver != nil {
				receiver, err := canonicalTypeExpression(declaration.Receiver.Type)
				if err != nil {
					return packageapi.Snapshot{}, fmt.Errorf("public method %q: %w", declaration.Name.Value, err)
				}
				name, kind = receiver+"::"+declaration.Name.Value, "method"
				typeIdentity, err := canonicalFunctionDeclaration(declaration)
				if err != nil {
					return packageapi.Snapshot{}, fmt.Errorf("public method %q: %w", name, err)
				}
				snapshot.Exports[name] = packageapi.Export{Kind: kind, Type: typeIdentity}
				continue
			}
			name, kind = declaration.Name.Value, "function"
		case *ast.VariableDeclaration:
			if declaration.Name == nil || !declaration.Exported {
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

func canonicalADTDeclaration(declaration *ast.ADTType, checker *typechecker.TypeChecker) (string, string, bool, error) {
	parameters, err := canonicalTypeParameters(declaration.TypeParams)
	if err != nil {
		return "", "", false, err
	}
	if len(declaration.Variants) == 1 {
		variant := declaration.Variants[0]
		if variant == nil {
			return "", "", false, fmt.Errorf("nil variant")
		}
		if record, ok := variant.Literal.(*ast.RecordLiteral); ok {
			identity, err := canonicalTypeExpression(record)
			if err != nil {
				return "", "", false, err
			}
			identity = "record" + parameters + strings.TrimPrefix(identity, "record")
			isStruct := record.Token.TokenKind == token.STRUCT
			kind := "record"
			if isStruct {
				kind = "struct"
			}
			return kind, identity, isStruct, nil
		}
		if infix, ok := variant.Literal.(*ast.InfixExpression); ok && infix.Operator == "&" {
			if scheme, ok := checker.Env().Get(declaration.Name.Value); ok && scheme.Type != nil {
				return "record", "record" + parameters + strings.TrimPrefix(canonicalCheckedType(scheme.Type), "record"), false, nil
			}
		}
		if variant.Name != nil && variant.Name.Value == declaration.Name.Value && variant.Payload != nil && variant.Literal == nil {
			base, err := canonicalTypeExpression(variant.Payload)
			if err != nil {
				return "", "", false, err
			}
			return "alias", "alias" + parameters + "(" + base + ")", false, nil
		}
	}
	variants := make([]string, 0, len(declaration.Variants))
	for _, variant := range declaration.Variants {
		if variant == nil || variant.Name == nil {
			return "", "", false, fmt.Errorf("unnamed variant")
		}
		part := variant.Name.Value
		if variant.Payload != nil {
			payload, err := canonicalTypeExpression(variant.Payload)
			if err != nil {
				return "", "", false, err
			}
			part += "(" + payload + ")"
		}
		if variant.Literal != nil {
			part += "=" + strings.ReplaceAll(variant.Literal.String(), " ", "")
		}
		if variant.Result != nil {
			result, err := canonicalTypeExpression(variant.Result)
			if err != nil {
				return "", "", false, err
			}
			part += "=>" + result
		}
		variants = append(variants, part)
	}
	return "sum", "sum" + parameters + "{" + strings.Join(variants, "|") + "}", false, nil
}

func canonicalInterfaceDeclaration(declaration *ast.InterfaceType) (string, error) {
	parameters, err := canonicalTypeParameters(declaration.TypeParams)
	if err != nil {
		return "", err
	}
	methods := make([]string, 0, len(declaration.Methods))
	for _, method := range declaration.Methods {
		if method == nil || method.Name == nil {
			return "", fmt.Errorf("unnamed method")
		}
		parts := make([]string, 0, len(method.Parameters)+1)
		if method.ReceiverType != nil {
			receiver, err := canonicalTypeExpression(method.ReceiverType)
			if err != nil {
				return "", err
			}
			parts = append(parts, receiver)
		}
		for _, parameter := range method.Parameters {
			identity, err := canonicalTypeExpression(parameter.Type)
			if err != nil {
				return "", err
			}
			parts = append(parts, identity)
		}
		result := "()"
		if method.ReturnType != nil {
			result, err = canonicalTypeExpression(method.ReturnType)
			if err != nil {
				return "", err
			}
		}
		methods = append(methods, method.Name.Value+"("+strings.Join(parts, ",")+")->"+result)
	}
	sort.Strings(methods)
	return "interface" + parameters + "{" + strings.Join(methods, ";") + "}", nil
}

func canonicalTypeParameters(parameters []*ast.TypeParameter) (string, error) {
	parts := make([]string, 0, len(parameters))
	for _, parameter := range parameters {
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
		parts = append(parts, part)
	}
	if len(parts) == 0 {
		return "", nil
	}
	return "[" + strings.Join(parts, ",") + "]", nil
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
	if function.Receiver != nil {
		receiver, err := canonicalTypeExpression(function.Receiver.Type)
		if err != nil {
			return "", err
		}
		prefix += "receiver[" + receiver + "]."
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
		// A declared record or struct is part of the API by name; its shape
		// is the named export's own definition (and for pub(opaque) types, no
		// part of the API at all). Spelling it structurally here would leak
		// opaque representations through every signature mentioning them.
		if value.Name != "" {
			return modules.DemangleText(value.Name)
		}
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
	var out strings.Builder
	identifier := make([]rune, 0)
	flush := func() {
		if len(identifier) == 0 {
			return
		}
		word := string(identifier)
		switch word {
		case "byte":
			word = "u8"
		case "rune":
			word = "u32"
		}
		out.WriteString(word)
		identifier = identifier[:0]
	}
	for _, r := range text {
		if unicode.IsLetter(r) || unicode.IsDigit(r) || r == '_' {
			identifier = append(identifier, r)
			continue
		}
		flush()
		if !unicode.IsSpace(r) {
			out.WriteRune(r)
		}
	}
	flush()
	return out.String()
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
			layout, spec, ok, err := resolveRecordLayout(declaration.record, resolved, options, program)
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

func resolveRecordLayout(record *ast.RecordLiteral, resolved map[string]resolvedRecordLayout, options Options, program *ast.Program) (semir.Representation, semir.RecordLayoutSpec, bool, error) {
	fields := make([]semir.RecordFieldRepresentation, 0, len(record.FieldOrder))
	for _, field := range record.FieldOrder {
		representation, ok, err := fieldRepresentation(field, resolved, options, program)
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

func fieldRepresentation(field ast.RecordField, resolved map[string]resolvedRecordLayout, options Options, program *ast.Program) (semir.RecordFieldRepresentation, bool, error) {
	representation, ok, err := naturalTypeRepresentation(field.Name, field.Value, resolved, options, program)
	if err != nil {
		return semir.RecordFieldRepresentation{}, false, err
	}
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

func naturalTypeRepresentation(name string, expression ast.Expression, resolved map[string]resolvedRecordLayout, options Options, program *ast.Program) (semir.RecordFieldRepresentation, bool, error) {
	if indexed, ok := expression.(*ast.IndexExpression); ok {
		if base, isIdent := indexed.Left.(*ast.Identifier); isIdent && base.Value == "Atomic" {
			return naturalTypeRepresentation(name, indexed.Index, resolved, options, program)
		}
		if layout, ok, err := resolveGenericStructApplication(indexed, resolved, options, program); err != nil {
			return semir.RecordFieldRepresentation{}, false, err
		} else if ok {
			return semir.RecordFieldRepresentation{Name: name, Size: layout.Size, Alignment: layout.Alignment}, true, nil
		}
		if length, fixed := indexed.Index.(*ast.IntegerLiteral); fixed && length.Value >= 0 {
			element, ok, err := naturalTypeRepresentation(name, indexed.Left, resolved, options, program)
			if err != nil {
				return semir.RecordFieldRepresentation{}, false, err
			}
			if !ok {
				return semir.RecordFieldRepresentation{}, false, nil
			}
			total := uint64(element.Size) * uint64(length.Value)
			if total > uint64(^uint32(0)) {
				return semir.RecordFieldRepresentation{}, false, nil
			}
			return semir.RecordFieldRepresentation{Name: name, Size: uint32(total), Alignment: element.Alignment}, true, nil
		}
	}
	identifier, ok := expression.(*ast.Identifier)
	if !ok {
		return semir.RecordFieldRepresentation{}, false, nil
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
		return representation, true, nil
	}
	if nested, exists := resolved[identifier.Value]; exists {
		return semir.RecordFieldRepresentation{Name: name, Size: nested.representation.Size, Alignment: nested.representation.Alignment}, true, nil
	}
	return semir.RecordFieldRepresentation{}, false, nil
}

func resolveGenericStructApplication(application *ast.IndexExpression, resolved map[string]resolvedRecordLayout, options Options, program *ast.Program) (semir.Representation, bool, error) {
	name, arguments, ok := flattenGenericApplication(application)
	if !ok {
		return semir.Representation{}, false, nil
	}
	key, err := canonicalTypeExpression(application)
	if err != nil {
		return semir.Representation{}, false, err
	}
	if cached, ok := resolved[key]; ok {
		return cached.representation, true, nil
	}
	for _, statement := range program.Statements {
		template, ok := statement.(*ast.ADTType)
		if !ok || template.Name == nil || template.Name.Value != name || len(template.TypeParams) != len(arguments) || len(template.Variants) != 1 {
			continue
		}
		record, ok := template.Variants[0].Literal.(*ast.RecordLiteral)
		if !ok || record.Token.TokenKind != token.STRUCT {
			return semir.Representation{}, false, nil
		}
		bindings := make(map[string]ast.Expression, len(arguments))
		for i, parameter := range template.TypeParams {
			if parameter == nil || parameter.Name == nil {
				return semir.Representation{}, false, fmt.Errorf("generic struct %q has invalid type parameters", name)
			}
			bindings[parameter.Name.Value] = arguments[i]
		}
		instantiated := *record
		instantiated.Fields = make(map[string]ast.Expression, len(record.Fields))
		instantiated.FieldOrder = make([]ast.RecordField, 0, len(record.FieldOrder))
		for _, field := range record.FieldOrder {
			fieldType, ok := typechecker.SubstituteTypeAST(field.Value, bindings)
			if !ok {
				return semir.Representation{}, false, fmt.Errorf("generic struct %q field %q cannot be specialized", name, field.Name)
			}
			copyField := field
			copyField.Value = fieldType
			instantiated.Fields[field.Name] = fieldType
			instantiated.FieldOrder = append(instantiated.FieldOrder, copyField)
		}
		layout, spec, ok, err := resolveRecordLayout(&instantiated, resolved, options, program)
		if err != nil || !ok {
			return semir.Representation{}, ok, err
		}
		resolved[key] = resolvedRecordLayout{representation: layout, spec: spec}
		return layout, true, nil
	}
	return semir.Representation{}, false, nil
}

func flattenGenericApplication(expression ast.Expression) (string, []ast.Expression, bool) {
	switch value := expression.(type) {
	case *ast.Identifier:
		if value == nil || value.Value == "" {
			return "", nil, false
		}
		return value.Value, nil, true
	case *ast.IndexExpression:
		name, arguments, ok := flattenGenericApplication(value.Left)
		if !ok || value.Index == nil {
			return "", nil, false
		}
		return name, append(arguments, value.Index), true
	default:
		return "", nil, false
	}
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
