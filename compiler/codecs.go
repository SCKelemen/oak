package compiler

import (
	"encoding/json"
	"fmt"
	"reflect"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// This closed first codec projection generates ordinary Oak before semantic
// checking. It does not introduce runtime reflection or erased visitor values.
// All generated field accesses and borrows pass through the ordinary gates.
func lowerDerivedCodecs(program *ast.Program) error {
	d := codecDeriver{records: map[string]*ast.ADTType{}, schemas: map[string]*ast.TagDeclaration{}, names: map[string]bool{}, generated: map[string]bool{}, active: map[string]bool{}}
	for _, stmt := range program.Statements {
		if name := declarationName(stmt); name != "" {
			d.names[name] = true
		}
		switch node := stmt.(type) {
		case *ast.ADTType:
			d.records[node.Name.Value] = node
		case *ast.TagDeclaration:
			d.schemas[node.Name.Value] = node
		}
	}
	if err := transformSyntax(reflect.ValueOf(program), func(expr ast.Expression) (ast.Expression, error) {
		call, ok := expr.(*ast.InvocationExpression)
		if !ok {
			return expr, nil
		}
		name, args, ordinary := codecApplication(call.Function)
		values := call.Arguments
		if !ordinary {
			// from[T](value).to[Json](output) is one static operation. Neither
			// a borrowed wrapper nor a temporary source object is constructed.
			index, ok := call.Function.(*ast.IndexExpression)
			if !ok || index.Dot {
				return expr, nil
			}
			member, ok := index.Left.(*ast.IndexExpression)
			if !ok || !member.Dot {
				return expr, nil
			}
			label, ok := member.Index.(*ast.Identifier)
			if !ok || label.Value != "to" {
				return expr, nil
			}
			producer, ok := member.Left.(*ast.InvocationExpression)
			if !ok {
				return expr, nil
			}
			producerName, producerTypes, ok := codecApplication(producer.Function)
			if !ok || producerName != "from" {
				return expr, nil
			}
			if len(producerTypes) != 1 || len(producer.Arguments) != 1 {
				return nil, fmt.Errorf("codec: expected from[T](value).to[Json](output)")
			}
			producerType, named := producerTypes[0].(*ast.Identifier)
			if named && producerType.Value == "Json" {
				if len(values) != 0 {
					return nil, fmt.Errorf("codec: expected from[Json](input).to[T]()")
				}
				name = "decode"
				args = []ast.Expression{index.Index, producerTypes[0]}
				values = producer.Arguments
			} else {
				if len(values) != 1 {
					return nil, fmt.Errorf("codec: expected from[T](value).to[Json](output)")
				}
				name = "encode"
				args = []ast.Expression{producerTypes[0], index.Index}
				values = []ast.Expression{producer.Arguments[0], values[0]}
			}
		}
		if name != "encode" && name != "encoded_size" && name != "decode" {
			return expr, nil
		}
		arity := 2
		if name == "encoded_size" || name == "decode" {
			arity = 1
		}
		if len(args) != 2 || len(values) != arity {
			return nil, fmt.Errorf("codec: %s[T, Json] needs %d value arguments", name, arity)
		}
		typ, typeOK := args[0].(*ast.Identifier)
		format, formatOK := args[1].(*ast.Identifier)
		if !typeOK || !formatOK || format.Value != "Json" {
			return nil, fmt.Errorf("codec: requires a concrete named type and the Json format")
		}
		if name == "decode" {
			if err := d.deriveDecoder(typ.Value); err != nil {
				return nil, err
			}
		} else if err := d.derive(typ.Value); err != nil {
			return nil, err
		}
		lowered := *call
		lowered.Function = &ast.Identifier{Token: call.Token, Value: codecName(name, typ.Value)}
		lowered.Arguments = values
		return &lowered, nil
	}); err != nil {
		return err
	}
	// Reserved producers cannot escape as values or be shadowed by binders.
	if err := transformSyntax(reflect.ValueOf(program), func(expr ast.Expression) (ast.Expression, error) {
		if id, ok := expr.(*ast.Identifier); ok && (id.Value == "from" || id.Value == "encode" || id.Value == "encoded_size" || id.Value == "decode") {
			return nil, fmt.Errorf("codec: %s is reserved for an immediately consumed, explicitly typed codec call", id.Value)
		}
		return expr, nil
	}); err != nil {
		return err
	}
	program.Statements = append(program.Statements, d.output...)
	return nil
}

func codecApplication(expr ast.Expression) (string, []ast.Expression, bool) {
	switch e := expr.(type) {
	case *ast.Identifier:
		return e.Value, nil, true
	case *ast.IndexExpression:
		if !e.Dot {
			name, args, ok := codecApplication(e.Left)
			return name, append(args, e.Index), ok
		}
	}
	return "", nil, false
}

func codecName(operation, typ string) string { return "__oak_json_" + operation + "_" + typ }

type codecDeriver struct {
	decodeGenerated map[string]bool
	decodeActive    map[string]bool
	records         map[string]*ast.ADTType
	schemas         map[string]*ast.TagDeclaration
	names           map[string]bool
	generated       map[string]bool
	active          map[string]bool
	output          []ast.Statement
}

type codecField struct{ name, wire, typ string }

func (d *codecDeriver) fields(name string) ([]codecField, error) {
	decl := d.records[name]
	if decl == nil || len(decl.TypeParams) != 0 || len(decl.Variants) != 1 {
		return nil, fmt.Errorf("codec: unsupported type %s; expected a concrete record, integer, Bool, or top-level string", name)
	}
	record, ok := decl.Variants[0].Literal.(*ast.RecordLiteral)
	if !ok || record.Extension != nil {
		return nil, fmt.Errorf("codec: %s is not a closed record", name)
	}
	fields := []codecField{}
	seen := map[string]bool{}
	for _, field := range record.OrderedFields() {
		typ, ok := field.Value.(*ast.Identifier)
		if !ok || typ.Value == "string" {
			return nil, fmt.Errorf("codec: unsupported field %s.%s; borrowed fields and composite type applications need further codec support", name, field.Name)
		}
		wire := field.Name
		for _, tag := range field.Tags {
			if tag.Name != "json" {
				continue
			}
			schema := d.schemas["json"]
			if schema == nil || len(schema.Schema.OrderedFields()) == 0 {
				return nil, fmt.Errorf("codec: json field tags require a declared tag schema")
			}
			value := tag.Value
			if entries, ok := value.(*ast.RecordLiteral); ok {
				for _, entry := range entries.OrderedFields() {
					if entry.Name != "name" {
						return nil, fmt.Errorf("codec: json tag property %s is not implemented; only name is supported", entry.Name)
					}
				}
				value = entries.Fields["name"]
				if value == nil {
					continue
				}
			} else if schema.Schema.OrderedFields()[0].Name != "name" {
				return nil, fmt.Errorf("codec: bare json tags require name as the schema's first field")
			}
			literal, ok := value.(*ast.StringLiteral)
			if !ok {
				return nil, fmt.Errorf("codec: JSON field names must be string literals")
			}
			wire = literal.Value
		}
		if seen[wire] {
			return nil, fmt.Errorf("codec: %s has duplicate JSON field name %q", name, wire)
		}
		seen[wire] = true
		fields = append(fields, codecField{field.Name, wire, typ.Value})
	}
	return fields, nil
}

func codecPrimitive(typ string) (string, string) {
	switch typ {
	case "u8", "u16", "u32", "u64":
		return "u64", "u64(value)"
	case "i8", "i16", "i32", "i64":
		return "i64", "i64(value)"
	case "Bool":
		return "bool", "value"
	}
	return "", ""
}

func (d *codecDeriver) derive(typ string) error {
	if d.generated[typ] {
		return nil
	}
	if d.active[typ] {
		return fmt.Errorf("codec: recursive record %s is unsupported", typ)
	}
	d.active[typ] = true
	defer delete(d.active, typ)
	for _, operation := range []string{"encoded_size", "write", "encode"} {
		if d.names[codecName(operation, typ)] {
			return fmt.Errorf("codec: generated name %s conflicts with a declaration", codecName(operation, typ))
		}
	}
	var size, write strings.Builder
	primitive, conversion := codecPrimitive(typ)
	switch {
	case primitive != "":
		fmt.Fprintf(&size, ".Ok(json_%s_size(%s))\n", primitive, conversion)
		fmt.Fprintf(&write, "json_%s_encode_at(dst, offset, %s)\n", primitive, conversion)
	case typ == "string":
		size.WriteString("bytes: []u8 = str_bytes(value)\njson_string_encode_size(bytes)\n")
		write.WriteString("bytes: []u8 = str_bytes(value)\njson_string_encode_at(dst, offset, bytes)\n")
	default:
		fields, err := d.fields(typ)
		if err != nil {
			return err
		}
		for _, field := range fields {
			if err := d.derive(field.typ); err != nil {
				return fmt.Errorf("codec field %s.%s: %w", typ, field.name, err)
			}
		}
		size.WriteString("total: u64 = 2\nvalid: Bool = true\n")
		write.WriteString("out: u32 = offset\ndst[out] = u8(123)\nout = out + u32(1)\n")
		for i, field := range fields {
			key, err := json.Marshal(field.wire)
			if err != nil {
				return err
			}
			prefix := append(key, ':')
			if i != 0 {
				prefix = append([]byte{','}, prefix...)
			}
			fmt.Fprintf(&size, "part%d: Result[u32, JsonError] = %s(value.%s)\nvalid = valid && json_result_ok(part%d)\ntotal = total + u64(%d) + u64(json_result_value(part%d))\n", i, codecName("encoded_size", field.typ), field.name, i, len(prefix), i)
			for _, b := range prefix {
				fmt.Fprintf(&write, "dst[out] = u8(%d)\nout = out + u32(1)\n", b)
			}
			fmt.Fprintf(&write, "part%d: Result[u32, JsonError] = %s(value.%s, dst, out)\nassert(json_result_ok(part%d))\nout = out + json_result_value(part%d)\n", i, codecName("write", field.typ), field.name, i, i)
		}
		size.WriteString("!valid || total > u64(4294967295) ? { .Err(.SizeOverflow) } | { .Ok(u32_trunc_u64(total)) }\n")
		write.WriteString("dst[out] = u8(125)\n.Ok(out - offset + u32(1))\n")
	}
	// The write function independently checks capacity, even if called by name.
	// This retains fail-closed behavior for generated helpers exposed by the
	// bootstrap's flat namespace; callers need no unsafe preflight capability.
	source := fmt.Sprintf("%s: (value: %s): Result[u32, JsonError] {\n%s}\n", codecName("encoded_size", typ), typ, size.String())
	source += fmt.Sprintf("%s: (value: %s, dst: [*]u8, offset: u32): Result[u32, JsonError] {\nmeasured: Result[u32, JsonError] = %s(value)\n!json_result_ok(measured) ? { measured } | !bytes_range_fits(len(dst), offset, json_result_value(measured)) ? { .Err(.DestinationTooSmall) } | {\n%s}\n}\n", codecName("write", typ), typ, codecName("encoded_size", typ), write.String())
	source += fmt.Sprintf("%s: (value: %s, dst: [*]u8): Result[u32, JsonError] = %s(value, dst, u32(0))\n", codecName("encode", typ), typ, codecName("write", typ))
	if err := d.appendCodecSource(typ, source); err != nil {
		return err
	}
	d.generated[typ] = true
	return nil
}

func (d *codecDeriver) appendCodecSource(typ, source string) error {
	tree, err := New().WithSource("derived_json.oak", source).Parse().Get()
	if err != nil {
		return fmt.Errorf("codec: generated %s: %w", typ, err)
	}
	// Every generated function needs a distinct resolution context. Source
	// offsets repeat across independently parsed codec instantiations, whose
	// Result types differ; sharing the std context aliases those records.
	for _, stmt := range tree.Root.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok {
			continue
		}
		context := "codec:" + fn.Name.Value
		if err := transformSyntax(reflect.ValueOf(fn), func(expr ast.Expression) (ast.Expression, error) {
			switch node := expr.(type) {
			case *ast.InfixExpression:
				node.Token.SemanticContext = context
			case *ast.MatchExpression:
				node.Token.SemanticContext = context
			case *ast.VariantExpression:
				node.Token.SemanticContext = context
			}
			return expr, nil
		}); err != nil {
			return err
		}
	}
	d.output = append(d.output, tree.Root.Statements...)
	return nil
}
