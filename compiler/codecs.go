package compiler

import (
	"encoding/json"
	"fmt"
	"reflect"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/modules"
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

type codecField struct {
	name, wire, typ string
	length          int64 // Zero denotes a scalar field; fixed arrays must be nonempty.
	nullable        bool
}

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
		element := field.Value
		length := int64(0)
		nullable := false
		if array, ok := element.(*ast.IndexExpression); ok && !array.Dot {
			if base, named := array.Left.(*ast.Identifier); named && base.Value == "Option" {
				nullable, element = true, array.Index
			} else {
				count, fixed := array.Index.(*ast.IntegerLiteral)
				if !fixed || count.Value <= 0 || count.Value > 4294967295 {
					return nil, fmt.Errorf("codec: %s.%s requires a fixed array length in 1..4294967295", name, field.Name)
				}
				length, element = count.Value, array.Left
			}
		}
		typ, ok := element.(*ast.Identifier)
		if !ok || typ.Value == "string" {
			return nil, fmt.Errorf("codec: unsupported field %s.%s; borrowed fields and composite type applications need further codec support", name, field.Name)
		}
		wire := field.Name
		for _, tag := range field.Tags {
			if !isJSONTag(tag.Name) {
				continue
			}
			schema := d.schemas[tag.Name]
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
		fields = append(fields, codecField{field.Name, wire, typ.Value, length, nullable})
	}
	return fields, nil
}

// codecPrimitive classifies a scalar codec type: "u64" and "i64" for the
// fixed-width integers (the JSON helpers work at 64 bits), "bool" for Bool,
// and "" for anything else.
func codecPrimitive(typ string) string {
	switch typ {
	case "u8", "u16", "u32", "u64":
		return "u64"
	case "i8", "i16", "i32", "i64":
		return "i64"
	case "Bool":
		return "bool"
	}
	return ""
}

// codecConversion widens the value to the JSON helper's width: u64(value),
// i64(value), or the Bool itself.
func codecConversion(s *synth, primitive string) ast.Expression {
	if primitive == "bool" {
		return s.id("value")
	}
	return s.conv(primitive, s.id("value"))
}

// jsonResult is the Result[u32, JsonError] every encoder returns.
func jsonResult(s *synth) ast.Expression {
	return s.app("Result", s.id("u32"), s.id("JsonError"))
}

// errVariant is the .Err(.Name) result.
func errVariant(s *synth, name string) ast.Expression {
	return s.variant("Err", s.variant(name, nil))
}

// derive builds the three encoder functions of one type as typed syntax
// (compiler/synth.go): __oak_json_encoded_size_T measures,
// __oak_json_write_unchecked_T writes measured, checked storage at an offset
// and returns the count, __oak_json_write_T measures and checks capacity
// once then calls it, __oak_json_encode_T writes at 0.
func (d *codecDeriver) derive(typ string) error {
	if d.generated[typ] {
		return nil
	}
	if d.active[typ] {
		return fmt.Errorf("codec: recursive record %s is unsupported", typ)
	}
	d.active[typ] = true
	defer delete(d.active, typ)
	for _, operation := range []string{"encoded_size", "write_unchecked", "write", "encode"} {
		if d.names[codecName(operation, typ)] {
			return fmt.Errorf("codec: generated name %s conflicts with a declaration", codecName(operation, typ))
		}
	}
	sizeName, uncheckedName, writeName, encodeName := codecName("encoded_size", typ), codecName("write_unchecked", typ), codecName("write", typ), codecName("encode", typ)
	size := newSynth("codec:" + sizeName)
	// The unchecked writer (docs/spec/71-codecs.md section 4a) writes a
	// value the caller has already measured into storage the caller has
	// already checked, and returns the byte count. It measures nothing and
	// checks no capacity: one bounds check per record, at the checked
	// entry, instead of one per field at every nesting level. Every store
	// it makes is still a bounds-checked Oak store, so a caller that broke
	// the contract traps rather than writes out of range.
	write := newSynth("codec:" + uncheckedName)
	var sizeBody, writeBody []ast.Statement
	primitive := codecPrimitive(typ)
	switch {
	case primitive != "":
		sizeBody = []ast.Statement{size.expr(size.variant("Ok", size.call("json_"+primitive+"_size", codecConversion(size, primitive))))}
		writeBody = []ast.Statement{write.expr(write.call("json_"+primitive+"_write_at", write.id("dst"), write.id("offset"), codecConversion(write, primitive)))}
	case typ == "string":
		sizeBody = []ast.Statement{
			size.decl("bytes", size.view(size.id("u8")), size.call("str_bytes", size.id("value"))),
			size.expr(size.call("json_string_encode_size", size.id("bytes"))),
		}
		writeBody = []ast.Statement{
			write.decl("bytes", write.view(write.id("u8")), write.call("str_bytes", write.id("value"))),
			write.expr(write.call("json_string_write_at", write.id("dst"), write.id("offset"), write.id("bytes"))),
		}
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
		sizeBody, writeBody, err = recordEncoder(size, write, fields)
		if err != nil {
			return err
		}
	}
	sizeFn := size.fn(sizeName, []*ast.FunctionParameter{size.param("value", size.id(typ))}, jsonResult(size), sizeBody...)
	uncheckedFn := write.fn(uncheckedName,
		[]*ast.FunctionParameter{write.param("value", write.id(typ)), write.param("dst", write.span(write.id("u8"))), write.param("offset", write.id("u32"))},
		write.id("u32"),
		writeBody...)
	// The checked write function is the entry callers reach by name: it
	// measures, checks capacity once, and hands the unchecked writer
	// storage that fits. This retains fail-closed behavior for generated
	// helpers exposed by the bootstrap's flat namespace; callers need no
	// unsafe preflight capability, and the output is unchanged on failure.
	checked := newSynth("codec:" + writeName)
	writeFn := checked.fn(writeName,
		[]*ast.FunctionParameter{checked.param("value", checked.id(typ)), checked.param("dst", checked.span(checked.id("u8"))), checked.param("offset", checked.id("u32"))},
		jsonResult(checked),
		checked.decl("measured", jsonResult(checked), checked.call(sizeName, checked.id("value"))),
		checked.expr(checked.cond(
			checked.not(checked.call("json_result_ok", checked.id("measured"))),
			checked.block(checked.expr(checked.id("measured"))),
			checked.cond(
				checked.not(checked.call("bytes_range_fits", checked.call("len", checked.id("dst")), checked.id("offset"), checked.call("json_result_value", checked.id("measured")))),
				checked.block(checked.expr(errVariant(checked, "DestinationTooSmall"))),
				checked.block(checked.expr(checked.variant("Ok", checked.call(uncheckedName, checked.id("value"), checked.id("dst"), checked.id("offset")))))))))
	encode := newSynth("codec:" + encodeName)
	encodeFn := encode.fn(encodeName,
		[]*ast.FunctionParameter{encode.param("value", encode.id(typ)), encode.param("dst", encode.span(encode.id("u8")))},
		jsonResult(encode),
		encode.expr(encode.call(writeName, encode.id("value"), encode.id("dst"), encode.u32(0))))
	d.output = append(d.output, sizeFn, uncheckedFn, writeFn, encodeFn)
	d.generated[typ] = true
	return nil
}

// recordEncoder builds the measuring and writing bodies of a record's
// encoder: the object braces, each field's key prefix (a leading comma
// after the first), and the field value — scalar, nullable, or a fixed
// array element by element.
func recordEncoder(size, write *synth, fields []codecField) ([]ast.Statement, []ast.Statement, error) {
	sizeBody := []ast.Statement{
		size.decl("total", size.id("u64"), size.intLit(2)),
		size.decl("valid", size.id("Bool"), size.boolean(true)),
	}
	writeBody := []ast.Statement{
		write.decl("out", write.id("u32"), write.id("offset")),
		write.store(write.index(write.id("dst"), write.id("out")), write.u8(123)),
		write.assign("out", write.add(write.id("out"), write.u32(1))),
	}
	for i, field := range fields {
		key, err := json.Marshal(field.wire)
		if err != nil {
			return nil, nil, err
		}
		prefix := append(key, ':')
		if i != 0 {
			prefix = append([]byte{','}, prefix...)
		}
		part := fmt.Sprintf("part%d", i)
		optional := fmt.Sprintf("optional%d", i)
		index := fmt.Sprintf("index%d", i)
		sizeCall := codecName("encoded_size", field.typ)
		// Fields write through the unchecked form: the record's checked
		// entry measured the whole value and checked the destination once.
		writeCall := codecName("write_unchecked", field.typ)
		// value.field, rebuilt per use: nodes are never shared.
		fieldOf := func(s *synth) ast.Expression { return s.field(s.id("value"), field.name) }

		switch {
		case field.nullable:
			sizeBody = append(sizeBody,
				size.assign("total", size.add(size.id("total"), size.u64(uint64(len(prefix))))),
				size.decl(optional, size.app("Option", size.id(field.typ)), fieldOf(size)),
				size.expr(size.match(size.id(optional),
					size.arm("None", "", size.block(size.assign("total", size.add(size.id("total"), size.u64(4))))),
					size.arm("Some", "present", size.block(
						size.decl(part, jsonResult(size), size.call(sizeCall, size.id("present"))),
						size.assign("valid", size.and(size.id("valid"), size.call("json_result_ok", size.id(part)))),
						size.assign("total", size.add(size.id("total"), size.conv("u64", size.call("json_result_value", size.id(part))))))))))
		case field.length == 0:
			sizeBody = append(sizeBody,
				size.decl(part, jsonResult(size), size.call(sizeCall, fieldOf(size))),
				size.assign("valid", size.and(size.id("valid"), size.call("json_result_ok", size.id(part)))),
				size.assign("total", size.add(size.add(size.id("total"), size.u64(uint64(len(prefix)))), size.conv("u64", size.call("json_result_value", size.id(part))))))
		default:
			// Include brackets and commas once; the loop does not expand with N.
			sizeBody = append(sizeBody,
				size.assign("total", size.add(size.id("total"), size.u64(uint64(int64(len(prefix))+field.length+1)))),
				size.decl(index, size.id("u32"), size.intLit(0)),
				size.loop(size.and(size.lt(size.id(index), size.u32(field.length)), size.id("valid")),
					size.decl(part, jsonResult(size), size.call(sizeCall, size.index(fieldOf(size), size.id(index)))),
					size.assign("valid", size.call("json_result_ok", size.id(part))),
					size.assign("total", size.add(size.id("total"), size.conv("u64", size.call("json_result_value", size.id(part))))),
					size.assign("valid", size.and(size.id("valid"), size.le(size.id("total"), size.u64(4294967295)))),
					size.assign(index, size.add(size.id(index), size.u32(1)))))
		}

		for _, b := range prefix {
			writeBody = append(writeBody,
				write.store(write.index(write.id("dst"), write.id("out")), write.u8(int64(b))),
				write.assign("out", write.add(write.id("out"), write.u32(1))))
		}
		emitPart := func(value ast.Expression) []ast.Statement {
			return []ast.Statement{
				write.assign("out", write.add(write.id("out"), write.call(writeCall, value, write.id("dst"), write.id("out")))),
			}
		}
		switch {
		case field.nullable:
			null := []ast.Statement{}
			for k, b := range []byte("null") {
				at := ast.Expression(write.id("out"))
				if k != 0 {
					at = write.add(write.id("out"), write.u32(int64(k)))
				}
				null = append(null, write.store(write.index(write.id("dst"), at), write.u8(int64(b))))
			}
			null = append(null, write.assign("out", write.add(write.id("out"), write.u32(4))))
			writeBody = append(writeBody,
				write.decl(optional, write.app("Option", write.id(field.typ)), fieldOf(write)),
				write.expr(write.match(write.id(optional),
					write.arm("None", "", write.block(null...)),
					write.arm("Some", "present", write.block(emitPart(write.id("present"))...)))))
		case field.length == 0:
			writeBody = append(writeBody, emitPart(fieldOf(write))...)
		default:
			loopBody := []ast.Statement{
				write.expr(write.cond(write.ne(write.id(index), write.u32(0)), write.block(
					write.store(write.index(write.id("dst"), write.id("out")), write.u8(44)),
					write.assign("out", write.add(write.id("out"), write.u32(1)))), nil)),
			}
			loopBody = append(loopBody, emitPart(write.index(fieldOf(write), write.id(index)))...)
			loopBody = append(loopBody, write.assign(index, write.add(write.id(index), write.u32(1))))
			writeBody = append(writeBody,
				write.store(write.index(write.id("dst"), write.id("out")), write.u8(91)),
				write.assign("out", write.add(write.id("out"), write.u32(1))),
				write.decl(index, write.id("u32"), write.intLit(0)),
				write.loop(write.lt(write.id(index), write.u32(field.length)), loopBody...),
				write.store(write.index(write.id("dst"), write.id("out")), write.u8(93)),
				write.assign("out", write.add(write.id("out"), write.u32(1))))
		}
	}
	sizeBody = append(sizeBody, size.expr(size.cond(
		size.or(size.not(size.id("valid")), size.gt(size.id("total"), size.u64(4294967295))),
		size.block(size.expr(errVariant(size, "SizeOverflow"))),
		size.block(size.expr(size.variant("Ok", size.call("u32_trunc_u64", size.id("total"))))))))
	writeBody = append(writeBody,
		write.store(write.index(write.id("dst"), write.id("out")), write.u8(125)),
		write.expr(write.add(write.sub(write.id("out"), write.id("offset")), write.u32(1))))
	return sizeBody, writeBody, nil
}

// isJSONTag recognizes the json tag schema under its flat name or a
// package-scoped internal name (docs/spec/83-modules.md section 6.8).
func isJSONTag(name string) bool {
	if name == "json" {
		return true
	}
	demangled := modules.DemangleText(name)
	return strings.HasSuffix(demangled, ".json")
}
