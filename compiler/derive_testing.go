package compiler

// Typed test commands (docs/spec/110-testing.md, "Typed commands"): a
// command sum type whose variants carry Unit, one fixed-width scalar, or a
// closed record of at most two scalars derives its generator over the choice
// tape, its packing into the three-word TestCommand carrier, and its
// range-checked decoder. Three kinds, one fact (the declaration), the same
// mechanism as derive.equal: typed syntax (compiler/synth.go), every gate.
//
//   cmd_generate: (choices: [*]TestChoices, data: []u8): Cmd = derive.test_generate
//   cmd_encode:   (v: Cmd): TestCommand = derive.test_encode
//   cmd_decode:   (command: TestCommand): Option[Cmd] = derive.test_decode
//
// Encoding is injective and canonical: kind is the variant index, the first
// scalar is target, the second is value, and unused words are zero, so the
// runner's command reducer (delete whole commands, shrink words toward zero)
// moves through decodable commands toward the smallest variant payloads.

import (
	"github.com/SCKelemen/oak/ast"
)

// commandScalars are the payload scalar types that fit one u32 carrier word.
var commandScalars = map[string]uint64{"u8": 255, "u16": 65535, "u32": 4294967295, "Bool": 1}

type commandField struct {
	name string // "" for a bare scalar payload
	typ  string
}

type commandVariant struct {
	name   string
	record string // payload record type name, "" for Unit or a bare scalar
	fields []commandField
}

// testCommandType returns the command type of a testing derive request after
// checking the signature of its kind.
func (d *deriver) testCommandType(kind string, fn *ast.FunctionStatement) (*ast.Identifier, bool) {
	bad := func(want string) (*ast.Identifier, bool) {
		d.report(CodeDeriveSignature, fn.Name, "derive.%s requires the signature %s", kind, want)
		return nil, false
	}
	if fn.Receiver != nil || len(fn.TypeParams) != 0 {
		return bad("a non-generic top-level function")
	}
	switch kind {
	case "test_generate":
		if len(fn.Parameters) != 2 || !isSpanOf(fn.Parameters[0].Type, "TestChoices") || !isViewOf(fn.Parameters[1].Type, "u8") {
			return bad("(choices: [*]TestChoices, data: []u8): T")
		}
		ident, ok := fn.ReturnType.(*ast.Identifier)
		if !ok {
			return bad("(choices: [*]TestChoices, data: []u8): T")
		}
		return ident, true
	case "test_encode":
		if len(fn.Parameters) != 1 || !isIdentifierType(fn.ReturnType, "TestCommand") {
			return bad("(v: T): TestCommand")
		}
		ident, ok := fn.Parameters[0].Type.(*ast.Identifier)
		if !ok {
			return bad("(v: T): TestCommand")
		}
		return ident, true
	case "test_decode":
		if len(fn.Parameters) != 1 || !isIdentifierType(fn.Parameters[0].Type, "TestCommand") {
			return bad("(command: TestCommand): Option[T]")
		}
		option, ok := fn.ReturnType.(*ast.IndexExpression)
		if !ok || option.Dot || !isIdentifierType(option.Left, "Option") {
			return bad("(command: TestCommand): Option[T]")
		}
		ident, ok := option.Index.(*ast.Identifier)
		if !ok {
			return bad("(command: TestCommand): Option[T]")
		}
		return ident, true
	}
	return nil, false
}

func isSpanOf(expr ast.Expression, element string) bool {
	index, ok := expr.(*ast.IndexExpression)
	if !ok || index.Dot {
		return false
	}
	marker, ok := index.Index.(*ast.Identifier)
	return ok && marker.Value == "*" && isIdentifierType(index.Left, element)
}

func isViewOf(expr ast.Expression, element string) bool {
	index, ok := expr.(*ast.IndexExpression)
	if !ok || index.Dot {
		return false
	}
	marker, ok := index.Index.(*ast.Identifier)
	return ok && marker.Value == "" && isIdentifierType(index.Left, element)
}

// commandVariants reads a command sum type: every variant carries Unit, one
// carrier scalar, or a closed record of at most two carrier scalars.
func (d *deriver) commandVariants(kind, typeName string, decl *ast.ADTType, node ast.Node) ([]commandVariant, bool) {
	unsupported := func(format string, args ...interface{}) ([]commandVariant, bool) {
		diag := d.report(CodeDeriveUnsupported, node, "derive.%s for %s: "+format, append([]interface{}{kind, typeName}, args...)...)
		diag.AddHelp("command variants carry Unit, one of u8/u16/u32/Bool, or a record of at most two of those")
		return nil, false
	}
	if _, isRecord := recordShape(decl); isRecord || len(decl.Variants) == 0 {
		return unsupported("expected a sum type of command variants")
	}
	var variants []commandVariant
	for _, variant := range decl.Variants {
		if variant.Name == nil || variant.Literal != nil || variant.Result != nil {
			return unsupported("variants must be plain constructors")
		}
		v := commandVariant{name: variant.Name.Value}
		if variant.Payload != nil {
			ident, ok := variant.Payload.(*ast.Identifier)
			if !ok {
				return unsupported("variant %s has a payload the generator cannot carry", v.name)
			}
			if _, scalar := commandScalars[ident.Value]; scalar {
				v.fields = []commandField{{"", ident.Value}}
			} else {
				payload := d.types[ident.Value]
				if payload == nil || len(payload.TypeParams) != 0 {
					return unsupported("variant %s needs a closed record payload of at most two carrier scalars", v.name)
				}
				shape, isRecord := recordShape(payload)
				if !isRecord || len(shape.FieldOrder) > 2 {
					return unsupported("variant %s needs a closed record payload of at most two carrier scalars", v.name)
				}
				v.record = ident.Value
				for _, field := range shape.FieldOrder {
					typ, ok := field.Value.(*ast.Identifier)
					if !ok {
						return unsupported("field %s.%s has a type the carrier cannot hold", v.record, field.Name)
					}
					if _, scalar := commandScalars[typ.Value]; !scalar {
						return unsupported("field %s.%s has type %s; carrier scalars are u8, u16, u32 and Bool", v.record, field.Name, typ.Value)
					}
					v.fields = append(v.fields, commandField{field.Name, typ.Value})
				}
			}
		}
		variants = append(variants, v)
	}
	return variants, true
}

// scalarGenerate draws one scalar of the given type from the choice tape.
func scalarGenerate(s *synth, typ string) ast.Expression {
	switch typ {
	case "u8":
		return s.call("u8_trunc_u32", s.call("test_range", s.id("choices"), s.id("data"), s.u32(0), s.u32(255)))
	case "u16":
		return s.call("u16_trunc_u32", s.call("test_range", s.id("choices"), s.id("data"), s.u32(0), s.u32(65535)))
	case "Bool":
		return s.call("test_bool", s.id("choices"), s.id("data"))
	}
	return s.call("test_u32", s.id("choices"), s.id("data"))
}

// scalarToWord widens one scalar to a carrier word.
func scalarToWord(s *synth, typ string, value ast.Expression) ast.Expression {
	if typ == "Bool" {
		return s.cond(value, s.u32(1), s.u32(0))
	}
	return s.conv("u32", value)
}

// scalarFromWord narrows one carrier word to a scalar; the caller has already
// checked the range.
func scalarFromWord(s *synth, typ string, word ast.Expression) ast.Expression {
	switch typ {
	case "u8":
		return s.call("u8_trunc_u32", word)
	case "u16":
		return s.call("u16_trunc_u32", word)
	case "Bool":
		return s.eq(word, s.u32(1))
	}
	return word
}

// construct builds the variant value Type.Variant, Type.Variant(scalar), or
// Type.Variant(Record { field: value, ... }).
func (v commandVariant) construct(s *synth, typeName string, fields []ast.Expression) ast.Expression {
	switch {
	case len(v.fields) == 0:
		return s.qualified(typeName, v.name, nil)
	case v.record == "":
		return s.qualified(typeName, v.name, fields[0])
	}
	inits := make([]recordInit, 0, len(v.fields))
	for i, field := range v.fields {
		inits = append(inits, s.set(field.name, fields[i]))
	}
	return s.qualified(typeName, v.name, s.record(v.record, inits...))
}

func (d *deriver) testGenerateHelper(name, typeName string, decl *ast.ADTType, node ast.Node) (*ast.FunctionStatement, bool) {
	variants, ok := d.commandVariants("test_generate", typeName, decl, node)
	if !ok {
		return nil, false
	}
	s := newSynth(d.helperContext(decl, name))
	// variant == u32(0) ? { v0 } | variant == u32(1) ? { v1 } | ... | { vlast }
	var chain ast.Expression
	for i := len(variants) - 1; i >= 0; i-- {
		v := variants[i]
		fields := make([]ast.Expression, 0, len(v.fields))
		for _, field := range v.fields {
			fields = append(fields, scalarGenerate(s, field.typ))
		}
		value := s.block(s.expr(v.construct(s, typeName, fields)))
		if chain == nil {
			chain = value
			continue
		}
		chain = s.cond(s.eq(s.id("variant"), s.u32(int64(i))), value, chain)
	}
	return s.fn(name,
		[]*ast.FunctionParameter{s.param("choices", s.span(s.id("TestChoices"))), s.param("data", s.view(s.id("u8")))},
		s.id(typeName),
		s.decl("variant", s.id("u32"), s.call("test_range", s.id("choices"), s.id("data"), s.u32(0), s.u32(int64(len(variants)-1)))),
		s.expr(chain)), true
}

func (d *deriver) testEncodeHelper(name, typeName string, decl *ast.ADTType, node ast.Node) (*ast.FunctionStatement, bool) {
	variants, ok := d.commandVariants("test_encode", typeName, decl, node)
	if !ok {
		return nil, false
	}
	s := newSynth(d.helperContext(decl, name))
	arms := make([]*ast.MatchArm, 0, len(variants))
	for i, v := range variants {
		words := []ast.Expression{s.u32(0), s.u32(0)}
		binding := ""
		if len(v.fields) != 0 {
			binding = "x"
		}
		for j, field := range v.fields {
			var access ast.Expression = s.id("x")
			if v.record != "" {
				access = s.field(s.id("x"), field.name)
			}
			words[j] = scalarToWord(s, field.typ, access)
		}
		arms = append(arms, s.arm(v.name, binding, s.record("TestCommand", s.set("kind", s.u32(int64(i))), s.set("target", words[0]), s.set("value", words[1]))))
	}
	return s.fn(name, []*ast.FunctionParameter{s.param("v", s.id(typeName))}, s.id("TestCommand"), s.expr(s.match(s.id("v"), arms...))), true
}

func (d *deriver) testDecodeHelper(name, typeName string, decl *ast.ADTType, node ast.Node) (*ast.FunctionStatement, bool) {
	variants, ok := d.commandVariants("test_decode", typeName, decl, node)
	if !ok {
		return nil, false
	}
	s := newSynth(d.helperContext(decl, name))
	var chain ast.Expression = s.block(s.expr(s.variant("None", nil)))
	for i := len(variants) - 1; i >= 0; i-- {
		v := variants[i]
		words := []func() ast.Expression{
			func() ast.Expression { return s.field(s.id("command"), "target") },
			func() ast.Expression { return s.field(s.id("command"), "value") },
		}
		conditions := []ast.Expression{s.eq(s.field(s.id("command"), "kind"), s.u32(int64(i)))}
		var fields []ast.Expression
		for j, word := range words {
			if j < len(v.fields) {
				if bound := commandScalars[v.fields[j].typ]; bound < 4294967295 {
					conditions = append(conditions, s.le(word(), s.u32(int64(bound))))
				}
				fields = append(fields, scalarFromWord(s, v.fields[j].typ, word()))
			} else {
				conditions = append(conditions, s.eq(word(), s.u32(0)))
			}
		}
		chain = s.cond(s.and(conditions...), s.block(s.expr(s.variant("Some", v.construct(s, typeName, fields)))), chain)
	}
	return s.fn(name, []*ast.FunctionParameter{s.param("command", s.id("TestCommand"))}, s.app("Option", s.id(typeName)), s.expr(chain)), true
}
