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
	"fmt"
	"reflect"

	"github.com/SCKelemen/oak/ast"
)

// commandScalars are the payload scalar types that fit one u32 carrier word.
var commandScalars = map[string]uint64{"u8": 255, "u16": 65535, "u32": 4294967295, "Bool": 1}

type commandField struct {
	name string // "" for a bare scalar payload
	typ  string // the declared type: a carrier scalar or a refinement of u8/u16
	base string // the carrier scalar the field's word holds (typ, or the refinement's base)
	// refinement is the declaration when typ refines base: its predicate
	// over `value` is inlined by the generator (which scans the base range
	// for a value it admits) and the decoder (which refuses a word it
	// rejects), and `typ(v)` constructs the value (docs/spec/20-types.md
	// section 12; docs/spec/112-protocols.md section 1).
	refinement *ast.ADTType
}

// carrierScalar resolves a payload or field type name to the scalar its
// carrier word holds: the name itself, or the base of a refinement of u8 or
// u16. A u32 base is refused: the generator scans the base range for an
// admitted value, which u32 makes unbounded in practice.
func (d *deriver) carrierScalar(name string) (field commandField, ok bool) {
	if _, scalar := commandScalars[name]; scalar {
		return commandField{typ: name, base: name}, true
	}
	decl := d.types[name]
	if base := refinementBase(decl); base == "u8" || base == "u16" {
		return commandField{typ: name, base: base, refinement: decl}, true
	}
	return commandField{}, false
}

// admits is the refinement's predicate with every `value` replaced by a
// freshly made candidate expression, or nil for an unrefined field. The
// candidate is made per occurrence, so no synthesized node is shared or
// copied (the parsed predicate itself is copied once).
func (f commandField) admits(candidate func() ast.Expression) ast.Expression {
	if f.refinement == nil {
		return nil
	}
	return substituteIdentifier(f.refinement.Refinement, "value", candidate)
}

// construct is the field's value from its base: `Name(base)` for a
// refinement, the base itself otherwise.
func (f commandField) construct(s *synth, base ast.Expression) ast.Expression {
	if f.refinement == nil {
		return base
	}
	return s.call(f.typ, base)
}

// substituteIdentifier is a copy of expr with every occurrence of the
// variable `name` replaced by a value `with` makes for that occurrence.
// Unlike rewriteExpressions it does not descend into what it inserts (the
// carrier field `command.value` names a field, not the variable, and would
// otherwise be substituted without end), and it leaves the field name of a
// dotted access alone for the same reason.
func substituteIdentifier(expr ast.Expression, name string, with func() ast.Expression) ast.Expression {
	if id, isIdent := expr.(*ast.Identifier); isIdent {
		if id.Value == name {
			return with()
		}
		return cloneExpression(expr)
	}
	clone := cloneExpression(expr)
	substituteValue(reflect.ValueOf(clone), name, with)
	return clone
}

func substituteValue(v reflect.Value, name string, with func() ast.Expression) {
	switch v.Kind() {
	case reflect.Ptr:
		if v.IsNil() {
			return
		}
		if access, isAccess := v.Interface().(*ast.IndexExpression); isAccess && access.Dot {
			// `x.field`: the field name is not a variable.
			substituteValue(reflect.ValueOf(&access.Left).Elem(), name, with)
			return
		}
		substituteValue(v.Elem(), name, with)
	case reflect.Interface:
		if v.IsNil() {
			return
		}
		if v.Type() == expressionType && v.CanSet() {
			if id, isIdent := v.Interface().(*ast.Identifier); isIdent && id.Value == name {
				v.Set(reflect.ValueOf(with()))
				return // never into the replacement
			}
		}
		substituteValue(v.Elem(), name, with)
	case reflect.Struct:
		for i := 0; i < v.NumField(); i++ {
			if v.Field(i).CanSet() {
				substituteValue(v.Field(i), name, with)
			}
		}
	case reflect.Slice:
		for i := 0; i < v.Len(); i++ {
			substituteValue(v.Index(i), name, with)
		}
	}
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
			if field, scalar := d.carrierScalar(ident.Value); scalar {
				v.fields = []commandField{field}
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
					carrier, scalar := d.carrierScalar(typ.Value)
					if !scalar {
						return unsupported("field %s.%s has type %s; carrier scalars are u8, u16, u32 and Bool, or a refinement of u8 or u16", v.record, field.Name, typ.Value)
					}
					carrier.name = field.Name
					v.fields = append(v.fields, carrier)
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
		var leading []ast.Statement
		for j, field := range v.fields {
			local := fmt.Sprintf("field%d", j)
			leading = append(leading, s.decl(local, s.id(field.base), scalarGenerate(s, field.base)))
			if field.refinement != nil {
				// Scan the base range from the drawn value, wrapping, to the
				// first value the refinement admits: deterministic, and a
				// zero tape lands on the smallest admitted value. A
				// refinement that admits nothing traps at the construction.
				tries := fmt.Sprintf("tries%d", j)
				leading = append(leading,
					s.decl(tries, s.id("u32"), s.u32(0)),
					s.loop(s.and(s.not(field.admits(func() ast.Expression { return s.id(local) })), s.lt(s.id(tries), s.u32(int64(commandScalars[field.base])+1))),
						s.assign(local, s.add(s.id(local), s.conv(field.base, s.intLit(1)))),
						s.assign(tries, s.add(s.id(tries), s.u32(1)))))
			}
			fields = append(fields, field.construct(s, s.id(local)))
		}
		value := s.block(append(leading, s.expr(v.construct(s, typeName, fields)))...)
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
			words[j] = scalarToWord(s, field.base, access)
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
				field := v.fields[j]
				if bound := commandScalars[field.base]; bound < 4294967295 {
					conditions = append(conditions, s.le(word(), s.u32(int64(bound))))
				}
				if admits := field.admits(func() ast.Expression { return scalarFromWord(s, field.base, word()) }); admits != nil {
					// A word the refinement rejects decodes to None, never to
					// a trapping construction.
					conditions = append(conditions, admits)
				}
				fields = append(fields, field.construct(s, scalarFromWord(s, field.base, word())))
			} else {
				conditions = append(conditions, s.eq(word(), s.u32(0)))
			}
		}
		chain = s.cond(s.and(conditions...), s.block(s.expr(s.variant("Some", v.construct(s, typeName, fields)))), chain)
	}
	return s.fn(name, []*ast.FunctionParameter{s.param("command", s.id("TestCommand"))}, s.app("Option", s.id(typeName)), s.expr(chain)), true
}
