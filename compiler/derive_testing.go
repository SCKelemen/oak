package compiler

// Typed test commands (docs/spec/110-testing.md, "Typed commands"): a
// command sum type whose variants carry Unit, one fixed-width scalar, or a
// closed record of at most two scalars derives its generator over the choice
// tape, its packing into the three-word TestCommand carrier, and its
// range-checked decoder. Three kinds, one fact (the declaration), the same
// mechanism as derive.equal: generated Oak text, ordinary parser, every gate.
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
	"strings"

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
func scalarGenerate(typ string) string {
	switch typ {
	case "u8":
		return "u8_trunc_u32(test_range(choices, data, u32(0), u32(255)))"
	case "u16":
		return "u16_trunc_u32(test_range(choices, data, u32(0), u32(65535)))"
	case "Bool":
		return "test_bool(choices, data)"
	}
	return "test_u32(choices, data)"
}

// scalarToWord widens one scalar to a carrier word.
func scalarToWord(typ, expr string) string {
	if typ == "Bool" {
		return "(" + expr + " ? u32(1) | u32(0))"
	}
	return "u32(" + expr + ")"
}

// scalarFromWord narrows one carrier word to a scalar; the caller has already
// checked the range.
func scalarFromWord(typ, word string) string {
	switch typ {
	case "u8":
		return "u8_trunc_u32(" + word + ")"
	case "u16":
		return "u16_trunc_u32(" + word + ")"
	case "Bool":
		return word + " == u32(1)"
	}
	return word
}

func (v commandVariant) construct(typeName string, fields []string) string {
	switch {
	case len(v.fields) == 0:
		return typeName + "." + v.name
	case v.record == "":
		return fmt.Sprintf("%s.%s(%s)", typeName, v.name, fields[0])
	}
	var parts []string
	for i, field := range v.fields {
		parts = append(parts, field.name+": "+fields[i])
	}
	return fmt.Sprintf("%s.%s(%s { %s })", typeName, v.name, v.record, strings.Join(parts, ", "))
}

func (d *deriver) testGenerateHelper(name, typeName string, decl *ast.ADTType, node ast.Node) (string, bool) {
	variants, ok := d.commandVariants("test_generate", typeName, decl, node)
	if !ok {
		return "", false
	}
	var body strings.Builder
	fmt.Fprintf(&body, "%s: (choices: [*]TestChoices, data: []u8): %s {\n  variant: u32 = test_range(choices, data, u32(0), u32(%d))\n", name, typeName, len(variants)-1)
	for i, v := range variants {
		var fields []string
		for _, field := range v.fields {
			fields = append(fields, scalarGenerate(field.typ))
		}
		value := v.construct(typeName, fields)
		if i == len(variants)-1 {
			fmt.Fprintf(&body, "  { %s }\n}", value)
		} else {
			fmt.Fprintf(&body, "  variant == u32(%d) ? { %s } |\n", i, value)
		}
	}
	return body.String(), true
}

func (d *deriver) testEncodeHelper(name, typeName string, decl *ast.ADTType, node ast.Node) (string, bool) {
	variants, ok := d.commandVariants("test_encode", typeName, decl, node)
	if !ok {
		return "", false
	}
	var body strings.Builder
	fmt.Fprintf(&body, "%s: (v: %s): TestCommand = v ?", name, typeName)
	for i, v := range variants {
		words := []string{"u32(0)", "u32(0)"}
		pattern := "." + v.name
		if len(v.fields) != 0 {
			pattern += "(x)"
		}
		for j, field := range v.fields {
			access := "x"
			if v.record != "" {
				access = "x." + field.name
			}
			words[j] = scalarToWord(field.typ, access)
		}
		fmt.Fprintf(&body, "\n | %s => TestCommand { kind: u32(%d), target: %s, value: %s }", pattern, i, words[0], words[1])
	}
	return body.String(), true
}

func (d *deriver) testDecodeHelper(name, typeName string, decl *ast.ADTType, node ast.Node) (string, bool) {
	variants, ok := d.commandVariants("test_decode", typeName, decl, node)
	if !ok {
		return "", false
	}
	var body strings.Builder
	fmt.Fprintf(&body, "%s: (command: TestCommand): Option[%s] {\n", name, typeName)
	for i, v := range variants {
		words := []string{"command.target", "command.value"}
		conditions := []string{fmt.Sprintf("command.kind == u32(%d)", i)}
		var fields []string
		for j, word := range words {
			if j < len(v.fields) {
				if bound := commandScalars[v.fields[j].typ]; bound < 4294967295 {
					conditions = append(conditions, fmt.Sprintf("%s <= u32(%d)", word, bound))
				}
				fields = append(fields, scalarFromWord(v.fields[j].typ, word))
			} else {
				conditions = append(conditions, word+" == u32(0)")
			}
		}
		fmt.Fprintf(&body, "  %s ? { .Some(%s) } |\n", strings.Join(conditions, " && "), v.construct(typeName, fields))
	}
	body.WriteString("  { .None }\n}")
	return body.String(), true
}
