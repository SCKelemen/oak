from pathlib import Path
import re


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"expected one occurrence, got {count}: {old[:80]!r}")
    return text.replace(old, new, 1)


parser_path = Path("parser/parser.go")
p = parser_path.read_text()

p = replace_once(
    p,
    "\tp := &Parser{\n\t\tsource:        source,\n",
    "\tp := &Parser{\n\t\tsource:        token.NewCursor(source),\n",
)

invocation = '''func (p *Parser) parseInvocationExpression(function ast.Expression) ast.Expression {
\texp := &ast.InvocationExpression{Token: p.currentToken, Function: function}
\targs, ok := p.parseDelimited[ast.Expression](
\t\ttoken.LPAREN,
\t\ttoken.RPAREN,
\t\ttoken.COMMA,
\t\tfalse,
\t\tfunc() (ast.Expression, bool) {
\t\t\targ := p.parseExpression(LOWEST)
\t\t\treturn arg, arg != nil
\t\t},
\t)
\tif !ok {
\t\treturn nil
\t}
\texp.Arguments = args
\treturn exp
}

// Parse field access'''
p, n = re.subn(
    r"func \(p \*Parser\) parseInvocationExpression\(function ast\.Expression\) ast\.Expression \{.*?\n\}\n\n// Parse field access",
    invocation,
    p,
    count=1,
    flags=re.S,
)
if n != 1:
    raise RuntimeError(f"invocation replacement count {n}")

p, n = re.subn(
    r"func \(p \*Parser\) parseInvocationArguments\(\) \[\]ast\.Expression \{.*?\n\}\n\nfunc \(p \*Parser\) parseBoolean",
    "func (p *Parser) parseBoolean",
    p,
    count=1,
    flags=re.S,
)
if n != 1:
    raise RuntimeError(f"invocation arguments removal count {n}")

start_marker = "\t\t// Check if this is a generic type: Name[TypeArg1, TypeArg2, ...]\n"
end_marker = "\t\t// Not a generic type - return identifier as-is\n"
start = p.index(start_marker)
end = p.index(end_marker, start)
generic = '''\t\t// Check if this is a generic type: Name[TypeArg1, TypeArg2, ...]
\t\tif p.peekTokenIs(token.LBRACK) {
\t\t\tp.nextToken() // move to '['
\t\t\ttypeArgs, ok := p.parseDelimited[ast.Expression](
\t\t\t\ttoken.LBRACK,
\t\t\t\ttoken.RBRACK,
\t\t\t\ttoken.COMMA,
\t\t\t\tfalse,
\t\t\t\tfunc() (ast.Expression, bool) {
\t\t\t\t\targ := p.parseTypeExpression()
\t\t\t\t\treturn arg, arg != nil
\t\t\t\t},
\t\t\t)
\t\t\tif !ok {
\t\t\t\treturn nil
\t\t\t}

\t\t\tvar result ast.Expression = ident
\t\t\tfor _, arg := range typeArgs {
\t\t\t\tresult = &ast.IndexExpression{
\t\t\t\t\tToken: p.currentToken,
\t\t\t\t\tLeft:  result,
\t\t\t\t\tIndex: arg,
\t\t\t\t}
\t\t\t}
\t\t\treturn result
\t\t}
'''
p = p[:start] + generic + p[end:]

for old, new in (
    (
        "p.parseSeparated[*ast.Identifier](token.RPAREN, token.COMMA, false,",
        "p.parseDelimited[*ast.Identifier](token.LPAREN, token.RPAREN, token.COMMA, false,",
    ),
    (
        "p.parseSeparated[*ast.FunctionParameter](token.RPAREN, token.COMMA, false,",
        "p.parseDelimited[*ast.FunctionParameter](token.LPAREN, token.RPAREN, token.COMMA, false,",
    ),
    (
        "p.parseSeparated[*ast.TypeParameter](token.RBRACK, token.COMMA, false,",
        "p.parseDelimited[*ast.TypeParameter](token.LBRACK, token.RBRACK, token.COMMA, false,",
    ),
):
    p = replace_once(p, old, new)

array_literal = '''// Array literal: [expr1, expr2, ...] or [N]Type{ expr1, expr2, ... }
func (p *Parser) parseArrayLiteral() ast.Expression {
\topen := p.currentToken

\t// Typed slice literal: []Type{ ... }.
\tif p.lookaheadSignificant(1).TokenKind == token.RBRACK &&
\t\tp.lookaheadSignificant(2).TokenKind == token.IDENT &&
\t\tp.lookaheadSignificant(3).TokenKind == token.LBRACE {
\t\tp.nextToken() // ]
\t\tp.nextToken() // element type
\t\telementType := &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
\t\treturn p.parseTypedArrayLiteralWithToken(open, nil, elementType)
\t}

\t// Typed fixed array literal: [N]Type{ ... }.
\tif p.lookaheadSignificant(1).TokenKind == token.INT &&
\t\tp.lookaheadSignificant(2).TokenKind == token.RBRACK &&
\t\tp.lookaheadSignificant(3).TokenKind == token.IDENT &&
\t\tp.lookaheadSignificant(4).TokenKind == token.LBRACE {
\t\tp.nextToken() // N
\t\tsizeExpr := p.parseIntegerLiteral()
\t\tsize, ok := sizeExpr.(*ast.IntegerLiteral)
\t\tif !ok || size == nil {
\t\t\treturn nil
\t\t}
\t\tp.nextToken() // ]
\t\tp.nextToken() // element type
\t\telementType := &ast.Identifier{Token: p.currentToken, Value: p.currentToken.Literal}
\t\treturn p.parseTypedArrayLiteralWithToken(open, size, elementType)
\t}

\telements, ok := p.parseDelimited[ast.Expression](
\t\ttoken.LBRACK,
\t\ttoken.RBRACK,
\t\ttoken.COMMA,
\t\tfalse,
\t\tfunc() (ast.Expression, bool) {
\t\t\telement := p.parseExpression(LOWEST)
\t\t\treturn element, element != nil
\t\t},
\t)
\tif !ok {
\t\treturn nil
\t}
\treturn &ast.ArrayLiteral{Token: open, Elements: elements}
}

// Parse type-qualified literal'''
p, n = re.subn(
    r"// Array literal: \[expr1, expr2, \.\.\.\] or \[N\]Type\{ expr1, expr2, \.\.\. \}\nfunc \(p \*Parser\) parseArrayLiteral\(\) ast\.Expression \{.*?\n\}\n\n// Parse type-qualified literal",
    array_literal,
    p,
    count=1,
    flags=re.S,
)
if n != 1:
    raise RuntimeError(f"array replacement count {n}")

typed_array = '''func (p *Parser) parseTypedArrayLiteralWithToken(bracketToken token.Token, size *ast.IntegerLiteral, elementType ast.Expression) ast.Expression {
\tvar index ast.Expression
\tif size == nil {
\t\tindex = &ast.Identifier{Token: bracketToken, Value: ""}
\t} else {
\t\tindex = size
\t}
\tarrayType := &ast.IndexExpression{Token: bracketToken, Left: elementType, Index: index}

\tif !p.expectPeek(token.LBRACE) {
\t\treturn nil
\t}
\telements, ok := p.parseDelimited[ast.Expression](
\t\ttoken.LBRACE,
\t\ttoken.RBRACE,
\t\ttoken.COMMA,
\t\tfalse,
\t\tfunc() (ast.Expression, bool) {
\t\t\telement := p.parseExpression(LOWEST)
\t\t\treturn element, element != nil
\t\t},
\t)
\tif !ok {
\t\treturn nil
\t}
\treturn &ast.ArrayLiteral{Token: bracketToken, Elements: elements, Type: arrayType}
}

// Function statement'''
p, n = re.subn(
    r"func \(p \*Parser\) parseTypedArrayLiteralWithToken\(bracketToken token\.Token, size \*ast\.IntegerLiteral, elementType ast\.Expression\) ast\.Expression \{.*?\n\}\n\n// Function statement",
    typed_array,
    p,
    count=1,
    flags=re.S,
)
if n != 1:
    raise RuntimeError(f"typed array replacement count {n}")

if p.count("fieldName := p.currentToken.Literal") != 2:
    raise RuntimeError("unexpected record field-name parser count")
p = p.replace(
    "fieldName := p.currentToken.Literal",
    "fieldToken := p.currentToken\n\t\tfieldName := fieldToken.Literal",
)
p = replace_once(p, "record.Fields[fieldName] = fieldType", "record.AddField(fieldToken, fieldName, fieldType)")
p = replace_once(p, "record.Fields[fieldName] = fieldValue", "record.AddField(fieldToken, fieldName, fieldValue)")
parser_path.write_text(p)


ast_path = Path("ast/ast.go")
a = ast_path.read_text()
if '"sort"' in a:
    raise RuntimeError("ast already imports sort")
a = replace_once(a, '"fmt"\n\t"strings"', '"fmt"\n\t"sort"\n\t"strings"')

old = '''// RecordLiteral: { field1: value1, field2: value2, ... }
type RecordLiteral struct {
\tBaseNode
\tToken    token.Token // { token or struct token
\tEndToken token.Token // } token (for end position)
\tFields   map[string]Expression
\tTypeName *Identifier // optional type name for type-qualified literals: TypeName{ ... }
}
'''
new = '''// RecordField is one record member in source order. Value is either a value
// expression or a type expression depending on the record's syntactic context.
type RecordField struct {
\tToken token.Token
\tName  string
\tValue Expression
}

// RecordLiteral represents both record value and record type syntax. Fields is
// retained for O(1) compatibility lookup; FieldOrder is authoritative source order.
type RecordLiteral struct {
\tBaseNode
\tToken      token.Token // { token or struct token
\tEndToken   token.Token // } token (for end position)
\tFields     map[string]Expression
\tFieldOrder []RecordField
\tTypeName   *Identifier // optional type name for type-qualified literals: TypeName{ ... }
}

func (rl *RecordLiteral) AddField(tok token.Token, name string, value Expression) {
\tif rl.Fields == nil {
\t\trl.Fields = make(map[string]Expression)
\t}
\trl.Fields[name] = value
\trl.FieldOrder = append(rl.FieldOrder, RecordField{Token: tok, Name: name, Value: value})
}

// OrderedFields returns source order when it is known. It deliberately returns
// nil for legacy/manually-built map-only records rather than fabricating order.
func (rl *RecordLiteral) OrderedFields() []RecordField {
\tif len(rl.FieldOrder) == 0 {
\t\treturn nil
\t}
\treturn rl.FieldOrder
}
'''
a = replace_once(a, old, new)

old = '''\tfirst := true
\tfor field, expr := range rl.Fields {
\t\tif !first {
\t\t\tout.WriteString(", ")
\t\t}
\t\tout.WriteString(field)
\t\tout.WriteString(": ")
\t\tout.WriteString(expr.String())
\t\tfirst = false
\t}
'''
new = '''\tif len(rl.FieldOrder) > 0 {
\t\tfor i, field := range rl.FieldOrder {
\t\t\tif i > 0 {
\t\t\t\tout.WriteString(", ")
\t\t\t}
\t\t\tout.WriteString(field.Name)
\t\t\tout.WriteString(": ")
\t\t\tout.WriteString(field.Value.String())
\t\t}
\t} else {
\t\t// Legacy/manual ASTs have no source order. Sort only for deterministic
\t\t// rendering; semantic/layout code must not treat this as source order.
\t\tnames := make([]string, 0, len(rl.Fields))
\t\tfor name := range rl.Fields {
\t\t\tnames = append(names, name)
\t\t}
\t\tsort.Strings(names)
\t\tfor i, name := range names {
\t\t\tif i > 0 {
\t\t\t\tout.WriteString(", ")
\t\t\t}
\t\t\tout.WriteString(name)
\t\t\tout.WriteString(": ")
\t\t\tout.WriteString(rl.Fields[name].String())
\t\t}
\t}
'''
a = replace_once(a, old, new)
ast_path.write_text(a)


semantic_path = Path("compiler/semantic_types.go")
s = semantic_path.read_text()
s = replace_once(s, '\t"sort"\n', "")
s = s.replace(
    "// program. It never invents representation information that the AST cannot\n// justify. In particular, record membership is preserved but field layout stays\n// unspecified because the historical AST stores record fields in a map.",
    "// program. It never invents representation information that the AST cannot\n// justify. Record source order is preserved; concrete ABI offsets remain unknown\n// until a target layout pass computes them.",
)
s = s.replace(
    "// Representation intentionally stays unspecified until source field\n\t\t\t// order is preserved by the typed syntax representation.",
    "// Representation intentionally stays unspecified until a target-specific\n\t\t\t// layout pass computes sizes, alignments, and offsets.",
)
old = '''func buildRecordFields(record *ast.RecordLiteral) ([]semir.Field, error) {
\tif record == nil {
\t\treturn nil, fmt.Errorf("nil record")
\t}
\tnames := make([]string, 0, len(record.Fields))
\tfor name := range record.Fields {
\t\tnames = append(names, name)
\t}
\tsort.Strings(names)

\tfields := make([]semir.Field, 0, len(names))
\tfor _, name := range names {
\t\tfieldType, err := semanticTypeName(record.Fields[name])
\t\tif err != nil {
\t\t\treturn nil, fmt.Errorf("field %q: %w", name, err)
\t\t}
\t\tfields = append(fields, semir.Field{Name: name, Type: fieldType})
\t}
\treturn fields, nil
}
'''
new = '''func buildRecordFields(record *ast.RecordLiteral) ([]semir.Field, error) {
\tif record == nil {
\t\treturn nil, fmt.Errorf("nil record")
\t}
\tordered := record.OrderedFields()
\tif len(record.Fields) > 0 && len(ordered) == 0 {
\t\treturn nil, fmt.Errorf("record source order is unavailable")
\t}

\tfields := make([]semir.Field, 0, len(ordered))
\tfor _, field := range ordered {
\t\tfieldType, err := semanticTypeName(field.Value)
\t\tif err != nil {
\t\t\treturn nil, fmt.Errorf("field %q: %w", field.Name, err)
\t\t}
\t\tfields = append(fields, semir.Field{Name: field.Name, Type: fieldType})
\t}
\treturn fields, nil
}
'''
s = replace_once(s, old, new)
semantic_path.write_text(s)


test_path = Path("compiler/semantic_types_test.go")
t = test_path.read_text()
replacement = '''func TestBuildTypeModelPreservesRecordOrderWithoutInventingLayout(t *testing.T) {
\trecord := &ast.RecordLiteral{Fields: make(map[string]ast.Expression)}
\trecord.AddField(ast.Identifier{}.Token, "y", &ast.Identifier{Value: "i32"})
\trecord.AddField(ast.Identifier{}.Token, "x", &ast.Identifier{Value: "i32"})
\tprogram := &ast.Program{Statements: []ast.Statement{
\t\t&ast.ADTType{
\t\t\tName: &ast.Identifier{Value: "Point"},
\t\t\tVariants: []*ast.ADTVariant{
\t\t\t\t{Name: &ast.Identifier{Value: "Point"}, Literal: record},
\t\t\t},
\t\t},
\t}}

\tmodule, err := BuildTypeModel(program)
\tif err != nil {
\t\tt.Fatalf("record projection failed: %v", err)
\t}
\tpoint := module.Definitions[0]
\tif point.Type.Kind != semir.TypeRecord {
\t\tt.Fatalf("expected record semantic type, got %q", point.Type.Kind)
\t}
\tif point.Representation.Kind != semir.RepresentationUnspecified || len(point.Representation.Fields) != 0 {
\t\tt.Fatalf("projector invented ABI representation: %#v", point.Representation)
\t}
\tif got := []string{point.Type.Fields[0].Name, point.Type.Fields[1].Name}; got[0] != "y" || got[1] != "x" {
\t\tt.Fatalf("expected source field order [y x], got %v", got)
\t}
}

func TestBuildTypeModelRejectsRecordWithoutSourceOrder(t *testing.T) {
\tprogram := &ast.Program{Statements: []ast.Statement{
\t\t&ast.ADTType{
\t\t\tName: &ast.Identifier{Value: "Legacy"},
\t\t\tVariants: []*ast.ADTVariant{{
\t\t\t\tName: &ast.Identifier{Value: "Legacy"},
\t\t\t\tLiteral: &ast.RecordLiteral{Fields: map[string]ast.Expression{
\t\t\t\t\t"x": &ast.Identifier{Value: "i32"},
\t\t\t\t}},
\t\t\t}},
\t\t},
\t}}
\t_, err := BuildTypeModel(program)
\tif err == nil || !strings.Contains(err.Error(), "source order is unavailable") {
\t\tt.Fatalf("expected fail-closed record-order error, got %v", err)
\t}
}

func TestBuildTypeModelProjectsInterfaceMethods'''
t, n = re.subn(
    r"func TestBuildTypeModelProjectsRecordWithoutInventingLayout\(t \*testing\.T\) \{.*?\n\}\n\nfunc TestBuildTypeModelProjectsInterfaceMethods",
    replacement,
    t,
    count=1,
    flags=re.S,
)
if n != 1:
    raise RuntimeError(f"semantic record test replacement count {n}")
test_path.write_text(t)
