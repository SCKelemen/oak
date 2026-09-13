package asm

import (
	"fmt"
	"math"

	"github.com/SCKelemen/oak/ast"
)

// The raw syntax table: a theorem, the functions its body names, and the
// program's record and sum-type declarations, serialized as the parser
// produced them — identifiers, operators, and type names as strings,
// nothing resolved or typed — for the syntax serializer written in Oak
// (prove/solver/syntax.oak), which resolves names, types the subset, lays
// out the leaves, and builds the syntax table the Oak lowering reads
// (asm/syntax.go describes that table; ExportSyntax is its Go twin, kept
// as the cross-check). A parser written in Oak will produce this table
// directly; until then the Go parser's tree is dumped into it here.
//
// Words: a 16-word header (strings, pool words, type expressions, nodes,
// list words, functions, parameters, records, fields, sum types, variants,
// the theorem's function index), the string table (2 words each: byte
// offset, byte length), the byte pool (four bytes per word, little-endian),
// the type expressions (4 words each: kind, name or element, length), the
// functions (8 words each: name, parameter start, parameter count, result
// type, body node, flags), the parameters (4 words each: name, type,
// variadic), the records (4 words each: name, field start, field count),
// the fields (4 words each: name, type), the sum types (4 words each:
// name, variant start, variant count), the variants (4 words each: name,
// tag, payload type), the nodes (8 words each: kind, a, b, c, d, value
// low, value high), and the lists.
const (
	rawIntLit      = 0  // vlo, vhi
	rawBoolLit     = 1  // a = 1 or 0
	rawFloatLit    = 2  // a = the f32 bits, vlo/vhi = the f64 bits
	rawIdent       = 3  // a = string
	rawPrefix      = 4  // a = operator string, b = operand
	rawInfix       = 5  // a = operator string, b = left, c = right
	rawBlockExpr   = 6  // a = block node (NONE when empty)
	rawBlock       = 7  // a = list start, b = statement count
	rawVariant     = 8  // a = type name string (NONE for none), b = variant string, c = payload (NONE for none)
	rawMatch       = 9  // a = scrutinee, b = arms list start (pattern node, body node per arm), c = arm count
	rawPatVariant  = 10 // a = type name string (NONE for none), b = variant string, c = payload pattern (NONE for none)
	rawPatLiteral  = 11 // a = value node
	rawPatWild     = 12
	rawPatBinding  = 13 // a = name string
	rawIndex       = 14 // a = base, b = index, c = 1 for a dotted access
	rawRecordLit   = 15 // a = type name string (NONE for none), b = list start (field name string, value per field), c = field count
	rawArrayLit    = 16 // a = type expression (NONE for none), b = list start, c = element count
	rawCall        = 17 // a = function node, b = list start, c = argument count
	rawExprStmt    = 18 // a = expression
	rawVarDecl     = 19 // a = name string, b = type expression (NONE for none), c = value (NONE for none)
	rawAssign      = 20 // a = name string, b = value
	rawIndexAssign = 21 // a = target node, b = value
	rawWhile       = 22 // a = condition, b = body block node
	rawOther       = 23 // a = the Go node type's name, as a string

	rawTypeName  = 0 // a = name string
	rawTypeArray = 1 // a = element type expression, b = length
	rawTypeOther = 2 // a = the type's text, as a string

	rawFlagUnusable = 1 // a method, generic, foreign, or definition-less function
)

type rawWriter struct {
	strings   map[string]uint32
	pool      []byte
	strTable  []uint32
	types     []uint32
	funcs     []uint32
	params    []uint32
	records   []uint32
	fields    []uint32
	adts      []uint32
	variants  []uint32
	nodes     []uint32
	lists     []uint32
	functions map[string]*ast.FunctionStatement
	funcIndex map[string]uint32
	pending   []string
}

// ExportRaw serializes the theorem for the Oak serializer: the theorem,
// every program function reachable by name from its body, and the
// program's record and sum-type declarations. It fails only on a theorem
// without a body.
func ExportRaw(sig *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, decls Declarations) ([]uint32, bool) {
	if sig == nil || sig.Name == nil || sig.Body == nil {
		return nil, false
	}
	w := &rawWriter{strings: map[string]uint32{}, functions: functions, funcIndex: map[string]uint32{}}
	theorem := w.function(sig)
	for len(w.pending) > 0 {
		name := w.pending[0]
		w.pending = w.pending[1:]
		w.function(functions[name])
	}
	for _, name := range sortedKeys(decls.Records) {
		literal := decls.Records[name]
		start := uint32(len(w.fields) / 4)
		for _, field := range literal.FieldOrder {
			w.fields = append(w.fields, w.str(field.Name), w.typeExpr(field.Value), 0, 0)
		}
		w.records = append(w.records, w.str(name), start, uint32(len(literal.FieldOrder)), 0)
	}
	for _, name := range sortedKeys(decls.ADTs) {
		adt := decls.ADTs[name]
		start := uint32(len(w.variants) / 4)
		for i, variant := range adt.Variants {
			tag := i
			if i < len(adt.TagValues) {
				tag = adt.TagValues[i]
			}
			payload := problemNone
			if variant.Payload != nil {
				payload = w.typeExpr(variant.Payload)
			}
			w.variants = append(w.variants, w.str(variant.Name.Value), uint32(tag), payload, 0)
		}
		w.adts = append(w.adts, w.str(name), start, uint32(len(adt.Variants)), 0)
	}
	for len(w.pool)%4 != 0 {
		w.pool = append(w.pool, 0)
	}
	poolWords := make([]uint32, len(w.pool)/4)
	for i := range poolWords {
		poolWords[i] = uint32(w.pool[4*i]) | uint32(w.pool[4*i+1])<<8 | uint32(w.pool[4*i+2])<<16 | uint32(w.pool[4*i+3])<<24
	}
	header := []uint32{uint32(len(w.strTable) / 2), uint32(len(poolWords)), uint32(len(w.types) / 4), uint32(len(w.nodes) / 8), uint32(len(w.lists)), uint32(len(w.funcs) / 8), uint32(len(w.params) / 4), uint32(len(w.records) / 4), uint32(len(w.fields) / 4), uint32(len(w.adts) / 4), uint32(len(w.variants) / 4), theorem, 0, 0, 0, 0}
	words := make([]uint32, 0, len(header)+len(w.strTable)+len(poolWords)+len(w.types)+len(w.funcs)+len(w.params)+len(w.records)+len(w.fields)+len(w.adts)+len(w.variants)+len(w.nodes)+len(w.lists))
	for _, section := range [][]uint32{header, w.strTable, poolWords, w.types, w.funcs, w.params, w.records, w.fields, w.adts, w.variants, w.nodes, w.lists} {
		words = append(words, section...)
	}
	return words, true
}

func sortedKeys[V any](m map[string]V) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	for i := 1; i < len(keys); i++ {
		for j := i; j > 0 && keys[j] < keys[j-1]; j-- {
			keys[j], keys[j-1] = keys[j-1], keys[j]
		}
	}
	return keys
}

// str interns a string: one id per distinct text.
func (w *rawWriter) str(s string) uint32 {
	if id, seen := w.strings[s]; seen {
		return id
	}
	id := uint32(len(w.strTable) / 2)
	w.strings[s] = id
	w.strTable = append(w.strTable, uint32(len(w.pool)), uint32(len(s)))
	w.pool = append(w.pool, s...)
	return id
}

func (w *rawWriter) node(kind, a, b, c, d, vlo, vhi uint32) uint32 {
	id := uint32(len(w.nodes) / 8)
	w.nodes = append(w.nodes, kind, a, b, c, d, vlo, vhi, 0)
	return id
}

func (w *rawWriter) list(ids []uint32) uint32 {
	start := uint32(len(w.lists))
	w.lists = append(w.lists, ids...)
	return start
}

// typeExpr serializes a type expression: a name (an instantiation under
// its mangled name), a fixed array, or anything else by its text.
func (w *rawWriter) typeExpr(expr ast.Expression) uint32 {
	id := uint32(len(w.types) / 4)
	switch e := expr.(type) {
	case *ast.Identifier:
		w.types = append(w.types, rawTypeName, w.str(e.Value), 0, 0)
		return id
	case *ast.IndexExpression:
		if !e.Dot {
			if length, isLit := e.Index.(*ast.IntegerLiteral); isLit && length.Value > 0 {
				w.types = append(w.types, rawTypeArray, 0, uint32(length.Value), 0)
				w.types[4*id+1] = w.typeExpr(e.Left)
				return id
			}
			if name, ok := TypeApplicationName(expr); ok {
				w.types = append(w.types, rawTypeName, w.str(name), 0, 0)
				return id
			}
		}
	}
	w.types = append(w.types, rawTypeOther, w.str(typeText(expr)), 0, 0)
	return id
}

// function serializes a function the body names (once), returning its
// index; the functions a body names are queued.
func (w *rawWriter) function(fn *ast.FunctionStatement) uint32 {
	if index, seen := w.funcIndex[fn.Name.Value]; seen && index != problemNone {
		return index
	}
	index := uint32(len(w.funcs) / 8)
	w.funcIndex[fn.Name.Value] = index
	w.funcs = append(w.funcs, w.str(fn.Name.Value), 0, 0, 0, 0, 0, 0, 0)
	flags := uint32(0)
	if fn.Receiver != nil || len(fn.TypeParams) != 0 || fn.Body == nil || fn.ExternSymbol != "" {
		flags |= rawFlagUnusable
	}
	paramStart := uint32(len(w.params) / 4)
	for _, p := range fn.Parameters {
		variadic := uint32(0)
		if p.Variadic {
			variadic = 1
		}
		w.params = append(w.params, w.str(p.Name.Value), w.typeExpr(p.Type), variadic, 0)
	}
	ret := problemNone
	if fn.ReturnType != nil {
		ret = w.typeExpr(fn.ReturnType)
	}
	body := problemNone
	if fn.Body != nil {
		body = w.expr(fn.Body)
	}
	at := 8 * index
	w.funcs[at+1], w.funcs[at+2], w.funcs[at+3], w.funcs[at+4], w.funcs[at+5] = paramStart, uint32(len(fn.Parameters)), ret, body, flags
	return index
}

func (w *rawWriter) optional(e ast.Expression) uint32 {
	if e == nil {
		return problemNone
	}
	return w.expr(e)
}

// expr serializes an expression or statement node.
func (w *rawWriter) expr(e ast.Node) uint32 {
	switch e := e.(type) {
	case *ast.IntegerLiteral:
		v := uint64(e.Value)
		return w.node(rawIntLit, 0, 0, 0, 0, uint32(v), uint32(v>>32))
	case *ast.Boolean:
		bit := uint32(0)
		if e.Value {
			bit = 1
		}
		return w.node(rawBoolLit, bit, 0, 0, 0, 0, 0)
	case *ast.FloatLiteral:
		f64 := math.Float64bits(e.Value)
		return w.node(rawFloatLit, math.Float32bits(float32(e.Value)), 0, 0, 0, uint32(f64), uint32(f64>>32))
	case *ast.Identifier:
		return w.node(rawIdent, w.str(e.Value), 0, 0, 0, 0, 0)
	case *ast.PrefixExpression:
		right := w.expr(e.Right)
		return w.node(rawPrefix, w.str(e.Operator), right, 0, 0, 0, 0)
	case *ast.InfixExpression:
		left := w.expr(e.Left)
		right := w.expr(e.Right)
		return w.node(rawInfix, w.str(e.Operator), left, right, 0, 0, 0)
	case *ast.BlockExpression:
		block := problemNone
		if e.Block != nil {
			block = w.expr(e.Block)
		}
		return w.node(rawBlockExpr, block, 0, 0, 0, 0, 0)
	case *ast.BlockStatement:
		var ids []uint32
		for _, stmt := range e.Statements {
			ids = append(ids, w.expr(stmt))
		}
		return w.node(rawBlock, w.list(ids), uint32(len(ids)), 0, 0, 0, 0)
	case *ast.VariantExpression:
		typeName := problemNone
		if e.TypeName != nil {
			typeName = w.str(e.TypeName.Value)
		}
		payload := w.optional(e.Payload)
		return w.node(rawVariant, typeName, w.str(e.Variant.Value), payload, 0, 0, 0)
	case *ast.MatchExpression:
		scrutinee := w.optional(e.Scrutinee)
		var arms []uint32
		for _, arm := range e.Arms {
			arms = append(arms, w.pattern(arm.Pattern), w.optional(arm.Body))
		}
		return w.node(rawMatch, scrutinee, w.list(arms), uint32(len(e.Arms)), 0, 0, 0)
	case *ast.IndexExpression:
		base := w.expr(e.Left)
		index := w.optional(e.Index)
		dot := uint32(0)
		if e.Dot {
			dot = 1
		}
		return w.node(rawIndex, base, index, dot, 0, 0, 0)
	case *ast.RecordLiteral:
		typeName := problemNone
		if e.TypeName != nil {
			typeName = w.str(e.TypeName.Value)
		}
		var pairs []uint32
		for _, field := range e.FieldOrder {
			pairs = append(pairs, w.str(field.Name), w.expr(field.Value))
		}
		return w.node(rawRecordLit, typeName, w.list(pairs), uint32(len(e.FieldOrder)), 0, 0, 0)
	case *ast.ArrayLiteral:
		typ := problemNone
		if e.Type != nil {
			typ = w.typeExpr(e.Type)
		}
		var ids []uint32
		for _, element := range e.Elements {
			ids = append(ids, w.expr(element))
		}
		return w.node(rawArrayLit, typ, w.list(ids), uint32(len(ids)), 0, 0, 0)
	case *ast.InvocationExpression:
		if ident, isIdent := e.Function.(*ast.Identifier); isIdent {
			if _, known := w.functions[ident.Value]; known {
				if _, seen := w.funcIndex[ident.Value]; !seen {
					w.pending = append(w.pending, ident.Value)
					w.funcIndex[ident.Value] = problemNone // queued: listed once
				}
			}
		}
		function := w.expr(e.Function)
		var args []uint32
		for _, arg := range e.Arguments {
			args = append(args, w.expr(arg))
		}
		return w.node(rawCall, function, w.list(args), uint32(len(args)), 0, 0, 0)
	case *ast.ExpressionStatement:
		return w.node(rawExprStmt, w.optional(e.Expression), 0, 0, 0, 0, 0)
	case *ast.VariableDeclaration:
		typ := problemNone
		if e.Type != nil {
			typ = w.typeExpr(e.Type)
		}
		value := w.optional(e.Value)
		return w.node(rawVarDecl, w.str(e.Name.Value), typ, value, 0, 0, 0)
	case *ast.AssignmentStatement:
		value := w.expr(e.Value)
		return w.node(rawAssign, w.str(e.Name.Value), value, 0, 0, 0, 0)
	case *ast.IndexAssignmentStatement:
		target := w.expr(e.Target)
		value := w.expr(e.Value)
		return w.node(rawIndexAssign, target, value, 0, 0, 0, 0)
	case *ast.WhileStatement:
		cond := w.expr(e.Condition)
		body := problemNone
		if e.Body != nil {
			body = w.expr(e.Body)
		}
		return w.node(rawWhile, cond, body, 0, 0, 0, 0)
	}
	return w.node(rawOther, w.str(fmt.Sprintf("%T", e)), 0, 0, 0, 0, 0)
}

func (w *rawWriter) pattern(p ast.Pattern) uint32 {
	switch p := p.(type) {
	case *ast.VariantPattern:
		typeName := problemNone
		if p.TypeName != nil {
			typeName = w.str(p.TypeName.Value)
		}
		payload := problemNone
		if p.Payload != nil {
			payload = w.pattern(p.Payload)
		}
		return w.node(rawPatVariant, typeName, w.str(p.Variant.Value), payload, 0, 0, 0)
	case *ast.LiteralPattern:
		return w.node(rawPatLiteral, w.optional(p.Value), 0, 0, 0, 0, 0)
	case *ast.WildcardPattern:
		return w.node(rawPatWild, 0, 0, 0, 0, 0, 0)
	case *ast.BindingPattern:
		name := problemNone
		if p.Name != nil {
			name = w.str(p.Name.Value)
		}
		return w.node(rawPatBinding, name, 0, 0, 0, 0, 0)
	}
	return w.node(rawOther, w.str(fmt.Sprintf("%T", p)), 0, 0, 0, 0, 0)
}
