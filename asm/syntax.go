package asm

import (
	"fmt"
	"math"
	"sort"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// The syntax table: a theorem and the functions it calls, serialized for
// the lowering written in Oak (prove/solver/lower.oak), which turns it
// into the decider's terms the way asm/verify.go does. The subset:
// fixed-width integer and Bool scalars, records of them, and fixed arrays,
// as parameters, locals, arguments, and results; integer and Bool
// literals; the prefix operators ! ^ -; the infix arithmetic, bitwise,
// shift, comparison, and Boolean operators, with / and % by an unsigned
// constant power of two; the primitive constructors and the trunc/bits
// conversions; the scalar instruction functions; conditionals in value and
// statement position; typed locals and assignments, field and element
// stores at constant indexes; field and element reads, an element at a
// data-dependent index included; record and array literals; counted while
// loops; calls to program functions, inlined. Everything else — sum
// types, spans, floats, refinements, asserts, recursion — keeps the
// theorem with the Go lowering.
//
// Words: a 16-word header (functions, nodes, list words, largest symbol
// count, theorem function, leaves, types, type leaves, fields, leaf
// indices), the function table (8 words each: parameter start, parameter
// count, result type, body node, symbol count), the parameter table (4
// words each: type, leaf-index start, leaf count), the type table (8
// words each: kind, leaf count, leaf start, field start, field count,
// element type, length), the type leaves (width, signedness), the record
// fields (type, leaf offset), the leaf indices of the theorem's parameter
// leaves in the decider's name order, the nodes (8 words each: kind, a, b,
// c, d, value low, value high, type), and the lists (node ids).

const (
	synIntLit      = 0  // vlo, vhi
	synBoolLit     = 1  // a = 1 or 0
	synSym         = 2  // a = symbol
	synPrefix      = 3  // a = op (0 !, 1 ^, 2 -), b = operand
	synInfix       = 4  // a = op, b = left, c = right
	synCond        = 5  // a = condition, b = then, c = else (value position)
	synCall        = 6  // a = function, b = list start, c = argument count
	synConv        = 7  // a = target width, b = target signedness, c = operand
	synBlock       = 8  // a = list start, b = statement count
	synVarDecl     = 9  // a = symbol, b = type, d = initializer (NONE: the zero)
	synAssign      = 10 // a = symbol, b = value
	synWhile       = 11 // a = condition, b = body block
	synInstr       = 12 // a = operator code, b = member width, c = operand
	synCondStmt    = 13 // a = condition, b = then block, c = else block
	synField       = 14 // a = base, b = field index
	synIndex       = 15 // a = base, b = index node
	synRecordLit   = 16 // a = type, b = list start, c = field count (declaration order)
	synArrayLit    = 17 // a = type, b = list start, c = element count
	synAssignPlace = 18 // a = place (a field/index chain on a symbol), b = value
	synFloatLit    = 19 // a = the f32 bits, vlo/vhi = the f64 bits (the context's width picks)
	synFloatCall   = 20 // a = intrinsic code, b = list start, c = argument count
	synVariantLit  = 21 // a = type, b = variant index, c = payload node (NONE for none)
	synMatch       = 22 // a = scrutinee, b = arms list start, c = arm count (value position)
	synMatchStmt   = 23 // a = scrutinee, b = arms list start, c = arm count (arms are blocks)

	// An arm in the lists: pattern kind, variant index or literal node,
	// binding symbol (NONE for none), body node.
	synArmWords   = 4
	synPatVariant = 0
	synPatLiteral = 1
	synPatWild    = 2
	synPatBinding = 3
)

// The float intrinsics the lowering knows as bit operations
// (asm/floats_lowering.go).
var synFloatIntrinsics = map[string]uint32{
	"abs": 0, "copysign": 1, "is_nan": 2, "is_finite": 3, "is_infinite": 4, "is_normal": 5, "total_order": 6, "min": 7, "max": 8,
}

const (
	synKindScalar = 0
	synKindRecord = 1
	synKindArray  = 2
	synKindSum    = 3
)

// synVariantRef is a sum type's variant: its tag value, payload type (-1
// for none), and the payload's leaf offset in the value.
type synVariantRef struct {
	name   string
	tag    int
	typ    int
	offset int
}

var synInfixOps = map[string]uint32{
	"+": 0, "-": 1, "*": 2, "&": 3, "|": 4, "^": 5, "<<": 6, ">>": 7, "/": 8, "%": 9,
	"==": 10, "!=": 11, "<": 12, "<=": 13, ">": 14, ">=": 15, "&&": 16, "||": 17,
}

var synInstrOps = map[string]uint32{"rev": 10, "rev16": 11, "rev32": 12, "rbit": 13, "clz": 14, "cnt": 15, "cls": 16}

type synLeaf struct {
	width  int
	signed bool
	name   string // the leaf's path suffix, for the decider's parameter names
}

type synFieldRef struct {
	typ    int
	offset int // in leaves
	name   string
}

type synType struct {
	kind     int
	width    int
	signed   bool
	float    bool
	leaves   []synLeaf
	fields   []synFieldRef
	variants []synVariantRef
	elem     int
	length   int
	key      string
}

type synFunction struct {
	sig      *ast.FunctionStatement
	index    int
	symbols  map[string]int
	symTypes []int
	params   []int // parameter types
	ret      int
	body     uint32
}

type syntaxWriter struct {
	lo        *oakLowering
	functions map[string]*ast.FunctionStatement
	order     []*synFunction
	byName    map[string]*synFunction
	types     []*synType
	typeIndex map[string]int
	nodes     []uint32
	lists     []uint32
	maxSyms   int
	leafIdx   []uint32 // the theorem parameters' leaf indices, per parameter in order
	leafSpans [][2]int // per theorem parameter: start and count in leafIdx
	leaves    int
	leafNames []string // the theorem's leaves in the decider's name order
}

// ExportSyntax serializes the theorem and its callees for the Oak
// lowering, or says which construct keeps it with the Go lowering.
func ExportSyntax(sig *ast.FunctionStatement, functions map[string]*ast.FunctionStatement, decls Declarations) ([]uint32, []string, string, bool) {
	if sig == nil || sig.Name == nil || sig.Body == nil {
		return nil, nil, "no body", false
	}
	lo := newLowering(sig)
	lo.functions = functions
	lo.records, lo.adts = decls.Records, decls.ADTs
	w := &syntaxWriter{lo: lo, functions: functions, byName: map[string]*synFunction{}, typeIndex: map[string]int{}}
	theorem, reason, ok := w.function(sig, true)
	if !ok {
		return nil, nil, reason, false
	}
	var funcs, params, types, typeLeaves, fields, variants []uint32
	for _, f := range w.order {
		funcs = append(funcs, uint32(len(params)/4), uint32(len(f.params)), uint32(f.ret), f.body, uint32(len(f.symbols)), 0, 0, 0)
		for i, t := range f.params {
			start, count := problemNone, uint32(0)
			if f == theorem {
				start, count = uint32(w.leafSpans[i][0]), uint32(w.leafSpans[i][1])
			}
			params = append(params, uint32(t), start, count, 0)
		}
	}
	for _, t := range w.types {
		isFloat := uint32(0)
		if t.float {
			isFloat = 1
		}
		fieldStart, fieldCount := uint32(len(fields)/2), uint32(len(t.fields))
		if t.kind == synKindSum {
			// A sum type's field words index the variants table instead.
			fieldStart, fieldCount = uint32(len(variants)/3), uint32(len(t.variants))
		}
		types = append(types, uint32(t.kind), uint32(len(t.leaves)), uint32(len(typeLeaves)/2), fieldStart, fieldCount, uint32(t.elem), uint32(t.length), isFloat)
		for _, leaf := range t.leaves {
			s := uint32(0)
			if leaf.signed {
				s = 1
			}
			typeLeaves = append(typeLeaves, uint32(leaf.width), s)
		}
		for _, field := range t.fields {
			fields = append(fields, uint32(field.typ), uint32(field.offset))
		}
		for _, v := range t.variants {
			payload := problemNone
			if v.typ >= 0 {
				payload = uint32(v.typ)
			}
			variants = append(variants, uint32(v.tag), payload, uint32(v.offset))
		}
	}
	header := []uint32{uint32(len(w.order)), uint32(len(w.nodes) / 8), uint32(len(w.lists)), uint32(w.maxSyms), uint32(theorem.index), uint32(w.leaves), uint32(len(w.types)), uint32(len(typeLeaves) / 2), uint32(len(fields) / 2), uint32(len(w.leafIdx)), uint32(len(variants) / 3), 0, 0, 0, 0, 0}
	words := make([]uint32, 0, len(header)+len(funcs)+len(params)+len(types)+len(typeLeaves)+len(fields)+len(variants)+len(w.leafIdx)+len(w.nodes)+len(w.lists))
	words = append(words, header...)
	words = append(words, funcs...)
	words = append(words, params...)
	words = append(words, types...)
	words = append(words, typeLeaves...)
	words = append(words, fields...)
	words = append(words, variants...)
	words = append(words, w.leafIdx...)
	words = append(words, w.nodes...)
	words = append(words, w.lists...)
	return words, w.leafNames, "", true
}

// typeID interns a type of the subset: scalars by width and signedness,
// arrays by element and length, records by name (their fields interned
// in declaration order).
func (w *syntaxWriter) typeID(typ *oakType) (int, string, bool) {
	var key string
	switch typ.kind {
	case oakScalar:
		key = fmt.Sprintf("s%d:%v:%v", typ.width, typ.signed, typ.float)
	case oakArray:
		elem, reason, ok := w.typeID(typ.elem)
		if !ok {
			return 0, reason, false
		}
		key = fmt.Sprintf("a%d:%d", elem, typ.length)
	case oakRecord:
		key = "r:" + typ.name
	case oakADT:
		key = "u:" + typ.name
	default:
		return 0, fmt.Sprintf("the type %s", typ.name), false
	}
	if id, seen := w.typeIndex[key]; seen {
		return id, "", true
	}
	t := &synType{key: key}
	id := len(w.types)
	w.types = append(w.types, t)
	w.typeIndex[key] = id
	switch typ.kind {
	case oakScalar:
		t.kind, t.width, t.signed, t.float = synKindScalar, typ.width, typ.signed, typ.float
		t.leaves = []synLeaf{{width: typ.width, signed: typ.signed}}
	case oakArray:
		elem, _, _ := w.typeID(typ.elem)
		t.kind, t.elem, t.length = synKindArray, elem, int(typ.length)
		for k := 0; k < t.length; k++ {
			for _, leaf := range w.types[elem].leaves {
				t.leaves = append(t.leaves, synLeaf{width: leaf.width, signed: leaf.signed, name: fmt.Sprintf("[%d]%s", k, leaf.name)})
			}
		}
	case oakRecord:
		t.kind = synKindRecord
		for _, f := range typ.fields {
			ft, reason, ok := w.typeID(f.typ)
			if !ok {
				return 0, reason, false
			}
			t.fields = append(t.fields, synFieldRef{typ: ft, offset: len(t.leaves), name: f.name})
			for _, leaf := range w.types[ft].leaves {
				t.leaves = append(t.leaves, synLeaf{width: leaf.width, signed: leaf.signed, name: "." + f.name + leaf.name})
			}
		}
	case oakADT:
		// The tag (32 bits, as the decider carries it) then every
		// variant's payload, in variant order.
		t.kind = synKindSum
		t.leaves = append(t.leaves, synLeaf{width: 32, name: ".tag"})
		for _, v := range typ.variants {
			ref := synVariantRef{name: v.name, tag: int(v.tag), typ: -1, offset: len(t.leaves)}
			if v.payload != nil {
				pt, reason, ok := w.typeID(v.payload)
				if !ok {
					return 0, reason, false
				}
				ref.typ = pt
				for _, leaf := range w.types[pt].leaves {
					t.leaves = append(t.leaves, synLeaf{width: leaf.width, signed: leaf.signed, name: "." + v.name + leaf.name})
				}
			}
			t.variants = append(t.variants, ref)
		}
	}
	return id, "", true
}

// variantIndex finds a variant of a sum type by name.
func (w *syntaxWriter) variantIndex(typ int, name string) (int, bool) {
	for i, v := range w.types[typ].variants {
		if v.name == name {
			return i, true
		}
	}
	return 0, false
}

// typeOfExpr resolves a type expression of the subset.
func (w *syntaxWriter) typeOfExpr(expr ast.Expression) (int, string, bool) {
	typ, ok := w.lo.oakTypeOf(expr)
	if !ok {
		return 0, fmt.Sprintf("the type %s", typeText(expr)), false
	}
	switch typeText(expr) {
	case "f32", "f64":
		// A float is its IEEE bit pattern: a scalar with the float flag.
		typ = &oakType{kind: oakScalar, width: typ.width, float: true}
	case "f16", "bf16", "f8":
		return 0, "a narrow float type", false
	}
	return w.typeID(typ)
}

func (w *syntaxWriter) scalarType(width int, signed bool) int {
	id, _, _ := w.typeID(&oakType{kind: oakScalar, width: width, signed: signed})
	return id
}

// isFloatNode reports a node of a float type (a float literal has none of
// its own but is a float).
func (w *syntaxWriter) isFloatNode(id uint32) bool {
	if w.nodes[id*8] == synFloatLit {
		return true
	}
	t := w.nodeType(id)
	return t >= 0 && w.types[t].float
}

func (w *syntaxWriter) function(sig *ast.FunctionStatement, theorem bool) (*synFunction, string, bool) {
	name := sig.Name.Value
	if f, seen := w.byName[name]; seen {
		if f.body == problemNone {
			return nil, fmt.Sprintf("a recursive call to %s", name), false
		}
		return f, "", true
	}
	if sig.Receiver != nil || len(sig.TypeParams) != 0 || sig.Body == nil || sig.ExternSymbol != "" {
		return nil, fmt.Sprintf("a call to %s (a method, generic, foreign, or definition-less function)", name), false
	}
	f := &synFunction{sig: sig, index: len(w.order), symbols: map[string]int{}, body: problemNone}
	w.order = append(w.order, f)
	w.byName[name] = f
	if theorem {
		f.ret = w.scalarType(1, false)
	} else {
		ret, reason, ok := w.typeOfExpr(sig.ReturnType)
		if !ok {
			return nil, fmt.Sprintf("a call to %s returning %s", name, reason), false
		}
		f.ret = ret
	}
	type leafName struct {
		name  string
		param int
		leaf  int
	}
	var leafNames []leafName
	for i, param := range sig.Parameters {
		if param.Variadic {
			return nil, fmt.Sprintf("parameter %s is variadic", param.Name.Value), false
		}
		t, reason, ok := w.typeOfExpr(param.Type)
		if !ok {
			return nil, fmt.Sprintf("parameter %s: %s", param.Name.Value, reason), false
		}
		f.symbols[param.Name.Value] = len(f.params)
		f.symTypes = append(f.symTypes, t)
		f.params = append(f.params, t)
		if theorem {
			for k, leaf := range w.types[t].leaves {
				leafNames = append(leafNames, leafName{name: param.Name.Value + leaf.name, param: i, leaf: k})
			}
		}
	}
	if theorem {
		// The leaves are the decider's parameters in name order (its
		// interleaved variable order sorts the parameter names).
		sort.Slice(leafNames, func(a, b int) bool { return leafNames[a].name < leafNames[b].name })
		position := map[[2]int]int{}
		for idx, ln := range leafNames {
			position[[2]int{ln.param, ln.leaf}] = idx
			w.leafNames = append(w.leafNames, ln.name)
		}
		for i, t := range f.params {
			start := len(w.leafIdx)
			for k := range w.types[t].leaves {
				w.leafIdx = append(w.leafIdx, uint32(position[[2]int{i, k}]))
			}
			w.leafSpans = append(w.leafSpans, [2]int{start, len(w.types[t].leaves)})
		}
		w.leaves = len(leafNames)
	}
	body, reason, ok := w.expr(f, sig.Body)
	if !ok {
		if theorem {
			return nil, reason, false
		}
		return nil, fmt.Sprintf("a call to %s whose body contains %s", name, reason), false
	}
	f.body = body
	if len(f.symbols) > w.maxSyms {
		w.maxSyms = len(f.symbols)
	}
	return f, "", true
}

func (w *syntaxWriter) node(kind, a, b, c, d, vlo, vhi uint32, typ int) uint32 {
	id := uint32(len(w.nodes) / 8)
	t := problemNone
	if typ >= 0 {
		t = uint32(typ)
	}
	w.nodes = append(w.nodes, kind, a, b, c, d, vlo, vhi, t)
	return id
}

func (w *syntaxWriter) nodeType(id uint32) int {
	t := w.nodes[id*8+7]
	if t == problemNone {
		return -1
	}
	return int(t)
}

func (w *syntaxWriter) list(ids []uint32) uint32 {
	start := uint32(len(w.lists))
	w.lists = append(w.lists, ids...)
	return start
}

// expr serializes an expression, failing closed outside the subset. The
// node carries its static type when the subset determines one (a bare
// literal takes the context's).
func (w *syntaxWriter) expr(f *synFunction, e ast.Expression) (uint32, string, bool) {
	switch e := e.(type) {
	case *ast.IntegerLiteral:
		v := uint64(e.Value)
		return w.node(synIntLit, 0, 0, 0, 0, uint32(v), uint32(v>>32), -1), "", true
	case *ast.Boolean:
		bit := uint32(0)
		if e.Value {
			bit = 1
		}
		return w.node(synBoolLit, bit, 0, 0, 0, 0, 0, w.scalarType(1, false)), "", true
	case *ast.FloatLiteral:
		f64 := math.Float64bits(e.Value)
		return w.node(synFloatLit, uint32(math.Float32bits(float32(e.Value))), 0, 0, 0, uint32(f64), uint32(f64>>32), -1), "", true
	case *ast.Identifier:
		sym, known := f.symbols[e.Value]
		if !known {
			return 0, fmt.Sprintf("identifier %s (not a parameter or local)", e.Value), false
		}
		return w.node(synSym, uint32(sym), 0, 0, 0, 0, 0, f.symTypes[sym]), "", true
	case *ast.PrefixExpression:
		op := map[string]uint32{"!": 0, "^": 1, "-": 2}
		code, known := op[e.Operator]
		if !known {
			return 0, fmt.Sprintf("prefix operator %s", e.Operator), false
		}
		operand, reason, ok := w.expr(f, e.Right)
		if !ok {
			return 0, reason, false
		}
		typ := w.nodeType(operand)
		if code == 0 {
			typ = w.scalarType(1, false)
		}
		return w.node(synPrefix, code, operand, 0, 0, 0, 0, typ), "", true
	case *ast.InfixExpression:
		code, known := synInfixOps[e.Operator]
		if !known {
			return 0, fmt.Sprintf("operator %s", e.Operator), false
		}
		left, reason, ok := w.expr(f, e.Left)
		if !ok {
			return 0, reason, false
		}
		right, reason, ok := w.expr(f, e.Right)
		if !ok {
			return 0, reason, false
		}
		typ := w.nodeType(left)
		if typ < 0 {
			typ = w.nodeType(right)
		}
		if (w.isFloatNode(left) || w.isFloatNode(right)) && code < 10 {
			return 0, fmt.Sprintf("floating-point %s (not a bit operation)", e.Operator), false
		}
		if code >= 10 {
			typ = w.scalarType(1, false)
		}
		return w.node(synInfix, code, left, right, 0, 0, 0, typ), "", true
	case *ast.BlockExpression:
		return w.block(f, e.Block, true)
	case *ast.VariantExpression:
		if e.TypeName == nil {
			return 0, "a variant without its type name", false
		}
		t, reason, ok := w.typeOfExpr(e.TypeName)
		if !ok {
			return 0, reason, false
		}
		if w.types[t].kind != synKindSum {
			return 0, fmt.Sprintf("a variant of %s (not a sum type)", e.TypeName.Value), false
		}
		vi, known := w.variantIndex(t, e.Variant.Value)
		if !known {
			return 0, fmt.Sprintf("the variant %s of %s", e.Variant.Value, e.TypeName.Value), false
		}
		v := w.types[t].variants[vi]
		if (e.Payload == nil) != (v.typ < 0) {
			return 0, fmt.Sprintf("the variant %s.%s with the wrong payload shape", e.TypeName.Value, e.Variant.Value), false
		}
		payload := problemNone
		if e.Payload != nil {
			id, reason, ok := w.expr(f, e.Payload)
			if !ok {
				return 0, reason, false
			}
			payload = id
		}
		return w.node(synVariantLit, uint32(t), uint32(vi), payload, 0, 0, 0, t), "", true
	case *ast.MatchExpression:
		whenTrue, whenFalse, isBool := boolConditional(e)
		if !isBool {
			return w.match(f, e, true)
		}
		cond, reason, ok := w.expr(f, e.Scrutinee)
		if !ok {
			return 0, reason, false
		}
		then, reason, ok := w.expr(f, whenTrue)
		if !ok {
			return 0, reason, false
		}
		otherwise, reason, ok := w.expr(f, whenFalse)
		if !ok {
			return 0, reason, false
		}
		typ := w.nodeType(then)
		if typ < 0 {
			typ = w.nodeType(otherwise)
		}
		return w.node(synCond, cond, then, otherwise, 0, 0, 0, typ), "", true
	case *ast.IndexExpression:
		base, reason, ok := w.expr(f, e.Left)
		if !ok {
			return 0, reason, false
		}
		bt := w.nodeType(base)
		if bt < 0 {
			return 0, fmt.Sprintf("an access on %s, whose type is not known", e.Left.String()), false
		}
		if e.Dot {
			name, isName := e.Index.(*ast.Identifier)
			if !isName || w.types[bt].kind != synKindRecord {
				return 0, fmt.Sprintf("the field access %s", e.String()), false
			}
			for k, field := range w.types[bt].fields {
				if field.name == name.Value {
					return w.node(synField, base, uint32(k), 0, 0, 0, 0, field.typ), "", true
				}
			}
			return 0, fmt.Sprintf("the field %s", name.Value), false
		}
		if w.types[bt].kind != synKindArray {
			return 0, fmt.Sprintf("an index into %s (not an array)", e.Left.String()), false
		}
		index, reason, ok := w.expr(f, e.Index)
		if !ok {
			return 0, reason, false
		}
		return w.node(synIndex, base, index, 0, 0, 0, 0, w.types[bt].elem), "", true
	case *ast.RecordLiteral:
		if e.TypeName == nil {
			return 0, "a record literal without a type name", false
		}
		t, reason, ok := w.typeOfExpr(e.TypeName)
		if !ok {
			return 0, reason, false
		}
		var values []uint32
		for _, field := range w.types[t].fields {
			value, given := e.Fields[field.name]
			if !given {
				return 0, fmt.Sprintf("a %s literal without the field %s", e.TypeName.Value, field.name), false
			}
			id, reason, ok := w.expr(f, value)
			if !ok {
				return 0, reason, false
			}
			values = append(values, id)
		}
		return w.node(synRecordLit, uint32(t), w.list(values), uint32(len(values)), 0, 0, 0, t), "", true
	case *ast.ArrayLiteral:
		if e.Type == nil {
			return 0, "an array literal without a type", false
		}
		t, reason, ok := w.typeOfExpr(e.Type)
		if !ok {
			return 0, reason, false
		}
		if w.types[t].kind != synKindArray || len(e.Elements) != w.types[t].length {
			return 0, "an array literal of the wrong shape", false
		}
		var values []uint32
		for _, element := range e.Elements {
			id, reason, ok := w.expr(f, element)
			if !ok {
				return 0, reason, false
			}
			values = append(values, id)
		}
		return w.node(synArrayLit, uint32(t), w.list(values), uint32(len(values)), 0, 0, 0, t), "", true
	case *ast.InvocationExpression:
		if member, width, isInstruction := instructionFunction(e); isInstruction {
			code, known := synInstrOps[member]
			if !known || len(e.Arguments) != 1 {
				return 0, fmt.Sprintf("the instruction function %s", member), false
			}
			operand, reason, ok := w.expr(f, e.Arguments[0])
			if !ok {
				return 0, reason, false
			}
			return w.node(synInstr, code, uint32(width), operand, 0, 0, 0, w.scalarType(width, false)), "", true
		}
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return 0, "a call through a value", false
		}
		if callee, known := w.functions[ident.Value]; known {
			cf, reason, ok := w.function(callee, false)
			if !ok {
				return 0, reason, false
			}
			if len(e.Arguments) != len(cf.params) {
				return 0, fmt.Sprintf("a call to %s with %d arguments", ident.Value, len(e.Arguments)), false
			}
			var args []uint32
			for _, arg := range e.Arguments {
				id, reason, ok := w.expr(f, arg)
				if !ok {
					return 0, reason, false
				}
				args = append(args, id)
			}
			return w.node(synCall, uint32(cf.index), w.list(args), uint32(len(args)), 0, 0, 0, cf.ret), "", true
		}
		if code, isFloatIntrinsic := synFloatIntrinsics[ident.Value]; isFloatIntrinsic && typechecker.FloatIntrinsicName(ident.Value) {
			var args []uint32
			floatType := -1
			for _, arg := range e.Arguments {
				id, reason, ok := w.expr(f, arg)
				if !ok {
					return 0, reason, false
				}
				args = append(args, id)
				if t := w.nodeType(id); floatType < 0 && t >= 0 && w.types[t].float {
					floatType = t
				}
			}
			if (code <= 1 || code >= 7) && len(args) != map[uint32]int{0: 1, 1: 2, 7: 2, 8: 2}[code] {
				return 0, fmt.Sprintf("the float intrinsic %s with %d arguments", ident.Value, len(args)), false
			}
			if code >= 2 && code <= 5 && len(args) != 1 || code == 6 && len(args) != 2 {
				return 0, fmt.Sprintf("the float intrinsic %s with %d arguments", ident.Value, len(args)), false
			}
			typ := floatType
			if code >= 2 && code <= 6 {
				typ = w.scalarType(1, false)
			}
			return w.node(synFloatCall, code, w.list(args), uint32(len(args)), 0, 0, 0, typ), "", true
		}
		if typechecker.FloatIntrinsicName(ident.Value) {
			return 0, fmt.Sprintf("the float intrinsic %s (not a bit operation)", ident.Value), false
		}
		if len(e.Arguments) != 1 {
			return 0, fmt.Sprintf("call to %s", ident.Value), false
		}
		target := ""
		switch ident.Value {
		case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64":
			target = ident.Value
		default:
			if t, op, _, isConv := typechecker.ConversionParts(ident.Value); isConv && (op == "trunc" || op == "bits") {
				target = t
			}
		}
		if target == "" {
			return 0, fmt.Sprintf("call to %s", ident.Value), false
		}
		width, signed, _ := contractBits(&ast.Identifier{Value: target})
		operand, reason, ok := w.expr(f, e.Arguments[0])
		if !ok {
			return 0, reason, false
		}
		signedWord := uint32(0)
		if signed {
			signedWord = 1
		}
		resultType := w.scalarType(width, signed)
		if target == "f32" || target == "f64" {
			// A bits row into a float: the pattern, typed float.
			resultType, _, _ = w.typeID(&oakType{kind: oakScalar, width: width, float: true})
		}
		return w.node(synConv, uint32(width), signedWord, operand, 0, 0, 0, resultType), "", true
	}
	return 0, fmt.Sprintf("%T", e), false
}

// block serializes a block: statements, the last an expression (the
// result) in value position; in statement position (a loop body, a
// conditional's arm) every statement is a statement, a conditional among
// them a statement conditional.
func (w *syntaxWriter) block(f *synFunction, block *ast.BlockStatement, value bool) (uint32, string, bool) {
	if block == nil {
		return w.node(synBlock, 0, 0, 0, 0, 0, 0, -1), "", true
	}
	var ids []uint32
	resultType := -1
	for i, stmt := range block.Statements {
		last := i == len(block.Statements)-1
		switch s := stmt.(type) {
		case *ast.ExpressionStatement:
			if match, isMatch := s.Expression.(*ast.MatchExpression); isMatch && (!last || !value) {
				var id uint32
				var reason string
				var ok bool
				if _, _, isBool := boolConditional(match); isBool {
					id, reason, ok = w.condStmt(f, match)
				} else {
					id, reason, ok = w.match(f, match, false)
				}
				if !ok {
					return 0, reason, false
				}
				ids = append(ids, id)
				continue
			}
			if !last || !value {
				return 0, "an expression statement before the end of a block", false
			}
			id, reason, ok := w.expr(f, s.Expression)
			if !ok {
				return 0, reason, false
			}
			ids = append(ids, id)
			resultType = w.nodeType(id)
		case *ast.VariableDeclaration:
			if s.Type == nil {
				return 0, "a local without a type", false
			}
			t, reason, ok := w.typeOfExpr(s.Type)
			if !ok {
				return 0, fmt.Sprintf("a local of %s", reason), false
			}
			init := problemNone
			if s.Value == nil {
				// The Go lowering zero-fills a value-less array only.
				if w.types[t].kind != synKindArray {
					return 0, fmt.Sprintf("the local %s without an initializer", s.Name.Value), false
				}
			} else {
				id, reason, ok := w.expr(f, s.Value)
				if !ok {
					return 0, reason, false
				}
				init = id
			}
			sym, seen := f.symbols[s.Name.Value]
			if !seen {
				sym = len(f.symbols)
				f.symbols[s.Name.Value] = sym
				f.symTypes = append(f.symTypes, t)
			}
			ids = append(ids, w.node(synVarDecl, uint32(sym), uint32(t), 0, init, 0, 0, -1))
		case *ast.AssignmentStatement:
			sym, known := f.symbols[s.Name.Value]
			if !known {
				return 0, fmt.Sprintf("an assignment to %s (not a local)", s.Name.Value), false
			}
			value, reason, ok := w.expr(f, s.Value)
			if !ok {
				return 0, reason, false
			}
			ids = append(ids, w.node(synAssign, uint32(sym), value, 0, 0, 0, 0, -1))
		case *ast.IndexAssignmentStatement:
			place, reason, ok := w.expr(f, s.Target)
			if !ok {
				return 0, reason, false
			}
			value, reason, ok := w.expr(f, s.Value)
			if !ok {
				return 0, reason, false
			}
			ids = append(ids, w.node(synAssignPlace, place, value, 0, 0, 0, 0, -1))
		case *ast.WhileStatement:
			cond, reason, ok := w.expr(f, s.Condition)
			if !ok {
				return 0, reason, false
			}
			body, reason, ok := w.block(f, s.Body, false)
			if !ok {
				return 0, reason, false
			}
			ids = append(ids, w.node(synWhile, cond, body, 0, 0, 0, 0, -1))
		default:
			return 0, fmt.Sprintf("%T", stmt), false
		}
	}
	return w.node(synBlock, w.list(ids), uint32(len(ids)), 0, 0, 0, 0, resultType), "", true
}

// match serializes a match over a sum type or a scalar: the arms with
// their patterns (a variant with an optional payload binding or wildcard,
// a literal, a wildcard, a binding of the whole value) and bodies, in
// value position expressions, in statement position blocks.
func (w *syntaxWriter) match(f *synFunction, e *ast.MatchExpression, value bool) (uint32, string, bool) {
	scrutinee, reason, ok := w.expr(f, e.Scrutinee)
	if !ok {
		return 0, reason, false
	}
	st := w.nodeType(scrutinee)
	if st < 0 {
		return 0, "a match scrutinee whose type is not known", false
	}
	isSum := w.types[st].kind == synKindSum
	var arms []uint32
	resultType := -1
	bind := func(name *ast.Identifier, typ int) uint32 {
		if name == nil || name.Value == "_" {
			return problemNone
		}
		sym, seen := f.symbols[name.Value]
		if !seen {
			sym = len(f.symbols)
			f.symbols[name.Value] = sym
			f.symTypes = append(f.symTypes, typ)
		} else {
			f.symTypes[sym] = typ
		}
		return uint32(sym)
	}
	for _, arm := range e.Arms {
		kind, operand, binding := uint32(synPatWild), problemNone, problemNone
		switch pattern := arm.Pattern.(type) {
		case *ast.VariantPattern:
			if !isSum {
				return 0, "a variant pattern over a scalar", false
			}
			vi, known := w.variantIndex(st, pattern.Variant.Value)
			if !known {
				return 0, fmt.Sprintf("the variant %s in a pattern", pattern.Variant.Value), false
			}
			kind, operand = synPatVariant, uint32(vi)
			v := w.types[st].variants[vi]
			switch payload := pattern.Payload.(type) {
			case nil:
			case *ast.WildcardPattern:
			case *ast.BindingPattern:
				if payload.Name != nil && payload.Name.Value != "_" {
					if v.typ < 0 {
						return 0, "a binding on a bare variant", false
					}
					binding = bind(payload.Name, v.typ)
				}
			default:
				return 0, fmt.Sprintf("the payload pattern %s", pattern.Payload.String()), false
			}
		case *ast.LiteralPattern:
			if isSum {
				return 0, "a literal pattern over a sum type", false
			}
			id, reason, ok := w.expr(f, pattern.Value)
			if !ok {
				return 0, reason, false
			}
			kind, operand = synPatLiteral, id
		case *ast.WildcardPattern:
		case *ast.BindingPattern:
			if pattern.Name != nil && pattern.Name.Value != "_" {
				if !isSum {
					return 0, "a binding pattern over a scalar", false
				}
				kind, binding = synPatBinding, bind(pattern.Name, st)
			}
		default:
			return 0, fmt.Sprintf("the pattern %s", arm.Pattern.String()), false
		}
		var body uint32
		if value {
			body, reason, ok = w.expr(f, arm.Body)
		} else {
			block, isBlock := arm.Body.(*ast.BlockExpression)
			if !isBlock {
				return 0, "a match arm in statement position that is not a block", false
			}
			body, reason, ok = w.block(f, block.Block, false)
		}
		if !ok {
			return 0, reason, false
		}
		if value && resultType < 0 {
			resultType = w.nodeType(body)
		}
		arms = append(arms, kind, operand, binding, body)
	}
	if len(arms) == 0 {
		return 0, "a match without arms", false
	}
	kind := uint32(synMatch)
	if !value {
		kind = synMatchStmt
		resultType = -1
	}
	return w.node(kind, scrutinee, w.list(arms), uint32(len(arms)/synArmWords), 0, 0, 0, resultType), "", true
}

// condStmt serializes `c ? { ... } | { ... }` in statement position: the
// arms are blocks of statements.
func (w *syntaxWriter) condStmt(f *synFunction, match *ast.MatchExpression) (uint32, string, bool) {
	whenTrue, whenFalse, isBool := boolConditional(match)
	if !isBool {
		return 0, "a match statement that is not a Bool conditional", false
	}
	cond, reason, ok := w.expr(f, match.Scrutinee)
	if !ok {
		return 0, reason, false
	}
	arm := func(e ast.Expression) (uint32, string, bool) {
		block, isBlock := e.(*ast.BlockExpression)
		if !isBlock {
			return 0, "a conditional arm in statement position that is not a block", false
		}
		return w.block(f, block.Block, false)
	}
	then, reason, ok := arm(whenTrue)
	if !ok {
		return 0, reason, false
	}
	otherwise, reason, ok := arm(whenFalse)
	if !ok {
		return 0, reason, false
	}
	return w.node(synCondStmt, cond, then, otherwise, 0, 0, 0, -1), "", true
}
