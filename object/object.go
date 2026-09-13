package object

import (
	"bytes"
	"fmt"
	"github.com/SCKelemen/oak/token"
	"math/big"
	"strconv"
	"sync"
	"sync/atomic"

	"github.com/SCKelemen/oak/ast"
)

type Integer struct {
	Value int64
}

func (i *Integer) Inspect() string {
	return fmt.Sprintf("%d", i.Value)
}
func (i *Integer) Kind() ObjectKind { return INTEGER }
func (i *Integer) Type() ObjectType { return INTEGER_OBJ }

// U128 is a value of the 128-bit unsigned integer type (docs/spec/20-types.md
// section 11): the two 64-bit halves of its bit pattern. It is a distinct
// object from Integer so that a path not taught the width fails on the
// type rather than reading a truncated Value.
type U128 struct {
	Hi, Lo uint64
}

func (u *U128) Inspect() string    { return u.Big().String() }
func (u *U128) Kind() ObjectKind   { return WIDE }
func (u *U128) Type() ObjectType   { return U128_OBJ }
func (u *U128) IsZero() bool       { return u.Hi == 0 && u.Lo == 0 }
func (u *U128) Equal(o *U128) bool { return u.Hi == o.Hi && u.Lo == o.Lo }

// Less is the unsigned ordering of two 128-bit values.
func (u *U128) Less(o *U128) bool { return u.Hi < o.Hi || (u.Hi == o.Hi && u.Lo < o.Lo) }

// Big is the mathematical value in [0, 2^128).
func (u *U128) Big() *big.Int {
	v := new(big.Int).SetUint64(u.Hi)
	v.Lsh(v, 64)
	return v.Or(v, new(big.Int).SetUint64(u.Lo))
}

var u128Mask = new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 128), big.NewInt(1))

// U128FromBig folds a mathematical value into the width: the low 128 bits
// of its two's-complement pattern, which is the wrapping the operators
// specify.
func U128FromBig(v *big.Int) *U128 {
	w := new(big.Int).And(v, u128Mask)
	lo := new(big.Int).And(w, new(big.Int).SetUint64(^uint64(0))).Uint64()
	hi := new(big.Int).Rsh(w, 64).Uint64()
	return &U128{Hi: hi, Lo: lo}
}

type Boolean struct {
	Value bool
}

func (b *Boolean) Kind() ObjectKind { return BOOLEAN }
func (b *Boolean) Type() ObjectType { return BOOLEAN_OBJ }
func (b *Boolean) Inspect() string {
	return fmt.Sprintf("%t", b.Value)
}

type Null struct{}

func (n *Null) Kind() ObjectKind { return NULL }
func (n *Null) Type() ObjectType { return NULL_OBJ }
func (n *Null) Inspect() string  { return "null" }

type String struct {
	Value string
}

func (s *String) Kind() ObjectKind { return STRING }
func (s *String) Type() ObjectType { return STRING_OBJ }
func (s *String) Inspect() string  { return s.Value }

type Function struct {
	Parameters []*ast.Identifier
	Body       *ast.BlockStatement
	Env        *Environment
	// Variadic marks a Go-style trailing parameter: calls bundle the
	// trailing arguments into an Array bound to the last parameter name.
	Variadic bool
	// Dispatch carries the declaration's processor-feature realizations
	// (docs/spec/93-simd.md section 6); the interpreter selects one when
	// its feature set names the slot's feature, else runs Body.
	Dispatch []*ast.DispatchSlot
}

func (f *Function) Kind() ObjectKind { return FUNCTION }
func (f *Function) Type() ObjectType { return FUNCTION_OBJ }
func (f *Function) Inspect() string {
	return "fn(...) { ... }"
}

// BuiltinFunction is a function signature for built-in functions
// FieldAccessor is the runtime form of .field and captures no environment.
type FieldAccessor struct{ Field string }

func (f *FieldAccessor) Kind() ObjectKind { return FUNCTION }
func (f *FieldAccessor) Type() ObjectType { return FUNCTION_OBJ }
func (f *FieldAccessor) Inspect() string  { return "." + f.Field }

type BuiltinFunction func(args ...Object) Object

// Builtin represents a built-in function
type Builtin struct {
	Fn BuiltinFunction
}

func (b *Builtin) Kind() ObjectKind { return FUNCTION }
func (b *Builtin) Type() ObjectType { return FUNCTION_OBJ }
func (b *Builtin) Inspect() string  { return "builtin function" }

type ADTValue struct {
	TypeName string
	Variant  string
	Value    Object // optional payload
}

func (a *ADTValue) Kind() ObjectKind { return ADT }
func (a *ADTValue) Type() ObjectType { return ADT_OBJ }
func (a *ADTValue) Inspect() string {
	if a.Value != nil {
		return a.TypeName + "." + a.Variant + "(" + a.Value.Inspect() + ")"
	}
	return a.TypeName + "." + a.Variant
}

type ReturnValue struct {
	Value Object
}

func (rv *ReturnValue) Type() ObjectType { return RETURN_VALUE_OBJ }
func (rv *ReturnValue) Inspect() string  { return rv.Value.Inspect() }
func (rv *ReturnValue) Kind() ObjectKind { return RETURN_VALUE }

// BreakSignal is the control-flow value a `break` statement evaluates to:
// blocks return it upward until the enclosing while consumes it.
type BreakSignal struct{}

func (b *BreakSignal) Type() ObjectType { return BREAK_OBJ }
func (b *BreakSignal) Inspect() string  { return "break" }
func (b *BreakSignal) Kind() ObjectKind { return BREAK }

type Error struct {
	Message string
}

func (e *Error) Type() ObjectType { return ERROR_OBJ }
func (e *Error) Inspect() string  { return "ERROR: " + e.Message }
func (e *Error) Kind() ObjectKind { return ERROR }

// Record: { field1: value1, field2: value2, ... }
type Record struct {
	Fields map[string]Object
	// Order is the declared field order, when the record was built from a
	// declaration or a literal that has one: the order a scalar view of
	// the record reads its fields in (view_as).
	Order []string
}

func (r *Record) Type() ObjectType { return RECORD_OBJ }
func (r *Record) Kind() ObjectKind { return RECORD }
func (r *Record) Inspect() string {
	var out bytes.Buffer
	out.WriteRune('{')

	first := true
	for field, value := range r.Fields {
		if !first {
			out.WriteString(", ")
		}
		out.WriteString(field)
		out.WriteString(": ")
		out.WriteString(value.Inspect())
		first = false
	}

	out.WriteRune('}')
	return out.String()
}

// Array: [elem1, elem2, ...]
type Array struct {
	Elements []Object
}

// View is a borrowed window over an Array's storage (docs/spec/50-borrowing.md):
// Start and Len select the elements, Writable distinguishes a span ([*]T)
// from a read-only view ([]T). Element access goes through the array, so
// writes through a span are visible to the owner — the interpreter's
// counterpart of the backend's {base, len} pair.
type View struct {
	Array    *Array
	Start    int
	Len      int
	Writable bool
}

func (v *View) Type() ObjectType { return VIEW_OBJ }
func (v *View) Kind() ObjectKind { return ARRAY }
func (v *View) Inspect() string {
	kind := "view"
	if v.Writable {
		kind = "span"
	}
	return kind + "[" + strconv.Itoa(v.Start) + ":" + strconv.Itoa(v.Start+v.Len) + "]"
}

func (a *Array) Type() ObjectType { return ARRAY_OBJ }
func (a *Array) Kind() ObjectKind { return ARRAY }
func (a *Array) Inspect() string {
	var out bytes.Buffer
	out.WriteRune('[')
	for i, elem := range a.Elements {
		if i > 0 {
			out.WriteString(", ")
		}
		out.WriteString(elem.Inspect())
	}
	out.WriteRune(']')
	return out.String()
}

// Vector is a portable SIMD value (docs/spec/93-simd.md): 16 bytes of lane
// storage interpreted per Kind ("U8x16", "U16x8", "U32x4", "U64x2"), lanes
// in index order, each lane little-endian within its bytes.
type Vector struct {
	VectorKind string
	Bytes      [16]byte
}

func (v *Vector) Type() ObjectType { return VECTOR_OBJ }
func (v *Vector) Kind() ObjectKind { return VECTOR }
func (v *Vector) Inspect() string {
	var out bytes.Buffer
	out.WriteString("simd.")
	out.WriteString(v.VectorKind)
	out.WriteRune('(')
	for i, b := range v.Bytes {
		if i > 0 {
			out.WriteRune(' ')
		}
		fmt.Fprintf(&out, "%02x", b)
	}
	out.WriteRune(')')
	return out.String()
}

type ADTType struct {
	Name       string
	TypeParams []string
	Variants   []*ADTVariantDef
}

type ADTVariantDef struct {
	Name          string
	Payload       string   // semantic payload type spelling
	Literal       Object   // optional literal tag
	ResultName    string   // enclosing ADT name for an explicit indexed result
	ResultIndices []string // constructor result indices in source order
}

// A binding is one name in a scope.
type binding struct {
	name  string
	value Object
}

// inlineBindings is how many bindings a scope holds in its own frame before
// spilling to a map: a block, a match arm or a call body rarely declares
// more, so the common scope is one allocation with no map at all.
const inlineBindings = 8

// spillBindings is the largest spill a scope searches linearly before it
// moves every spilled binding into a map.
const spillBindings = 32

type Environment struct {
	// The first bindings live in the frame itself; the rest, if any, in
	// store. A name is in exactly one of the two.
	inline [inlineBindings]binding
	bound  int
	// spill holds the bindings past the inline frame, searched linearly
	// while there are at most spillBindings of them; store takes over
	// beyond that (the root scope with a whole prelude of names).
	spill []binding
	store map[string]Object
	// captured is set once a function value closes over this scope or a
	// scope inside it; an uncaptured scope returns to the pool when its
	// body ends (ReleaseEnvironment).
	captured bool
	adtTypes map[string]*ADTType
	// recordDecls retains record type declarations' field structure
	// (name/order/type expressions) for zero-value construction of
	// storage-identity records in the interpreter.
	recordDecls     map[string]*ast.RecordLiteral
	refinementBases map[string]ast.Expression
	recordTemplates map[string]recordTemplate
	outer           *Environment
	// arithmeticWidths, when set, reports the checker's recorded fixed-width
	// result type of an arithmetic or negation token, so the interpreter
	// wraps exactly as compiled code does. Inherited through enclosures.
	arithmeticWidths func(token.Token) (string, bool)
}

func NewEnvironment() *Environment {
	// A root is never pooled, so it is captured from the start: the mark
	// then stops at it, and goroutines evaluating in scopes under one root
	// never write to it (prove.TheoremsWith runs theorems in parallel).
	return &Environment{adtTypes: make(map[string]*ADTType), captured: true}
}

// NewEnclosedEnvironment opens a scope inside outer. It allocates only the
// binding store: ADT types are looked up through the chain (GetADTType),
// so nothing is copied — a block, a call or a match arm costs one small
// map, not a copy of every declared type. This is what the prover's
// exhaustive enumeration and the REPL pay per evaluated scope
// (docs/notes/formal-methods-performance-2026-09.md, item 5).
func NewEnclosedEnvironment(outer *Environment) *Environment {
	env := envPool.Get().(*Environment)
	env.outer = outer
	if outer != nil {
		env.arithmeticWidths = outer.arithmeticWidths
	}
	return env
}

// envPool holds scopes whose bodies have ended uncaptured, so a block, a
// call or a match arm reuses a frame instead of allocating one.
var envPool = sync.Pool{New: func() any { return &Environment{} }}

// ReleaseEnvironment returns a scope opened by NewEnclosedEnvironment to
// the pool once its body has ended, unless a function value captured it
// (or a scope inside it), in which case the closure keeps it. A root
// environment is never released. Every field is cleared so the pool holds
// no values.
func ReleaseEnvironment(env *Environment) {
	if env == nil || env.outer == nil || env.captured {
		return
	}
	for i := 0; i < env.bound; i++ {
		env.inline[i] = binding{}
	}
	for i := range env.spill {
		env.spill[i] = binding{}
	}
	// The spill's capacity is kept: a scope that spilled once is likely a
	// function body that will spill again.
	spill := env.spill[:0]
	*env = Environment{spill: spill}
	envPool.Put(env)
}

// MarkCaptured records that a function value closes over this scope: it
// and every scope it can reach stay out of the pool.
func (e *Environment) MarkCaptured() {
	for scope := e; scope != nil && !scope.captured; scope = scope.outer {
		scope.captured = true
	}
}

// Locate finds name and says where: hops scopes out, in inline slot slot
// (slot is -1 when the binding spilled to the map). The interpreter caches
// (hops, slot) on the identifier and rechecks it with At.
func (e *Environment) Locate(name string) (value Object, hops, slot int, ok bool) {
	for scope := e; scope != nil; scope = scope.outer {
		for i := 0; i < scope.bound; i++ {
			if scope.inline[i].name == name {
				return scope.inline[i].value, hops, i, true
			}
		}
		for i := range scope.spill {
			if scope.spill[i].name == name {
				return scope.spill[i].value, hops, -1, true
			}
		}
		if scope.store != nil {
			if obj, spilled := scope.store[name]; spilled {
				return obj, hops, -1, true
			}
		}
		hops++
	}
	return nil, 0, 0, false
}

// At reads the binding of name at a cached location, or reports false
// when the scopes have changed shape since the location was cached.
func (e *Environment) At(hops, slot int, name string) (Object, bool) {
	scope := e
	for ; hops > 0 && scope != nil; hops-- {
		scope = scope.outer
	}
	if scope == nil || slot >= scope.bound || scope.inline[slot].name != name {
		return nil, false
	}
	return scope.inline[slot].value, true
}

// AssignAt updates the binding of name at a cached location, or reports
// false when the location no longer holds the name.
func (e *Environment) AssignAt(hops, slot int, name string, val Object) bool {
	scope := e
	for ; hops > 0 && scope != nil; hops-- {
		scope = scope.outer
	}
	if scope == nil || slot >= scope.bound || scope.inline[slot].name != name {
		return false
	}
	scope.inline[slot].value = val
	return true
}

// lookup finds a binding in this scope alone.
func (e *Environment) lookup(name string) (Object, bool) {
	for i := 0; i < e.bound; i++ {
		if e.inline[i].name == name {
			return e.inline[i].value, true
		}
	}
	for i := range e.spill {
		if e.spill[i].name == name {
			return e.spill[i].value, true
		}
	}
	if e.store != nil {
		obj, ok := e.store[name]
		return obj, ok
	}
	return nil, false
}

func (e *Environment) Get(name string) (Object, bool) {
	for scope := e; scope != nil; scope = scope.outer {
		if obj, ok := scope.lookup(name); ok {
			return obj, true
		}
	}
	return nil, false
}

// Set binds name in this scope, replacing an existing binding of the name.
func (e *Environment) Set(name string, val Object) Object {
	for i := 0; i < e.bound; i++ {
		if e.inline[i].name == name {
			e.inline[i].value = val
			return val
		}
	}
	for i := range e.spill {
		if e.spill[i].name == name {
			e.spill[i].value = val
			return val
		}
	}
	if e.store != nil {
		if _, spilled := e.store[name]; spilled {
			e.store[name] = val
			return val
		}
	}
	if e.bound < inlineBindings {
		e.inline[e.bound] = binding{name: name, value: val}
		e.bound++
		return val
	}
	if e.store == nil && len(e.spill) < spillBindings {
		e.spill = append(e.spill, binding{name: name, value: val})
		return val
	}
	if e.store == nil {
		e.store = make(map[string]Object, 2*spillBindings)
		for _, b := range e.spill {
			e.store[b.name] = b.value
		}
		e.spill = nil
	}
	e.store[name] = val
	return val
}

// Assign updates an existing binding in the scope that declares it, so an
// assignment inside a nested block (a match arm, a loop body) reaches the
// outer variable instead of shadowing it. Reports false when no scope
// holds the name.
func (e *Environment) Assign(name string, val Object) bool {
	for scope := e; scope != nil; scope = scope.outer {
		if _, ok := scope.lookup(name); ok {
			scope.Set(name, val)
			return true
		}
	}
	return false
}

// SetRecordTemplate retains a generic record declaration (Idx[P]) with its
// type-parameter names, for zero-value construction of instantiations.
func (e *Environment) SetRecordTemplate(name string, params []string, decl *ast.RecordLiteral) {
	if e.recordTemplates == nil {
		e.recordTemplates = make(map[string]recordTemplate)
	}
	e.recordTemplates[name] = recordTemplate{params: params, decl: decl}
}

// GetRecordTemplate returns a generic record declaration and its
// type-parameter names.
func (e *Environment) GetRecordTemplate(name string) ([]string, *ast.RecordLiteral, bool) {
	template, ok := e.recordTemplates[name]
	if !ok && e.outer != nil {
		return e.outer.GetRecordTemplate(name)
	}
	if !ok {
		return nil, nil, false
	}
	return template.params, template.decl, true
}

type recordTemplate struct {
	params []string
	decl   *ast.RecordLiteral
}

func (e *Environment) GetADTType(name string) (*ADTType, bool) {
	for scope := e; scope != nil; scope = scope.outer {
		if scope.adtTypes == nil {
			continue
		}
		if adt, ok := scope.adtTypes[name]; ok {
			return adt, true
		}
	}
	return nil, false
}

func (e *Environment) SetADTType(name string, adt *ADTType) {
	if e.adtTypes == nil {
		e.adtTypes = make(map[string]*ADTType)
	}
	e.adtTypes[name] = adt
	adtGeneration.Add(1)
}

// adtGeneration counts type declarations: the interpreter caches "this
// name was not a type" on an identifier together with the generation it
// checked, and a declaration anywhere invalidates every such cache.
var adtGeneration atomic.Uint32

// ADTGeneration is the current type-declaration generation.
func ADTGeneration() uint32 { return adtGeneration.Load() }

// TypesOnlyAtRoot reports whether every type visible from this scope is
// declared in the root: then whether a name is a type does not depend on
// which scope asks, and the answer can be cached per identifier.
func (e *Environment) TypesOnlyAtRoot() bool {
	for scope := e; scope != nil; scope = scope.outer {
		if scope.adtTypes != nil && scope.outer != nil {
			return false
		}
	}
	return true
}

// SetRefinementBase retains a refinement declaration's base type, so a
// zero value of the refined type is the base's zero (evaluator/zero.go).
func (e *Environment) SetRefinementBase(name string, base ast.Expression) {
	if e.refinementBases == nil {
		e.refinementBases = make(map[string]ast.Expression)
	}
	e.refinementBases[name] = base
}

// GetRefinementBase resolves a refinement's base type through the scope
// chain.
func (e *Environment) GetRefinementBase(name string) (ast.Expression, bool) {
	base, ok := e.refinementBases[name]
	if !ok && e.outer != nil {
		return e.outer.GetRefinementBase(name)
	}
	return base, ok
}

// SetRecordDecl retains a record declaration's field structure.
func (e *Environment) SetRecordDecl(name string, decl *ast.RecordLiteral) {
	if e.recordDecls == nil {
		e.recordDecls = make(map[string]*ast.RecordLiteral)
	}
	e.recordDecls[name] = decl
}

// GetRecordDecl resolves a record declaration through the scope chain.
func (e *Environment) GetRecordDecl(name string) (*ast.RecordLiteral, bool) {
	decl, ok := e.recordDecls[name]
	if !ok && e.outer != nil {
		return e.outer.GetRecordDecl(name)
	}
	return decl, ok
}

// GetAllADTTypes is every ADT type visible from this scope. The root
// environment returns its own table (the type checker is built on the
// root and records declarations into it); an enclosed scope returns a
// merged copy over the chain, inner declarations shadowing outer ones.
func (e *Environment) GetAllADTTypes() map[string]*ADTType {
	if e.outer == nil {
		return e.adtTypes
	}
	merged := make(map[string]*ADTType)
	for scope := e; scope != nil; scope = scope.outer {
		for name, adt := range scope.adtTypes {
			if _, shadowed := merged[name]; !shadowed {
				merged[name] = adt
			}
		}
	}
	return merged
}

func (e *Environment) GetOuter() *Environment {
	return e.outer
}

type ObjectKind int

type Object interface {
	Type() ObjectType
	Inspect() string
}

type ObjectType string

const (
	INTEGER_OBJ      = "INTEGER"
	U128_OBJ         = "U128"
	FLOAT_OBJ        = "FLOAT"
	BOOLEAN_OBJ      = "BOOLEAN"
	STRING_OBJ       = "STRING"
	NULL_OBJ         = "NULL"
	RETURN_VALUE_OBJ = "RETURN_VALUE"
	BREAK_OBJ        = "BREAK"
	ERROR_OBJ        = "ERROR"
	FUNCTION_OBJ     = "FUNCTION"
	ADT_OBJ          = "ADT"
	RECORD_OBJ       = "RECORD"
	ARRAY_OBJ        = "ARRAY"
	VIEW_OBJ         = "VIEW"
	VECTOR_OBJ       = "VECTOR"
)

const (
	ILLEGAL ObjectKind = iota
	INTEGER
	BOOLEAN
	STRING
	NULL
	FUNCTION
	ADT
	VARIANT
	ERROR
	RETURN_VALUE
	BREAK
	RECORD
	ARRAY
	VECTOR
	FLOAT
	WIDE
)

var types = [...]string{
	ILLEGAL:      "ILLEGAL",
	INTEGER:      "INTEGER",
	BOOLEAN:      "BOOLEAN",
	STRING:       "STRING",
	NULL:         "NULL",
	FUNCTION:     "FUNCTION",
	ADT:          "ADT",
	VARIANT:      "VARIANT",
	ERROR:        "ERROR",
	RETURN_VALUE: "RETURN_VALUE",
	RECORD:       "RECORD",
	ARRAY:        "ARRAY",
	VECTOR:       "VECTOR",
	FLOAT:        "FLOAT",
	WIDE:         "U128",
}

func (kind ObjectKind) String() string {
	s := ""
	if 0 <= kind && kind < ObjectKind(len(types)) {
		s = types[kind]
	}
	if s == "" {
		s = "object(" + strconv.Itoa(int(kind)) + ")"
	}
	return s
}

// SetArithmeticWidths installs the checker's width oracle (typically
// TypeChecker.ArithmeticType) so evaluation wraps fixed-width arithmetic
// like the compiled backend. Without one the interpreter computes on
// untyped 64-bit integers.
func (e *Environment) SetArithmeticWidths(oracle func(token.Token) (string, bool)) {
	e.arithmeticWidths = oracle
}

// ArithmeticWidth reports the recorded fixed-width type of a token, if an
// oracle is installed in this environment or an enclosing one.
func (e *Environment) ArithmeticWidth(tok token.Token) (string, bool) {
	for env := e; env != nil; env = env.outer {
		if env.arithmeticWidths != nil {
			return env.arithmeticWidths(tok)
		}
	}
	return "", false
}

// Float is a floating-point value of one width (docs/spec/20-types.md
// section 11.3): Bits is 32 or 64, and Value holds the exactly representable
// number of that width (an f32 value is stored widened, which is exact).
type Float struct {
	Value float64
	Bits  int
	// Format names a storage kind ("f16" or "bf16" when Bits is 16, "f8e4m3"
	// or "f8e5m2" when Bits is 8); Value then holds the exactly representable
	// widened number.
	Format string
}

func (f *Float) Kind() ObjectKind { return FLOAT }
func (f *Float) Type() ObjectType { return FLOAT_OBJ }
func (f *Float) Inspect() string {
	bits := f.Bits
	if bits != 32 {
		bits = 64
	}
	return strconv.FormatFloat(f.Value, 'g', -1, bits)
}
