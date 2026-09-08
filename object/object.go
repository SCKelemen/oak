package object

import (
	"bytes"
	"fmt"
	"strconv"

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

type Error struct {
	Message string
}

func (e *Error) Type() ObjectType { return ERROR_OBJ }
func (e *Error) Inspect() string  { return "ERROR: " + e.Message }
func (e *Error) Kind() ObjectKind { return ERROR }

// Record: { field1: value1, field2: value2, ... }
type Record struct {
	Fields map[string]Object
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

type Environment struct {
	store    map[string]Object
	adtTypes map[string]*ADTType
	// recordDecls retains record type declarations' field structure
	// (name/order/type expressions) for zero-value construction of
	// storage-identity records in the interpreter.
	recordDecls map[string]*ast.RecordLiteral
	outer       *Environment
}

func NewEnvironment() *Environment {
	return &Environment{
		store:    make(map[string]Object),
		adtTypes: make(map[string]*ADTType),
		outer:    nil,
	}
}

func NewEnclosedEnvironment(outer *Environment) *Environment {
	env := NewEnvironment()
	env.outer = outer
	// Copy ADT types from outer environment
	if outer != nil {
		for name, adtType := range outer.GetAllADTTypes() {
			env.adtTypes[name] = adtType
		}
	}
	return env
}

func (e *Environment) Get(name string) (Object, bool) {
	obj, ok := e.store[name]
	if !ok && e.outer != nil {
		obj, ok = e.outer.Get(name)
	}
	return obj, ok
}

func (e *Environment) Set(name string, val Object) Object {
	e.store[name] = val
	return val
}

func (e *Environment) GetADTType(name string) (*ADTType, bool) {
	adt, ok := e.adtTypes[name]
	if !ok && e.outer != nil {
		adt, ok = e.outer.GetADTType(name)
	}
	return adt, ok
}

func (e *Environment) SetADTType(name string, adt *ADTType) {
	e.adtTypes[name] = adt
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

func (e *Environment) GetAllADTTypes() map[string]*ADTType {
	return e.adtTypes
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
	BOOLEAN_OBJ      = "BOOLEAN"
	STRING_OBJ       = "STRING"
	NULL_OBJ         = "NULL"
	RETURN_VALUE_OBJ = "RETURN_VALUE"
	ERROR_OBJ        = "ERROR"
	FUNCTION_OBJ     = "FUNCTION"
	ADT_OBJ          = "ADT"
	RECORD_OBJ       = "RECORD"
	ARRAY_OBJ        = "ARRAY"
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
	RECORD
	ARRAY
	VECTOR
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
