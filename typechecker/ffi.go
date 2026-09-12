package typechecker

// The compiler-known foreign-interface libraries: the `c` interface library
// and the `arm64` abstract-assembly instruction library.
// Implementation of docs/spec/92-ffi.md.

import (
	"fmt"
	"regexp"
	"sort"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/modules"
)

// Diagnostic codes of the FFI family (docs/spec/92-ffi.md section 2.3).
const (
	// CodeExternSignatureNotC rejects extern binding signatures that
	// mention non-c.* parameter or return types: Oak types never cross the
	// boundary raw ("ABI honesty").
	CodeExternSignatureNotC = "OAK-F0101"
	// CodeExternSymbolInvalid rejects extern symbols that are not C
	// identifiers. This is the injection-freedom rule: the symbol is
	// emitted verbatim into generated C source, and the identifier grammar
	// is what makes that emission safe.
	CodeExternSymbolInvalid = "OAK-F0102"
	// CodeExternOutsideDefinition rejects `c.extern` anywhere other than
	// as the whole definition of a declaration-form function.
	CodeExternOutsideDefinition = "OAK-F0103"
	// CodeSpanElementNotABI rejects a boundary span whose element type has
	// no single meaning on both sides of the C boundary (section 2.5.1).
	CodeSpanElementNotABI = "OAK-F0104"
	// CodeSpanParameterPair rejects c.span_of/c.span_mut_of that does not
	// line up with a `c.Ptr, c.Size` parameter pair (section 2.5.1).
	CodeSpanParameterPair = "OAK-F0105"
	// CodeCStringNotLiteral rejects c.String over anything but a string
	// literal (section 2.5.3).
	CodeCStringNotLiteral = "OAK-F0106"
	// CodeForeignBorrowPlacement rejects c.borrow/c.borrow_mut outside an
	// unsafe block or anywhere but the initializer of a named binding
	// (docs/spec/92-ffi.md section 2.7).
	CodeForeignBorrowPlacement = "OAK-F0107"
	// CodeExportSymbolConflict rejects two C ABI exports that would share
	// one symbol, an explicit `export("...")` colliding with another export
	// or with a root package pub function's implicit `oak_<name>`
	// (docs/spec/92-ffi.md section 2.9).
	CodeExportSymbolConflict = "OAK-F0108"
	// CodeExportInvalid rejects an `export("...")` whose symbol is not a C
	// identifier or whose function has no single C ABI shape: a generic
	// template, a method, an extern binding, or a non-pub function
	// (docs/spec/92-ffi.md section 2.9).
	CodeExportInvalid = "OAK-F0109"
	// CodeCStringArgument rejects a `c.cstr(v)` argument that does not stand
	// for a `c.String` parameter, whose operand is not a named `[]u8` view
	// or a string literal, or whose literal operand is not NUL-terminated
	// (docs/spec/92-ffi.md section 2.5.3).
	CodeCStringArgument = "OAK-F0110"
	// CodeArgvArgument rejects a `c.argv_of(bytes, slots)` argument that
	// does not stand for a `c.Ptr` parameter, or whose operands are not a
	// named read-only `[]u8` view and a named writable `[*]c.Ptr` span
	// (docs/spec/92-ffi.md section 2.5.6).
	CodeArgvArgument = "OAK-F0111"
	// CodeOutArgument rejects a `c.out(x)` argument that does not stand for
	// a `c.Ptr` parameter, or whose operand is not a local binding of a
	// `c.*` scalar type or of a declared struct with boundary fields
	// (docs/spec/92-ffi.md section 2.5.7).
	CodeOutArgument = "OAK-F0112"
	// CodeForeignFunctionType rejects a `c.Fn[...]` type anywhere but as
	// the annotation of a local binding that `c.fn_at(p)` initializes inside
	// an unsafe block, a `c.fn_at` without that annotation, and a `c.Fn`
	// signature whose parameter or return types are not boundary types
	// (docs/spec/92-ffi.md section 2.10).
	CodeForeignFunctionType = "OAK-F0113"
)

// CType is a member of the `c` interface library (docs/spec/92-ffi.md
// section 2.1): a nominal foreign type, distinct from every Oak type, with
// no implicit conversions, arithmetic, or dereference.
type CType struct {
	Name string // the member name: "Int32", "Size", "Ptr", ...
}

func (t *CType) String() string { return "c." + t.Name }

func (t *CType) Equals(other Type) bool {
	if otherC, ok := other.(*CType); ok {
		return t.Name == otherC.Name
	}
	return false
}

// cTypeSpellings is the c-library type table of docs/spec/92-ffi.md
// section 2.1: member name to C spelling. It is the single authority for
// which members exist; the backend derives declarations from it.
var cTypeSpellings = map[string]string{
	"Char":   "char",
	"Int8":   "int8_t",
	"Int16":  "int16_t",
	"Int32":  "int32_t",
	"Int64":  "int64_t",
	"UInt8":  "uint8_t",
	"UInt16": "uint16_t",
	"UInt32": "uint32_t",
	"UInt64": "uint64_t",
	"Int":    "int",
	"UInt":   "unsigned int",
	"Long":   "long",
	"ULong":  "unsigned long",
	"Size":   "size_t",
	"Float":  "float",
	"Double": "double",
	"Bool":   "_Bool",
	"Ptr":    "void *",
	"String": "const char *",
}

// CTypeSpelling returns the C spelling of a `c` library member, so the C
// backend and the type checker share one table.
func CTypeSpelling(member string) (string, bool) {
	spelling, ok := cTypeSpellings[member]
	return spelling, ok
}

// cConversionOakOperand gives, for each convertible c member, the Oak
// primitive its constructor accepts (docs/spec/92-ffi.md section 2.2).
// Width and signedness are preserved by every row; c.Int/c.UInt/c.Size rows
// hold under the recorded ILP32/LP64 target model (section 2.4).
var cConversionOakOperand = map[string]string{
	"Int8": "i8", "Int16": "i16", "Int32": "i32", "Int64": "i64",
	"UInt8": "u8", "UInt16": "u16", "UInt32": "u32", "UInt64": "u64",
	"Char": "u8",
	"Int":  "i32", "UInt": "u32",
	"Size": "u32",
	// Bit-preserving float rows (docs/spec/92-ffi.md section 2.2,
	// 20-types.md section 11.3.4).
	"Float": "f32", "Double": "f64",
}

// oakConversionCOperands is the reverse direction: which c members an Oak
// primitive constructor accepts. Only the total (value-preserving) rows are
// invertible; `c.Size` narrowing back to `u32` is deliberately absent.
var oakConversionCOperands = map[string][]string{
	"i8": {"Int8"}, "i16": {"Int16"}, "i32": {"Int32", "Int"}, "i64": {"Int64"},
	"u8": {"UInt8", "Char"}, "u16": {"UInt16"}, "u32": {"UInt32", "UInt"}, "u64": {"UInt64"},
	"f32": {"Float"}, "f64": {"Double"},
}

// SimdType is a member of the `simd` portable vector library
// (docs/spec/93-simd.md): a nominal 16-byte vector value with no implicit
// conversions and no borrow interaction.
type SimdType struct {
	Name string // "U8x16", "U16x8", "U32x4", "U64x2"
}

func (t *SimdType) String() string { return "simd." + t.Name }

func (t *SimdType) Equals(other Type) bool {
	if otherSimd, ok := other.(*SimdType); ok {
		return t.Name == otherSimd.Name
	}
	return false
}

// SimdShape describes one vector type of docs/spec/93-simd.md section 1.1.
type SimdShape struct {
	TypeName string // library member: "U8x16"
	Suffix   string // op suffix: "u8x16"
	ElemName string // lane primitive: "u8"
	Lanes    int    // lane count
	// Float marks the floating-point vectors (docs/spec/20-types.md
	// section 11.3.7), whose operation set differs from the integer one.
	Float bool
}

// SimdShapes is the v1 vector catalog, shared with the backend and the
// interpreter (single authority for suffixes, lane types, and counts).
var SimdShapes = []SimdShape{
	{TypeName: "U8x16", Suffix: "u8x16", ElemName: "u8", Lanes: 16},
	{TypeName: "U16x8", Suffix: "u16x8", ElemName: "u16", Lanes: 8},
	{TypeName: "U32x4", Suffix: "u32x4", ElemName: "u32", Lanes: 4},
	{TypeName: "U64x2", Suffix: "u64x2", ElemName: "u64", Lanes: 2},
	{TypeName: "F32x4", Suffix: "f32x4", ElemName: "f32", Lanes: 4, Float: true},
	{TypeName: "F64x2", Suffix: "f64x2", ElemName: "f64", Lanes: 2, Float: true},
}

// SimdFloatBinaryOps, SimdFloatUnaryOps: the lane-wise operations of the
// floating-point vectors (section 11.3.7); each lane obeys the scalar rules
// of sections 11.3.3 and 11.3.5 (min/max are IEEE 754-2019 minimum/maximum).
var SimdFloatBinaryOps = []string{"add", "sub", "mul", "div", "min", "max"}
var SimdFloatUnaryOps = []string{"sqrt", "neg", "abs"}

// SimdShapeBySuffix resolves an op suffix ("u8x16") to its shape.
func SimdShapeBySuffix(suffix string) (SimdShape, bool) {
	for _, shape := range SimdShapes {
		if shape.Suffix == suffix {
			return shape, true
		}
	}
	return SimdShape{}, false
}

// simdTypeNames indexes the vector type members.
var simdTypeNames = func() map[string]bool {
	names := make(map[string]bool, len(SimdShapes))
	for _, shape := range SimdShapes {
		names[shape.TypeName] = true
	}
	return names
}()

// simdOps is the operation catalog of docs/spec/93-simd.md section 1.2,
// built per vector shape: splat, bounds-checked load/store, wrapping
// add/sub, bitwise and/or/xor, unsigned min/max, eq masks, any/all.
var simdOps = func() map[string]*FunctionType {
	ops := make(map[string]*FunctionType)
	for _, shape := range SimdShapes {
		vector := &SimdType{Name: shape.TypeName}
		elem := &PrimitiveType{Name: shape.ElemName}
		view := &ArrayType{Length: -1, IsSlice: true, ElementType: elem}
		span := &ArrayType{Length: -1, IsSpan: true, ElementType: elem}
		offset := &PrimitiveType{Name: "u32"}
		ops["splat_"+shape.Suffix] = &FunctionType{Parameters: []Type{elem}, ReturnType: vector}
		ops["load_"+shape.Suffix] = &FunctionType{Parameters: []Type{view, offset}, ReturnType: vector}
		ops["store_"+shape.Suffix] = &FunctionType{Parameters: []Type{span, offset, vector}, ReturnType: &UnitType{}}
		if shape.Float {
			// Floating-point vectors (docs/spec/20-types.md section 11.3.7):
			// lane-wise arithmetic, fma, lane access, and the pairwise
			// reduce_add whose grouping is its semantics.
			for _, binary := range SimdFloatBinaryOps {
				ops[binary+"_"+shape.Suffix] = &FunctionType{Parameters: []Type{vector, vector}, ReturnType: vector}
			}
			for _, unary := range SimdFloatUnaryOps {
				ops[unary+"_"+shape.Suffix] = &FunctionType{Parameters: []Type{vector}, ReturnType: vector}
			}
			ops["fma_"+shape.Suffix] = &FunctionType{Parameters: []Type{vector, vector, vector}, ReturnType: vector}
			ops["extract_"+shape.Suffix] = &FunctionType{Parameters: []Type{vector, offset}, ReturnType: elem}
			ops["insert_"+shape.Suffix] = &FunctionType{Parameters: []Type{vector, offset, elem}, ReturnType: vector}
			ops["reduce_add_"+shape.Suffix] = &FunctionType{Parameters: []Type{vector}, ReturnType: elem}
			continue
		}
		for _, binary := range []string{"add", "sub", "and", "or", "xor", "min", "max", "eq"} {
			ops[binary+"_"+shape.Suffix] = &FunctionType{Parameters: []Type{vector, vector}, ReturnType: vector}
		}
		for _, reduction := range []string{"any", "all"} {
			ops[reduction+"_"+shape.Suffix] = &FunctionType{Parameters: []Type{vector}, ReturnType: &BoolType{}}
		}
	}
	return ops
}()

// arm64Intrinsics is the AArch64 instruction-function catalog
// (docs/spec/92-ffi.md section 3.2, docs/spec/93-simd.md section 2).
// Every function is total; the semantic laws live in Oak.Intrinsics and
// Oak.Simd (Lean).
var arm64Intrinsics = map[string]*FunctionType{
	"rev32":  {Parameters: []Type{&PrimitiveType{Name: "u32"}}, ReturnType: &PrimitiveType{Name: "u32"}},
	"rev64":  {Parameters: []Type{&PrimitiveType{Name: "u64"}}, ReturnType: &PrimitiveType{Name: "u64"}},
	"rbit32": {Parameters: []Type{&PrimitiveType{Name: "u32"}}, ReturnType: &PrimitiveType{Name: "u32"}},
	"rbit64": {Parameters: []Type{&PrimitiveType{Name: "u64"}}, ReturnType: &PrimitiveType{Name: "u64"}},
	"clz32":  {Parameters: []Type{&PrimitiveType{Name: "u32"}}, ReturnType: &PrimitiveType{Name: "u32"}},
	"clz64":  {Parameters: []Type{&PrimitiveType{Name: "u64"}}, ReturnType: &PrimitiveType{Name: "u64"}},

	// Horizontal vector instructions (docs/spec/93-simd.md section 2).
	"uaddlv_u8x16": {Parameters: []Type{&SimdType{Name: "U8x16"}}, ReturnType: &PrimitiveType{Name: "u32"}},
	"umaxv_u8x16":  {Parameters: []Type{&SimdType{Name: "U8x16"}}, ReturnType: &PrimitiveType{Name: "u8"}},
	"uminv_u8x16":  {Parameters: []Type{&SimdType{Name: "U8x16"}}, ReturnType: &PrimitiveType{Name: "u8"}},
	"cnt_u8x16":    {Parameters: []Type{&SimdType{Name: "U8x16"}}, ReturnType: &SimdType{Name: "U8x16"}},
}

// Arm64IntrinsicNames reports whether name is a v1 arm64 instruction
// function, shared with the backend and the interpreter.
func Arm64IntrinsicNames() []string {
	names := make([]string, 0, len(arm64Intrinsics))
	for name := range arm64Intrinsics {
		names = append(names, name)
	}
	return names
}

// KnownLibraryMember reports whether library.member names a compiler-known
// library member (a c type, c.extern, or an arm64 instruction function), so
// lowering and the backend can preserve library accesses structurally.
func KnownLibraryMember(library, member string) bool {
	switch library {
	case "c":
		_, isType := cTypeSpellings[member]
		return isType || member == "extern" || member == "span_of" || member == "span_mut_of" ||
			member == "borrow" || member == "borrow_mut" || member == "own" || member == "disown" ||
			member == "cstr" || member == "borrow_string" || member == "argv_of" || member == "out" || member == "null" ||
			member == "const"
	case "arm64":
		_, isIntrinsic := arm64Intrinsics[member]
		return isIntrinsic
	case "simd":
		_, isOp := simdOps[member]
		return isOp || simdTypeNames[member]
	}
	return false
}

// conversionPrimitives are the fixed-width operands of the explicit
// conversion family ({target}_{op}_{source}: trunc, saturating, checked,
// bits — docs/spec/20-types.md).
var conversionPrimitives = map[string]int{
	"u8": 8, "u16": 16, "u32": 32, "u64": 64,
	"i8": 8, "i16": 16, "i32": 32, "i64": 64,
	// Floating-point rows (docs/spec/20-types.md section 11.3.4); the
	// backend and interpreter branch on IsFloatName before treating a
	// width as an integer width.
	"f32": 32, "f64": 64,
	// Storage formats (section 11.3.1): round from f32, bits with u16.
	"f16": 16, "bf16": 16,
	// The 8-bit storage formats (section 11.3.1): round and saturate from
	// f32, bits with u8.
	"f8e4m3": 8, "f8e5m2": 8,
}

var conversionOperations = map[string]bool{
	"trunc": true, "saturating": true, "checked": true, "bits": true, "round": true,
}

// ConversionParts destructures an explicit-conversion function name for the
// backend and the interpreter, sharing the type checker's grammar. The
// caller still validates the pair per operation.
func ConversionParts(name string) (target, op, source string, ok bool) {
	parts := splitNarrowingFunctionName(name)
	if parts == nil {
		return "", "", "", false
	}
	target, op, source = parts[0], parts[1], parts[2]
	if _, isPrim := conversionPrimitives[target]; !isPrim {
		return "", "", "", false
	}
	if _, isPrim := conversionPrimitives[source]; !isPrim {
		return "", "", "", false
	}
	if !conversionOperations[op] {
		return "", "", "", false
	}
	return target, op, source, true
}

// PrimitiveBits is the fixed width of a conversion operand.
func PrimitiveBits(name string) int { return conversionPrimitives[name] }

// cIdentifierPattern is the C identifier grammar of OAK-F0102.
var cIdentifierPattern = regexp.MustCompile(`^[A-Za-z_][A-Za-z0-9_]*$`)

// ValidCSymbol reports whether symbol satisfies the OAK-F0102 identifier
// grammar. The backend re-checks this before emitting (defense in depth).
func ValidCSymbol(symbol string) bool {
	return cIdentifierPattern.MatchString(symbol)
}

// libraryQualifiedType resolves a dotted type identifier ("c.Int32") to its
// library type, reporting whether the name was library-qualified at all.
// Unknown members of a known library resolve to nil after a diagnostic.
func (tc *TypeChecker) libraryQualifiedType(ident *ast.Identifier) (Type, bool) {
	library, member, ok := splitQualifiedName(ident.Value)
	if !ok {
		return nil, false
	}
	switch library {
	case "c":
		if _, known := cTypeSpellings[member]; known {
			return &CType{Name: member}, true
		}
		tc.addError(ident, "the c library has no type c.%s", member)
		return nil, true
	case "arm64":
		tc.addError(ident, "arm64.%s is an instruction function, not a type", member)
		return nil, true
	case "simd":
		if simdTypeNames[member] {
			return &SimdType{Name: member}, true
		}
		tc.addError(ident, "the simd library has no type simd.%s", member)
		return nil, true
	default:
		return nil, false
	}
}

func splitQualifiedName(name string) (library, member string, ok bool) {
	for i := 0; i < len(name); i++ {
		if name[i] == '.' {
			return name[:i], name[i+1:], i > 0 && i < len(name)-1
		}
	}
	return "", "", false
}

// libraryAccess destructures an expression of the shape `library.member`
// for the compiler-known libraries.
func libraryAccess(expr ast.Expression) (library, member string, ok bool) {
	access, isAccess := expr.(*ast.IndexExpression)
	if !isAccess {
		return "", "", false
	}
	base, isIdent := access.Left.(*ast.Identifier)
	if !isIdent || !compilerKnownLibraries[base.Value] {
		return "", "", false
	}
	memberIdent, isIdent := access.Index.(*ast.Identifier)
	if !isIdent {
		return "", "", false
	}
	return base.Value, memberIdent.Value, true
}

// compilerKnownLibraries are the reserved library names of
// docs/spec/92-ffi.md and docs/spec/93-simd.md.
var compilerKnownLibraries = map[string]bool{
	"c": true, "arm64": true, "simd": true,
}

// CompilerKnownLibrary reports whether name is a compiler-known library.
func CompilerKnownLibrary(name string) bool {
	return compilerKnownLibraries[name]
}

// checkLibraryInvocation types calls whose callee is a compiler-known
// library member: c conversions, misplaced c.extern, and arm64 instruction
// functions. Reports whether the call was such a library call.
func (tc *TypeChecker) checkLibraryInvocation(expr *ast.InvocationExpression) (Type, bool) {
	library, member, ok := libraryAccess(expr.Function)
	if !ok {
		return nil, false
	}
	// A local binding shadows the library name in expression position
	// (docs/spec/92-ffi.md section 2): `c` is an ordinary variable name.
	if _, bound := tc.env.Get(library); bound {
		return nil, false
	}
	switch library {
	case "c":
		return tc.checkCLibraryCall(expr, member), true
	case "arm64":
		return tc.checkCatalogCall(expr, "arm64", member, arm64Intrinsics,
			"the arm64 library has no instruction function arm64.%s"), true
	case "simd":
		typ := tc.checkCatalogCall(expr, "simd", member, simdOps,
			"the simd library has no operation simd.%s")
		if _, known := simdOps[member]; known {
			if info := tc.env.borrowMetadata(); info != nil {
				if info.simdCalls == nil {
					info.simdCalls = make(map[*ast.InvocationExpression]string)
				}
				info.simdCalls[expr] = member
			}
		}
		return typ, true
	}
	return nil, false
}

func (tc *TypeChecker) checkCLibraryCall(expr *ast.InvocationExpression, member string) Type {
	if member == "extern" {
		d := tc.addTypeDiagnostic(expr, CodeExternOutsideDefinition,
			"c.extern is only a definition, not an expression")
		d.AddHelp("bind it as a whole function definition: name: (params): c.Ret = c.extern(\"symbol\")")
		return nil
	}
	switch member {
	case "msg_send":
		// A message send carries its signature in brackets and is a call
		// (docs/spec/92-ffi.md section 2.12); the parser and the invocation
		// checker handle that form, so reaching it here means the brackets
		// were left out.
		d := tc.addTypeDiagnostic(expr, CodeMessageSend,
			"c.msg_send takes the selector's signature in brackets: c.msg_send[(params) -> ret](receiver, selector, args...)")
		d.AddNote("the bracketed signature is the declared ABI of the selector's implementation, as an extern binding's signature is (docs/spec/92-ffi.md section 2.12)")
		return nil
	case "const":
		// A target constant exists only as the initializer of a top-level
		// binding with a c.* scalar annotation (docs/spec/92-ffi.md
		// section 2.11); checkVariableDeclaration consumes that form, so
		// reaching it here means it was written somewhere else.
		d := tc.addTypeDiagnostic(expr, CodeTargetConstant,
			"c.const is only the initializer of a top-level binding with a c.* integer annotation, not an expression")
		d.AddHelp("write NAME: c.Int = c.const(\"CLOCK_MONOTONIC\", \"<time.h>\") at package level and read NAME")
		return nil
	case "disown":
		return tc.checkForeignDisown(expr)
	case "borrow_string":
		return tc.checkForeignStringBorrow(expr)
	case "fn_at":
		return tc.checkForeignFunctionAt(expr)
	case "cstr":
		// A C string from Oak bytes is not an expression either: it exists
		// only as the argument standing for a c.String parameter of an
		// extern binding (docs/spec/92-ffi.md section 2.5.3).
		d := tc.addTypeDiagnostic(expr, CodeExternOutsideDefinition,
			"c.cstr is only an argument to an extern binding, not an expression")
		d.AddNote("c.cstr(v) hands C the base pointer of a NUL-terminated []u8 view for the duration of one foreign call and cannot be bound, stored, returned, or passed to Oak code")
		return nil
	case "argv_of", "out":
		// An argument vector and an out-parameter are not expressions
		// either: each stands for one c.Ptr parameter of an extern binding
		// for the duration of that call (docs/spec/92-ffi.md sections 2.5.6
		// and 2.5.7).
		d := tc.addTypeDiagnostic(expr, CodeExternOutsideDefinition,
			fmt.Sprintf("c.%s is only an argument to an extern binding, not an expression", member))
		d.AddNote("the pointer it forms exists for the duration of one foreign call and cannot be bound, stored, returned, or passed to Oak code")
		return nil
	case "span_of", "span_mut_of":
		// Boundary spans are not expressions: they exist only as arguments
		// of a call to an extern binding, where checkInvocationExpression
		// consumes them (docs/spec/92-ffi.md section 2.5.2).
		d := tc.addTypeDiagnostic(expr, CodeExternOutsideDefinition,
			fmt.Sprintf("c.%s is only an argument to an extern binding, not an expression", member))
		d.AddNote("a boundary span yields a c.Ptr, c.Size pair for the duration of one foreign call and cannot be bound, stored, returned, or passed to Oak code")
		return nil
	case "null":
		// c.null() is the one c.Ptr Oak may construct: the null pointer, for
		// the optional pointer parameters of foreign calls (posix_spawn's
		// file actions, attributes, and environment). It is as opaque as
		// every other c.Ptr (docs/spec/92-ffi.md section 2.1).
		if len(expr.Arguments) != 0 {
			tc.addError(expr, "c.null takes no arguments")
			return nil
		}
		return &CType{Name: "Ptr"}
	case "String":
		// c.String is constructible from a literal only: the backend emits
		// the literal NUL-terminated, and a runtime string would need a
		// copy the language does not perform silently (section 2.5.3).
		if len(expr.Arguments) != 1 {
			tc.addError(expr, "c.String takes exactly one string literal argument")
			return nil
		}
		if _, isLiteral := expr.Arguments[0].(*ast.StringLiteral); !isLiteral {
			d := tc.addTypeDiagnostic(expr.Arguments[0], CodeCStringNotLiteral,
				"c.String requires a string literal")
			d.AddNote("Oak strings carry a length and are not NUL-terminated; terminate runtime text yourself and pass c.span_of over its bytes (docs/spec/92-ffi.md section 2.5.3)")
			return nil
		}
		return &CType{Name: member}
	}
	oakOperand, convertible := cConversionOakOperand[member]
	if !convertible {
		if _, known := cTypeSpellings[member]; known {
			tc.addError(expr, "no conversion constructs c.%s from an Oak value (docs/spec/92-ffi.md section 2.2)", member)
		} else {
			tc.addError(expr, "the c library has no member c.%s", member)
		}
		return nil
	}
	if len(expr.Arguments) != 1 {
		tc.addError(expr, "c.%s takes exactly one %s argument", member, oakOperand)
		return nil
	}
	required := &PrimitiveType{Name: oakOperand}
	argType := tc.checkExpression(expr.Arguments[0], required)
	if argType != nil && !argType.Equals(required) {
		tc.addError(expr.Arguments[0], "c.%s converts %s values, got %s", member, oakOperand, argType)
		return nil
	}
	return &CType{Name: member}
}

// checkCatalogCall types a call against a fixed library catalog (the arm64
// instruction functions or the simd operations): exact arity, each argument
// checked against its declared parameter type.
func (tc *TypeChecker) checkCatalogCall(expr *ast.InvocationExpression, library, member string, catalog map[string]*FunctionType, unknownFormat string) Type {
	signature, known := catalog[member]
	if !known {
		tc.addError(expr, unknownFormat, member)
		return nil
	}
	if len(expr.Arguments) != len(signature.Parameters) {
		tc.addError(expr, "%s.%s takes %d argument(s), got %d", library, member, len(signature.Parameters), len(expr.Arguments))
		return nil
	}
	for i, arg := range expr.Arguments {
		argType := tc.checkExpression(arg, signature.Parameters[i])
		if argType != nil && !argType.Equals(signature.Parameters[i]) {
			tc.addError(arg, "%s.%s expects %s, got %s", library, member, signature.Parameters[i], argType)
			return nil
		}
	}
	return signature.ReturnType
}

// cConversionToOak reports whether an Oak primitive constructor accepts a
// value of the given c type: `i32(x: c.Int32)` and the other invertible
// rows of the conversion table.
func cConversionToOak(oakName string, arg Type) bool {
	cArg, isC := arg.(*CType)
	if !isC {
		return false
	}
	for _, member := range oakConversionCOperands[normalizePrimitiveName(oakName)] {
		if member == cArg.Name {
			return true
		}
	}
	return false
}

// checkExternFunction validates and registers an extern binding
// (docs/spec/92-ffi.md section 2.3). The declaration is the recorded trust
// boundary: the signature is asserted, not checked, against the foreign
// symbol. Returns the declared function type, or nil if invalid.
// checkAsmBoundary validates the typed interface of an asm-backed
// declaration (docs/spec/94-assembler.md §3): v1 admits fixed-width
// integers, f32/f64, Bool, and simd vectors across the boundary, spans and
// views of the fixed-width scalars, plus () and never results. The
// signature is registered so calls type ordinarily; the body is the
// unit's, checked by the assembler.
func (tc *TypeChecker) checkAsmBoundary(stmt *ast.FunctionStatement) {
	if tc.asmBackedFunctions == nil {
		tc.asmBackedFunctions = make(map[string]bool)
	}
	tc.asmBackedFunctions[stmt.Name.Value] = true
	if stmt.Receiver != nil || len(stmt.TypeParams) > 0 {
		tc.addError(stmt, "asm-backed function %s cannot have a receiver or generic parameters", stmt.Name.Value)
		return
	}
	fixedWidth := func(t *PrimitiveType) bool {
		return t != nil && (t.Name[0] == 'u' || t.Name[0] == 'i' || t.Name == "f32" || t.Name == "f64")
	}
	boundary := func(typ Type) bool {
		switch t := typ.(type) {
		case *PrimitiveType:
			return fixedWidth(t)
		case *BoolType, *SimdType:
			return true
		case *ArrayType:
			// Spans and views of fixed-width elements cross as {base, len}
			// pairs (docs/spec/94-assembler.md §7); owned arrays do not.
			if t == nil || !(t.IsSpan || t.IsSlice) {
				return false
			}
			elem, isPrim := t.ElementType.(*PrimitiveType)
			return isPrim && fixedWidth(elem)
		}
		return false
	}
	for _, param := range stmt.Parameters {
		if param.Variadic {
			tc.addError(param.Name, "asm-backed function %s cannot be variadic", stmt.Name.Value)
			continue
		}
		paramType := tc.parseTypeExpression(param.Type)
		if paramType != nil && !boundary(paramType) {
			tc.addError(param.Name, "asm-backed function %s: parameter %s has type %s, which cannot cross the asm boundary in v1 (fixed-width integers, Bool, simd vectors)", stmt.Name.Value, param.Name.Value, paramType)
		}
	}
	if stmt.ReturnType != nil {
		returnType := tc.parseTypeExpression(stmt.ReturnType)
		_, isUnit := returnType.(*UnitType)
		_, isNever := returnType.(*NeverType)
		if returnType != nil && !isUnit && !isNever && !boundary(returnType) {
			tc.addError(stmt.ReturnType, "asm-backed function %s returns %s, which cannot cross the asm boundary in v1", stmt.Name.Value, returnType)
		}
	}
	tc.predeclareFunctionSignature(stmt)
}

func (tc *TypeChecker) checkExternFunction(stmt *ast.FunctionStatement) {
	if !ValidCSymbol(stmt.ExternSymbol) {
		d := tc.addTypeDiagnostic(stmt, CodeExternSymbolInvalid,
			fmt.Sprintf("extern symbol %q is not a C identifier", stmt.ExternSymbol))
		d.AddNote("the symbol is emitted into generated C source; only [A-Za-z_][A-Za-z0-9_]* is admitted")
		return
	}
	if stmt.Receiver != nil || len(stmt.TypeParams) > 0 {
		tc.addError(stmt, "extern binding %s cannot have a receiver or generic parameters", stmt.Name.Value)
		return
	}
	paramTypes := make([]Type, 0, len(stmt.Parameters))
	valid := true
	for _, param := range stmt.Parameters {
		if param.Variadic {
			tc.addError(param.Name, "extern binding %s cannot be variadic", stmt.Name.Value)
			valid = false
			continue
		}
		paramType := tc.parseTypeExpression(param.Type)
		if !tc.boundaryValue(paramType) {
			d := tc.addTypeDiagnostic(param.Name, CodeExternSignatureNotC,
				fmt.Sprintf("extern binding %s: parameter %s must have a c.* type or a proven-layout struct", stmt.Name.Value, param.Name.Value))
			d.AddNote("Oak scalars never cross the foreign boundary raw; convert explicitly at the call site. A declared struct whose fields are boundary types passes by value with its layout asserted (docs/spec/92-ffi.md section 2.3)")
			valid = false
			continue
		}
		paramTypes = append(paramTypes, paramType)
	}
	var returnType Type = &UnitType{}
	if stmt.ReturnType != nil {
		returnType = tc.parseTypeExpression(stmt.ReturnType)
		_, isUnit := returnType.(*UnitType)
		if !isUnit && !tc.boundaryValue(returnType) {
			d := tc.addTypeDiagnostic(stmt.ReturnType, CodeExternSignatureNotC,
				fmt.Sprintf("extern binding %s: return type must be a c.* type, a proven-layout struct, or ()", stmt.Name.Value))
			d.AddNote("Oak scalars never cross the foreign boundary raw; convert explicitly at the call site. A declared struct whose fields are boundary types returns by value with its layout asserted (docs/spec/92-ffi.md section 2.3)")
			valid = false
		}
	}
	if !valid {
		return
	}
	if tc.externFunctions == nil {
		tc.externFunctions = make(map[string]bool)
	}
	tc.externFunctions[stmt.Name.Value] = true
	tc.env.Set(stmt.Name.Value, Generalize(&FunctionType{
		Parameters: paramTypes,
		ReturnType: returnType,
	}, tc.env))
}

// boundaryValue reports whether a type may be an extern binding's parameter
// or return type: a c.* type, or a declared struct (or boundary tagged
// union) whose layout the backend asserts, passed by value
// (docs/spec/92-ffi.md section 2.3).
func (tc *TypeChecker) boundaryValue(typ Type) bool {
	switch t := typ.(type) {
	case *CType:
		return true
	case *RecordType:
		return tc.boundaryStruct(t, map[string]bool{})
	case *ADTType:
		return tc.boundaryTaggedUnion(t.Name, map[string]bool{})
	}
	return false
}

// BoundarySpanArgument recognizes `c.span_of(v)` / `c.span_mut_of(s)` in
// argument position (docs/spec/92-ffi.md section 2.5), returning the member
// and the operand. A local binding named `c` shadows the library, exactly as
// for every other library call.
func (tc *TypeChecker) BoundarySpanArgument(arg ast.Expression) (member string, operand ast.Expression, ok bool) {
	call, isCall := arg.(*ast.InvocationExpression)
	if !isCall {
		return "", nil, false
	}
	library, member, isLibrary := libraryAccess(call.Function)
	if !isLibrary || library != "c" || (member != "span_of" && member != "span_mut_of") {
		return "", nil, false
	}
	if _, bound := tc.env.Get("c"); bound {
		return "", nil, false
	}
	if len(call.Arguments) != 1 {
		return member, nil, true
	}
	return member, call.Arguments[0], true
}

// CStringArgument recognizes `c.cstr(v)` in argument position
// (docs/spec/92-ffi.md section 2.5.3), returning the operand. A local
// binding named `c` shadows the library, exactly as for every other library
// call.
func (tc *TypeChecker) CStringArgument(arg ast.Expression) (operand ast.Expression, ok bool) {
	call, isCall := arg.(*ast.InvocationExpression)
	if !isCall {
		return nil, false
	}
	library, member, isLibrary := libraryAccess(call.Function)
	if !isLibrary || library != "c" || member != "cstr" {
		return nil, false
	}
	if _, bound := tc.env.Get("c"); bound {
		return nil, false
	}
	if len(call.Arguments) != 1 {
		return nil, true
	}
	return call.Arguments[0], true
}

// checkCStringArgument validates one `c.cstr(v)` argument of an extern call
// (docs/spec/92-ffi.md section 2.5.3): the parameter at pos is `c.String`,
// and the operand is either a named read-only `[]u8` view — whose trailing
// NUL the backend checks at the call — or a string literal that ends in a
// NUL, checked here.
func (tc *TypeChecker) checkCStringArgument(arg ast.Expression, operand ast.Expression, parameters []Type, pos int) bool {
	if operand == nil {
		tc.addError(arg, "c.cstr takes exactly one []u8 view or string literal argument")
		return false
	}
	if pos >= len(parameters) {
		d := tc.addTypeDiagnostic(arg, CodeCStringArgument, "c.cstr must stand for a `c.String` parameter of the extern binding")
		d.AddNote("the extern's prototype declares the pointer C receives as c.String (docs/spec/92-ffi.md section 2.5.3)")
		return false
	}
	if str, isC := parameters[pos].(*CType); !isC || str.Name != "String" {
		d := tc.addTypeDiagnostic(arg, CodeCStringArgument,
			fmt.Sprintf("c.cstr must stand for a `c.String` parameter of the extern binding, got %s", parameters[pos]))
		d.AddNote("the extern's prototype declares the pointer C receives as c.String (docs/spec/92-ffi.md section 2.5.3)")
		return false
	}
	switch v := operand.(type) {
	case *ast.StringLiteral:
		if len(v.Value) == 0 || v.Value[len(v.Value)-1] != 0 {
			d := tc.addTypeDiagnostic(operand, CodeCStringArgument, "c.cstr literal is not NUL-terminated")
			d.AddHelp("end the literal with \\0, or construct it with c.String(\"...\"), which terminates the literal itself")
			return false
		}
		return true
	case *ast.Identifier:
		operandType := tc.checkExpression(v)
		if operandType == nil {
			return false
		}
		array, isArray := operandType.(*ArrayType)
		var element *PrimitiveType
		isPrim := false
		if isArray {
			element, isPrim = array.ElementType.(*PrimitiveType)
		}
		if !isArray || !array.IsSlice || !isPrim || (element.Name != "u8" && element.Name != "byte") {
			d := tc.addTypeDiagnostic(operand, CodeCStringArgument,
				fmt.Sprintf("c.cstr takes a read-only view []u8, got %s", operandType))
			d.AddNote("the view's last byte must be NUL; the backend checks it at the call and traps otherwise (docs/spec/92-ffi.md section 2.5.3)")
			return false
		}
		return true
	}
	d := tc.addTypeDiagnostic(operand, CodeCStringArgument, "c.cstr takes a named []u8 view binding or a string literal")
	d.AddHelp("bind the bytes first: text: []u8 = view(&buffer)")
	return false
}

// ArgvArgument recognizes `c.argv_of(bytes, slots)` in argument position
// (docs/spec/92-ffi.md section 2.5.6), returning both operands. A local
// binding named `c` shadows the library, as for every other library call.
func (tc *TypeChecker) ArgvArgument(arg ast.Expression) (bytes, slots ast.Expression, ok bool) {
	call, isCall := arg.(*ast.InvocationExpression)
	if !isCall {
		return nil, nil, false
	}
	library, member, isLibrary := libraryAccess(call.Function)
	if !isLibrary || library != "c" || member != "argv_of" {
		return nil, nil, false
	}
	if _, bound := tc.env.Get("c"); bound {
		return nil, nil, false
	}
	if len(call.Arguments) != 2 {
		return nil, nil, true
	}
	return call.Arguments[0], call.Arguments[1], true
}

// OutArgument recognizes `c.out(x)` in argument position (docs/spec/
// 92-ffi.md section 2.5.7), returning the operand.
func (tc *TypeChecker) OutArgument(arg ast.Expression) (operand ast.Expression, ok bool) {
	call, isCall := arg.(*ast.InvocationExpression)
	if !isCall {
		return nil, false
	}
	library, member, isLibrary := libraryAccess(call.Function)
	if !isLibrary || library != "c" || member != "out" {
		return nil, false
	}
	if _, bound := tc.env.Get("c"); bound {
		return nil, false
	}
	if len(call.Arguments) != 1 {
		return nil, true
	}
	return call.Arguments[0], true
}

// pointerParameter reports whether the parameter at pos is `c.Ptr`.
func pointerParameter(parameters []Type, pos int) bool {
	if pos >= len(parameters) {
		return false
	}
	ptr, isC := parameters[pos].(*CType)
	return isC && ptr.Name == "Ptr"
}

// checkArgvArgument validates one `c.argv_of(bytes, slots)` argument of an
// extern call (docs/spec/92-ffi.md section 2.5.6): the parameter at pos is
// `c.Ptr`; `bytes` is a named read-only `[]u8` view holding the
// NUL-terminated strings back to back, and `slots` a named writable
// `[*]c.Ptr` span the backend fills with each string's start pointer and a
// trailing NULL at the call. The terminator and the slot count are checked
// at the call, which traps naming the source position otherwise.
func (tc *TypeChecker) checkArgvArgument(arg ast.Expression, bytes, slots ast.Expression, parameters []Type, pos int) bool {
	if bytes == nil || slots == nil {
		tc.addError(arg, "c.argv_of takes exactly two arguments: a []u8 view of NUL-terminated strings and a [*]c.Ptr span of slots")
		return false
	}
	if !pointerParameter(parameters, pos) {
		got := "no parameter"
		if pos < len(parameters) {
			got = parameters[pos].String()
		}
		d := tc.addTypeDiagnostic(arg, CodeArgvArgument,
			fmt.Sprintf("c.argv_of must stand for a `c.Ptr` parameter of the extern binding, got %s", got))
		d.AddNote("the extern's prototype declares the argument vector C receives as c.Ptr (char *const argv[]) (docs/spec/92-ffi.md section 2.5.6)")
		return false
	}
	bytesIdent, bytesIsIdent := bytes.(*ast.Identifier)
	slotsIdent, slotsIsIdent := slots.(*ast.Identifier)
	if !bytesIsIdent || !slotsIsIdent {
		d := tc.addTypeDiagnostic(arg, CodeArgvArgument, "c.argv_of takes named bindings: a []u8 view and a [*]c.Ptr span")
		d.AddHelp("bind them first: text: []u8 = view(&buffer); slots: [*]c.Ptr = span(&pointers)")
		return false
	}
	bytesType := tc.checkExpression(bytesIdent)
	slotsType := tc.checkExpression(slotsIdent)
	if bytesType == nil || slotsType == nil {
		return false
	}
	bytesArray, bytesIsArray := bytesType.(*ArrayType)
	bytesIsU8 := false
	if bytesIsArray {
		if prim, isPrim := bytesArray.ElementType.(*PrimitiveType); isPrim {
			bytesIsU8 = prim.Name == "u8" || prim.Name == "byte"
		}
	}
	if !bytesIsArray || !bytesArray.IsSlice || !bytesIsU8 {
		d := tc.addTypeDiagnostic(bytes, CodeArgvArgument,
			fmt.Sprintf("c.argv_of takes a read-only view []u8 of NUL-terminated strings, got %s", bytesType))
		d.AddNote("every string in the view ends in NUL, the view's last byte included; the backend checks it at the call (docs/spec/92-ffi.md section 2.5.6)")
		return false
	}
	slotsArray, slotsIsArray := slotsType.(*ArrayType)
	slotsIsPtr := false
	if slotsIsArray {
		if elem, isC := slotsArray.ElementType.(*CType); isC {
			slotsIsPtr = elem.Name == "Ptr"
		}
	}
	if !slotsIsArray || !slotsArray.IsSpan || !slotsIsPtr {
		d := tc.addTypeDiagnostic(slots, CodeArgvArgument,
			fmt.Sprintf("c.argv_of takes a writable span [*]c.Ptr of pointer slots, got %s", slotsType))
		d.AddNote("the span needs one slot per string plus one for the trailing NULL; the backend checks the count at the call (docs/spec/92-ffi.md section 2.5.6)")
		return false
	}
	return true
}

// checkOutArgument validates one `c.out(x)` argument of an extern call
// (docs/spec/92-ffi.md section 2.5.7): the parameter at pos is `c.Ptr` and
// the operand a local binding of a `c.*` scalar type (never c.Ptr or
// c.String, which are not storage C may fill) or of a declared struct whose
// fields are boundary types. The foreign callee receives the binding's
// address for the duration of the call and may write through it.
func (tc *TypeChecker) checkOutArgument(arg ast.Expression, operand ast.Expression, parameters []Type, pos int) bool {
	if operand == nil {
		tc.addError(arg, "c.out takes exactly one local binding argument")
		return false
	}
	if !pointerParameter(parameters, pos) {
		got := "no parameter"
		if pos < len(parameters) {
			got = parameters[pos].String()
		}
		d := tc.addTypeDiagnostic(arg, CodeOutArgument,
			fmt.Sprintf("c.out must stand for a `c.Ptr` parameter of the extern binding, got %s", got))
		d.AddNote("the extern's prototype declares an out-parameter as c.Ptr; C writes the value through it (docs/spec/92-ffi.md section 2.5.7)")
		return false
	}
	ident, isIdent := operand.(*ast.Identifier)
	if !isIdent {
		d := tc.addTypeDiagnostic(operand, CodeOutArgument, "c.out takes a named local binding")
		d.AddHelp("declare the storage first: status: c.Int = c.Int(i32(0))")
		return false
	}
	if _, isGlobal := tc.globalOwners[ident.Value]; isGlobal {
		d := tc.addTypeDiagnostic(operand, CodeOutArgument,
			fmt.Sprintf("c.out takes a local binding, not the global %s", ident.Value))
		d.AddNote("static storage is written only by Oak code; copy the global into a local, pass that, and store it back")
		return false
	}
	operandType := tc.checkExpression(ident)
	if operandType == nil {
		return false
	}
	switch t := operandType.(type) {
	case *CType:
		if t.Name == "Ptr" || t.Name == "String" {
			d := tc.addTypeDiagnostic(operand, CodeOutArgument,
				fmt.Sprintf("c.out takes a c.* scalar or a boundary struct, got %s", operandType))
			d.AddNote("an opaque foreign pointer is not storage C fills; to receive a pointer, declare the out-parameter's target as c.Ptr and read it back through c.borrow (docs/spec/92-ffi.md section 2.7)")
			return false
		}
		return true
	case *RecordType:
		if tc.boundaryStruct(t, map[string]bool{}) {
			return true
		}
	}
	d := tc.addTypeDiagnostic(operand, CodeOutArgument,
		fmt.Sprintf("c.out takes a c.* scalar or a declared struct with boundary fields, got %s", operandType))
	d.AddNote("Oak scalars never cross the boundary raw (docs/spec/92-ffi.md section 2.3); declare the binding with the c.* type the callee writes, and convert after the call")
	return false
}

// boundarySpanElementTypes are the primitive element types with one meaning
// on both sides of the C boundary (docs/spec/92-ffi.md section 2.5.1):
// fixed-width integers, the IEEE binary32/binary64 types, and the f16/bf16
// storage formats, which cross as their uint16_t carriers
// (docs/spec/20-types.md section 11.3.8). Bool, tagged unions, and structs
// with proven layouts are admitted by boundarySpanElement.
var boundarySpanElementTypes = map[string]bool{
	"u8": true, "u16": true, "u32": true, "u64": true,
	"i8": true, "i16": true, "i32": true, "i64": true,
	"byte": true,
	"f32":  true, "f64": true, "f16": true, "bf16": true,
	"f8e4m3": true, "f8e5m2": true,
}

// boundarySpanElement reports whether an element type has one meaning on
// both sides of the C boundary: a whitelisted primitive, Bool, a boundary
// tagged union (section 2.6), or a declared struct whose fields are
// recursively such types (section 2.5.1). Everything else — semantic
// records without a committed representation, strings, views, generic
// shapes — is rejected, so C never receives a pointer to storage whose
// layout the backend did not assert.
func (tc *TypeChecker) boundarySpanElement(element Type, visiting map[string]bool) bool {
	switch element := element.(type) {
	case *PrimitiveType:
		return boundarySpanElementTypes[element.Name]
	case *BoolType:
		return true
	case *ADTType:
		return tc.boundaryTaggedUnion(element.Name, visiting)
	case *RecordType:
		return tc.boundaryStruct(element, visiting)
	}
	return false
}

// boundaryStruct reports whether a declared struct has one meaning on both
// sides of the C boundary: it is representation-committed (the struct
// keyword, so the backend emits it with C compile-time layout assertions),
// named, and every field is a boundary element type. Semantic records
// ({ x: u32 }) have no committed layout and are rejected.
func (tc *TypeChecker) boundaryStruct(record *RecordType, visiting map[string]bool) bool {
	if !record.Struct || record.Name == "" || record.Open || len(record.Fields) == 0 {
		return false
	}
	if visiting[record.Name] {
		return true
	}
	visiting[record.Name] = true
	for _, name := range record.orderedFieldNames() {
		if !tc.boundarySpanElement(record.Fields[name], visiting) {
			return false
		}
	}
	return true
}

// checkBoundarySpan validates one boundary-span argument of an extern call:
// the operand is a named read-only view (span_of) or writable span
// (span_mut_of) over an ABI-representable element type, and the parameters
// at pos and pos+1 are exactly c.Ptr and c.Size (section 2.5.1).
func (tc *TypeChecker) checkBoundarySpan(arg ast.Expression, member string, operand ast.Expression, parameters []Type, pos int) bool {
	if operand == nil {
		tc.addError(arg, "c.%s takes exactly one view or span argument", member)
		return false
	}
	pairOK := pos+1 < len(parameters)
	if pairOK {
		ptr, isPtr := parameters[pos].(*CType)
		size, isSize := parameters[pos+1].(*CType)
		pairOK = isPtr && isSize && ptr.Name == "Ptr" && size.Name == "Size"
	}
	if !pairOK {
		d := tc.addTypeDiagnostic(arg, CodeSpanParameterPair,
			fmt.Sprintf("c.%s must stand for a `c.Ptr, c.Size` parameter pair of the extern binding", member))
		d.AddNote("a boundary span occupies two consecutive parameter positions: the pointer, then the element count (docs/spec/92-ffi.md section 2.5.1)")
		return false
	}
	ident, isIdent := operand.(*ast.Identifier)
	if !isIdent {
		tc.addError(operand, "c.%s takes a named view or span binding", member)
		return false
	}
	operandType := tc.checkExpression(ident)
	if operandType == nil {
		return false
	}
	array, isArray := operandType.(*ArrayType)
	switch {
	case member == "span_of" && (!isArray || !array.IsSlice):
		tc.addError(operand, "c.span_of takes a read-only view []T, got %s", operandType)
		return false
	case member == "span_mut_of" && (!isArray || !array.IsSpan):
		tc.addError(operand, "c.span_mut_of takes a writable span [*]T, got %s", operandType)
		return false
	}
	if !tc.boundarySpanElement(array.ElementType, map[string]bool{}) {
		d := tc.addTypeDiagnostic(operand, CodeSpanElementNotABI,
			fmt.Sprintf("element type %s cannot cross the C boundary in a span", array.ElementType))
		d.AddNote("boundary spans carry fixed-width integers, floating-point types, Bool, declared structs whose fields are those, and tagged unions whose payloads are those; other element types have no single meaning on both sides (docs/spec/92-ffi.md sections 2.5.1 and 2.6)")
		return false
	}
	return true
}

// boundaryTaggedUnion reports whether a declared tagged union has one
// meaning on both sides of the C boundary (docs/spec/92-ffi.md section
// 2.6): it is not generic, and every payload is a fixed-width integer,
// Bool, or such a union. The emitted shape is a u32 tag followed by the
// payload union, with its layout asserted at C compile time.
func (tc *TypeChecker) boundaryTaggedUnion(name string, visiting map[string]bool) bool {
	adt, declared := tc.adtTypes[name]
	if !declared || len(adt.TypeParams) > 0 {
		return false
	}
	if visiting[name] {
		return true
	}
	visiting[name] = true
	for _, variant := range adt.Variants {
		switch {
		case variant.Payload == "":
		case boundarySpanElementTypes[variant.Payload], variant.Payload == "Bool":
		case tc.boundaryTaggedUnion(variant.Payload, visiting):
		default:
			return false
		}
	}
	return true
}

// foreignBorrowAccess recognizes the callee of an inbound buffer borrow,
// `c.borrow[T]` or `c.borrow_mut[T]` (docs/spec/92-ffi.md section 2.7): an
// index over the library member naming the element type.
func foreignBorrowAccess(fn ast.Expression) (member string, element ast.Expression, ok bool) {
	index, isIndex := fn.(*ast.IndexExpression)
	if !isIndex || index.Dot {
		return "", nil, false
	}
	library, member, isLibrary := libraryAccess(index.Left)
	if !isLibrary || library != "c" || (member != "borrow" && member != "borrow_mut" && member != "own") {
		return "", nil, false
	}
	return member, index.Index, true
}

// ForeignBorrowCall recognizes a call of `c.borrow[T](ptr, count)` or
// `c.borrow_mut[T](ptr, count)`, for the backends and the borrow checker.
func ForeignBorrowCall(call *ast.InvocationExpression) (member string, element ast.Expression, ok bool) {
	if call == nil {
		return "", nil, false
	}
	// `c.borrow_string(p)` (docs/spec/92-ffi.md section 2.7.1) names no
	// element type: the elements are the bytes of a NUL-terminated C
	// string, and the count comes from the terminator at runtime.
	if library, member, isLibrary := libraryAccess(call.Function); isLibrary && library == "c" && member == "borrow_string" {
		return member, nil, true
	}
	return foreignBorrowAccess(call.Function)
}

// checkForeignStringBorrow types `c.borrow_string(p)` (docs/spec/92-ffi.md
// section 2.7): inside an unsafe block, as the initializer of a named
// binding, a read-only `[]u8` view over the bytes of the NUL-terminated C
// string at `p`, excluding the terminator; the length is the terminator's
// offset, read at runtime. The trust contract is c.borrow's: the program
// asserts the string is terminated and stays valid for the block's extent.
func (tc *TypeChecker) checkForeignStringBorrow(expr *ast.InvocationExpression) Type {
	if tc.unsafeDepth == 0 {
		d := tc.addTypeDiagnostic(expr, CodeForeignBorrowPlacement,
			"c.borrow_string takes runtime-owned memory and is admitted only inside an unsafe block")
		d.AddNote("the program asserts that the pointer addresses a NUL-terminated string that stays valid for the block's extent (docs/spec/92-ffi.md section 2.7)")
		d.AddHelp("wrap the binding and its uses in unsafe { ... }")
	} else if tc.initializerUnderCheck != expr {
		d := tc.addTypeDiagnostic(expr, CodeForeignBorrowPlacement,
			"c.borrow_string must initialize a named binding, so the borrow it creates has a scope")
		d.AddHelp("bind it first: text: []u8 = c.borrow_string(ptr)")
	}
	if len(expr.Arguments) != 1 {
		tc.addError(expr, "c.borrow_string takes exactly one c.Ptr")
		return nil
	}
	ptrType := tc.checkExpression(expr.Arguments[0], &CType{Name: "Ptr"})
	if ptr, isC := ptrType.(*CType); ptrType != nil && (!isC || ptr.Name != "Ptr") {
		tc.addError(expr.Arguments[0], "c.borrow_string takes a c.Ptr, got %s", ptrType)
	}
	return &ArrayType{Length: -1, IsSlice: true, ElementType: &PrimitiveType{Name: "u8"}}
}

// checkForeignBorrow types an inbound buffer borrow (docs/spec/92-ffi.md
// section 2.7): inside an unsafe block, as the initializer of a named
// binding, `c.borrow[T](ptr, count)` is a read-only view `[]T` and
// `c.borrow_mut[T](ptr, count)` a writable span `[*]T` over `count`
// elements of runtime-owned memory at `ptr`. `T` is a boundary element type
// (section 2.5.1), `ptr` a `c.Ptr`, `count` a `u32`. The trust contract the
// program asserts is stated in the spec; here the placement is enforced so
// the borrow checker always has a binding to scope the borrow to.
func (tc *TypeChecker) checkForeignBorrow(expr *ast.InvocationExpression, member string, elementExpr ast.Expression) Type {
	if tc.unsafeDepth == 0 {
		d := tc.addTypeDiagnostic(expr, CodeForeignBorrowPlacement,
			fmt.Sprintf("c.%s takes runtime-owned memory and is admitted only inside an unsafe block", member))
		d.AddNote("the program asserts that the pointer addresses count elements of the element type, valid and unaliased for writes for the block's extent (docs/spec/92-ffi.md section 2.7)")
		d.AddHelp("wrap the binding and its uses in unsafe { ... }")
	} else if tc.initializerUnderCheck != expr {
		d := tc.addTypeDiagnostic(expr, CodeForeignBorrowPlacement,
			fmt.Sprintf("c.%s must initialize a named binding, so the borrow it creates has a scope", member))
		d.AddHelp("bind it first: v: []T = c." + member + "[T](ptr, count)")
	}
	if len(expr.Arguments) != 2 {
		tc.addError(expr, "c.%s takes a c.Ptr and a u32 element count", member)
		return nil
	}
	element := tc.parseTypeExpression(elementExpr)
	if element == nil {
		tc.addError(elementExpr, "c.%s: invalid element type", member)
		return nil
	}
	if !tc.boundarySpanElement(element, map[string]bool{}) {
		d := tc.addTypeDiagnostic(elementExpr, CodeSpanElementNotABI,
			fmt.Sprintf("element type %s cannot cross the C boundary in a borrowed buffer", element))
		d.AddNote("inbound buffers carry the element types of docs/spec/92-ffi.md section 2.5.1: fixed-width integers, floating-point types, Bool, declared structs whose fields are those, and tagged unions whose payloads are those")
		return nil
	}
	ptrType := tc.checkExpression(expr.Arguments[0], &CType{Name: "Ptr"})
	if ptr, isC := ptrType.(*CType); ptrType != nil && (!isC || ptr.Name != "Ptr") {
		tc.addError(expr.Arguments[0], "c.%s takes a c.Ptr first, got %s", member, ptrType)
	}
	u32Type := &PrimitiveType{Name: "u32"}
	countType := tc.checkExpression(expr.Arguments[1], u32Type)
	if prim, isPrim := countType.(*PrimitiveType); countType != nil && (!isPrim || prim.Name != "u32") {
		tc.addError(expr.Arguments[1], "c.%s takes a u32 element count second, got %s (lengths stay in u32 on the Oak side, docs/spec/92-ffi.md section 2.2)", member, countType)
	}
	switch member {
	case "borrow":
		return &ArrayType{Length: -1, IsSlice: true, ElementType: element}
	case "own":
		// An owner of runtime length (section 2.8): the binding borrows
		// it like an owned array until c.disown hands the memory back.
		return &BufferType{Element: element}
	}
	return &ArrayType{Length: -1, IsSpan: true, ElementType: element}
}

// checkForeignDisown types c.disown(b): the buffer's pointer, for the
// runtime to free or reuse; the borrow checker consumes the binding.
func (tc *TypeChecker) checkForeignDisown(expr *ast.InvocationExpression) Type {
	if len(expr.Arguments) != 1 {
		tc.addError(expr, "c.disown takes exactly one Buffer[T] binding")
		return nil
	}
	ident, isIdent := expr.Arguments[0].(*ast.Identifier)
	if !isIdent {
		tc.addError(expr.Arguments[0], "c.disown takes the Buffer[T] binding itself, not an expression")
		return nil
	}
	scheme, bound := tc.env.Get(ident.Value)
	if !bound || scheme == nil {
		tc.addError(ident, "undefined variable: %s", ident.Value)
		return nil
	}
	if _, isBuffer := scheme.Type.(*BufferType); !isBuffer {
		tc.addError(ident, "c.disown takes a Buffer[T] binding, got %s", scheme.Type)
		return nil
	}
	return &CType{Name: "Ptr"}
}

// exportOwner names the package a flattened top-level function belongs to
// for diagnostics: the module path the elaborator mangled into its internal
// name, or "the root package".
func exportOwner(fn *ast.FunctionStatement) string {
	if path, _, ok := modules.Demangle(fn.Name.Value); ok {
		return fmt.Sprintf("package %q", path)
	}
	return "the root package"
}

// implicitExportSymbol is the C symbol the backend gives a root package pub
// function without an explicit marker (codegen cFunctionName for a root
// program): every such function is exported as `oak_<name>`.
func implicitExportSymbol(fn *ast.FunctionStatement) string {
	return "oak_" + fn.Name.Value
}

// checkExportSymbols validates the program's C ABI exports
// (docs/spec/92-ffi.md section 2.9): every `export("symbol")` marker names
// a C identifier, marks a pub, non-generic, non-method, non-extern function,
// and no two exports of the program — explicit markers from any package and
// the root package's implicit `oak_<name>` exports — share a symbol. The
// check runs over the elaborated program, so dependency functions carry
// their mangled internal names and the marker is the only way they reach
// the header.
func (tc *TypeChecker) checkExportSymbols(program *ast.Program) {
	type owner struct {
		fn     *ast.FunctionStatement
		symbol string
	}
	// A declaration is identified by where it is written, not by the name
	// the elaborator gave it: the same source function is checked once in
	// the flattened program under its internal name and may be checked
	// again on its own, and neither pass may report it against itself.
	declaration := func(fn *ast.FunctionStatement) string {
		tok := fn.Name.Token
		return fmt.Sprintf("%s|%d|%d|%d", tok.SemanticContext, tok.Line, tok.Column, tok.ByteStart)
	}
	claimed := map[string]owner{}
	var explicit []*ast.FunctionStatement
	visited := map[*ast.FunctionStatement]bool{}
	for _, stmt := range program.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil || visited[fn] {
			continue
		}
		visited[fn] = true
		if fn.ExportSymbol != "" {
			explicit = append(explicit, fn)
			continue
		}
		// Root package pub functions are implicit exports; dependency pub
		// functions (mangled names) are not part of the C surface.
		if fn.Exported && fn.Receiver == nil && fn.ExternSymbol == "" && len(fn.TypeParams) == 0 {
			if _, _, mangled := modules.Demangle(fn.Name.Value); !mangled {
				claimed[implicitExportSymbol(fn)] = owner{fn: fn, symbol: implicitExportSymbol(fn)}
			}
		}
	}
	// Deterministic order: by symbol, then by internal name.
	sort.SliceStable(explicit, func(i, j int) bool {
		if explicit[i].ExportSymbol != explicit[j].ExportSymbol {
			return explicit[i].ExportSymbol < explicit[j].ExportSymbol
		}
		return explicit[i].Name.Value < explicit[j].Name.Value
	})
	for _, fn := range explicit {
		symbol := fn.ExportSymbol
		switch {
		case !ValidCSymbol(symbol):
			d := tc.addTypeDiagnostic(fn.Name, CodeExportInvalid,
				fmt.Sprintf("export symbol %q is not a C identifier", symbol))
			d.AddHelp("a C identifier starts with a letter or underscore and continues with letters, digits, and underscores")
			continue
		case !fn.Exported:
			d := tc.addTypeDiagnostic(fn.Name, CodeExportInvalid,
				fmt.Sprintf("export(%q) marks %s, which is not pub", symbol, fn.Name.Value))
			d.AddHelp("only a pub function has a C ABI surface; write `export(\"...\") pub name: ...`")
			continue
		case fn.Receiver != nil:
			tc.addTypeDiagnostic(fn.Name, CodeExportInvalid,
				fmt.Sprintf("export(%q) marks a method; only free functions have a C ABI shape", symbol))
			continue
		case fn.ExternSymbol != "":
			tc.addTypeDiagnostic(fn.Name, CodeExportInvalid,
				fmt.Sprintf("export(%q) marks an extern binding; the foreign symbol %q is already the C name", symbol, fn.ExternSymbol))
			continue
		case len(fn.TypeParams) != 0:
			tc.addTypeDiagnostic(fn.Name, CodeExportInvalid,
				fmt.Sprintf("export(%q) marks a generic template; export a concrete instantiation through a wrapper instead", symbol))
			continue
		}
		if prior, taken := claimed[symbol]; taken && declaration(prior.fn) != declaration(fn) {
			d := tc.addTypeDiagnostic(fn.Name, CodeExportSymbolConflict,
				fmt.Sprintf("export symbol %q is already used by %s in %s", symbol, prior.fn.Name.Value, exportOwner(prior.fn)))
			if prior.fn.ExportSymbol == "" {
				d.AddHelp(fmt.Sprintf("the root package's pub function %s is exported implicitly as %q; pick another symbol or rename the root function", prior.fn.Name.Value, symbol))
			} else {
				d.AddHelp(fmt.Sprintf("this export is in %s; C symbols are program-unique", exportOwner(fn)))
			}
			continue
		}
		claimed[symbol] = owner{fn: fn, symbol: symbol}
	}
}
