package typechecker

// The compiler-known foreign-interface libraries: the `c` interface library
// and the `arm64` abstract-assembly instruction library.
// Implementation of docs/spec/92-ffi.md.

import (
	"fmt"
	"regexp"

	"github.com/SCKelemen/oak/ast"
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
}

// oakConversionCOperands is the reverse direction: which c members an Oak
// primitive constructor accepts. Only the total (value-preserving) rows are
// invertible; `c.Size` narrowing back to `u32` is deliberately absent.
var oakConversionCOperands = map[string][]string{
	"i8": {"Int8"}, "i16": {"Int16"}, "i32": {"Int32", "Int"}, "i64": {"Int64"},
	"u8": {"UInt8", "Char"}, "u16": {"UInt16"}, "u32": {"UInt32", "UInt"}, "u64": {"UInt64"},
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
}

// SimdShapes is the v1 vector catalog, shared with the backend and the
// interpreter (single authority for suffixes, lane types, and counts).
var SimdShapes = []SimdShape{
	{TypeName: "U8x16", Suffix: "u8x16", ElemName: "u8", Lanes: 16},
	{TypeName: "U16x8", Suffix: "u16x8", ElemName: "u16", Lanes: 8},
	{TypeName: "U32x4", Suffix: "u32x4", ElemName: "u32", Lanes: 4},
	{TypeName: "U64x2", Suffix: "u64x2", ElemName: "u64", Lanes: 2},
}

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
		return isType || member == "extern"
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
}

var conversionOperations = map[string]bool{
	"trunc": true, "saturating": true, "checked": true, "bits": true,
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
		return tc.checkCatalogCall(expr, "simd", member, simdOps,
			"the simd library has no operation simd.%s"), true
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
		if _, isC := paramType.(*CType); !isC {
			d := tc.addTypeDiagnostic(param.Name, CodeExternSignatureNotC,
				fmt.Sprintf("extern binding %s: parameter %s must have a c.* type", stmt.Name.Value, param.Name.Value))
			d.AddNote("Oak types never cross the foreign boundary raw; convert explicitly at the call site (docs/spec/92-ffi.md section 2.3)")
			valid = false
			continue
		}
		paramTypes = append(paramTypes, paramType)
	}
	var returnType Type = &UnitType{}
	if stmt.ReturnType != nil {
		returnType = tc.parseTypeExpression(stmt.ReturnType)
		_, isC := returnType.(*CType)
		_, isUnit := returnType.(*UnitType)
		if !isC && !isUnit {
			d := tc.addTypeDiagnostic(stmt.ReturnType, CodeExternSignatureNotC,
				fmt.Sprintf("extern binding %s: return type must be a c.* type or ()", stmt.Name.Value))
			d.AddNote("Oak types never cross the foreign boundary raw; convert explicitly at the call site (docs/spec/92-ffi.md section 2.3)")
			valid = false
		}
	}
	if !valid {
		return
	}
	tc.env.Set(stmt.Name.Value, Generalize(&FunctionType{
		Parameters: paramTypes,
		ReturnType: returnType,
	}, tc.env))
}
