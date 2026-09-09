package typechecker

// Module-system obligations discharged by the type checker
// (docs/spec/83-modules.md sections 6.2 and 6.3). The elaborator
// (compiler/modules.go) resolves names and visibility before checking; two
// judgments need types and therefore land here: opaque-type projection
// (only the declaring package may look inside a pub(opaque) type) and
// sealed-import member types (the declaration behind `alias.member` must
// have exactly the type the import's signature promises).

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/token"
)

const (
	// CodeOpaqueProjection rejects constructing, destructuring, matching,
	// or reading fields of a pub(opaque) type outside its declaring package
	// (Oak.Modules.Visibility.opaque_projection_local).
	CodeOpaqueProjection = "OAK-M0110"
	// CodeSignatureType rejects a sealed import whose member has a type
	// other than the one the signature promises.
	CodeSignatureType = "OAK-M0113"
)

// SignatureObligation asks the checker to verify that the declaration
// Internal has type Type; Member is the source spelling for diagnostics.
type SignatureObligation struct {
	Internal string
	Member   string
	Type     ast.Expression
	Node     ast.Node
	// TypeMember marks a shared type member (`Key: type = T`): the
	// declaration Internal must be the type T, not have it.
	TypeMember bool
}

// SetModuleContext hands the checker the elaborator's facts: the opaque
// types (internal name -> declaring package path) and the set of loaded
// package paths, which is how a token's SemanticContext is read back as a
// package identity.
func (tc *TypeChecker) SetModuleContext(opaque map[string]string, packages []string) {
	tc.opaqueTypes = opaque
	tc.packagePaths = map[string]bool{}
	for _, path := range packages {
		tc.packagePaths[path] = true
	}
}

// SetSealedOpaque records, per importing package (the root spelled ""),
// the types that a sealed import's `Name: type` member made abstract for
// that package: projections are rejected there even though the declaring
// package exported the type transparently (docs/spec/83-modules.md
// section 6.3).
func (tc *TypeChecker) SetSealedOpaque(sealed map[string]map[string]bool) {
	tc.sealedOpaque = sealed
}

// SetAbstractTypes registers the fresh abstract types of sealed imports:
// each fresh internal name is a nominal type distinct from every other type,
// whose values are introduced and eliminated only by the compiler-only
// coercions `__abstract_<fresh>` and `__concrete_<fresh>` at the sealed
// boundary (docs/spec/83-modules.md section 6.3).
func (tc *TypeChecker) SetAbstractTypes(abstract map[string]string) {
	tc.abstractTypes = abstract
}

// registerAbstractTypes gives each fresh abstract type a nominal identity
// derived from its underlying declaration: records become a same-shaped
// record under the fresh name (nominal identity is by name), ADTs a fresh
// ADT name sharing the definition. Anything else cannot be made abstract.
func (tc *TypeChecker) registerAbstractTypes() {
	names := make([]string, 0, len(tc.abstractTypes))
	for fresh := range tc.abstractTypes {
		names = append(names, fresh)
	}
	sort.Strings(names)
	for _, fresh := range names {
		underlying := tc.abstractTypes[fresh]
		if def, isADT := tc.adtTypes[underlying]; isADT {
			tc.adtTypes[fresh] = def
			continue
		}
		if named, ok := tc.env.GetType(underlying); ok {
			if record, isRecord := named.(*RecordType); isRecord {
				copy := *record
				copy.Name = fresh
				tc.env.SetType(fresh, &copy)
				continue
			}
		}
		tc.addTypeDiagnostic(nil, CodeSignatureType,
			fmt.Sprintf("abstract type member %s: %s must be a declared record or ADT to be sealed abstract", modules.DemangleText(fresh), modules.DemangleText(underlying)))
	}
}

// abstractType returns the fresh type's representation.
func (tc *TypeChecker) abstractType(fresh string) Type {
	if _, isADT := tc.adtTypes[fresh]; isADT {
		return &ADTType{Name: fresh}
	}
	if named, ok := tc.env.GetType(fresh); ok {
		return named
	}
	return nil
}

// checkAbstractCoercion types the boundary builtins. Reports whether callee
// was one.
func (tc *TypeChecker) checkAbstractCoercion(callee string, expr *ast.InvocationExpression) (Type, bool) {
	var fresh string
	toAbstract := false
	switch {
	case strings.HasPrefix(callee, "__abstract_"):
		fresh, toAbstract = strings.TrimPrefix(callee, "__abstract_"), true
	case strings.HasPrefix(callee, "__concrete_"):
		fresh = strings.TrimPrefix(callee, "__concrete_")
	default:
		return nil, false
	}
	underlying, known := tc.abstractTypes[fresh]
	if !known || len(expr.Arguments) != 1 {
		tc.addError(expr, "%s is not a sealed boundary of this program", callee)
		return nil, true
	}
	freshType := tc.abstractType(fresh)
	var underlyingType Type
	if _, isADT := tc.adtTypes[underlying]; isADT {
		underlyingType = &ADTType{Name: underlying}
	} else if named, ok := tc.env.GetType(underlying); ok {
		underlyingType = named
	}
	if freshType == nil || underlyingType == nil {
		return nil, true
	}
	want, result := underlyingType, freshType
	if !toAbstract {
		want, result = freshType, underlyingType
	}
	got := tc.checkExpression(expr.Arguments[0], want)
	if got == nil {
		return nil, true
	}
	if !got.Equals(want) {
		d := tc.addTypeDiagnostic(expr, CodeSignatureType,
			fmt.Sprintf("sealed boundary expects %s, got %s", modules.DemangleText(fmt.Sprint(want)), modules.DemangleText(fmt.Sprint(got))))
		d.AddNote("values cross a sealed import only through its signature's declared types")
		return nil, true
	}
	return result, true
}

// packageOf reads the package that owns a token. Tokens of imported
// packages are stamped with their package path (optionally followed by
// `|<instantiation>` for monomorphized clones); everything else belongs to
// the root package, spelled "".
func (tc *TypeChecker) packageOf(tok token.Token) string {
	context := tok.SemanticContext
	if index := strings.IndexByte(context, '|'); index >= 0 {
		context = context[:index]
	}
	if index := strings.IndexByte(context, '#'); index >= 0 {
		context = context[:index]
	}
	if tc.packagePaths[context] {
		return context
	}
	return ""
}

// opaqueOwner reports the declaring package of an opaque type, looking
// through generic instantiations to their template.
func (tc *TypeChecker) opaqueOwner(typeName string) (string, bool) {
	if owner, ok := tc.opaqueTypes[typeName]; ok {
		return owner, true
	}
	if inst, ok := tc.adtInstantiations[typeName]; ok {
		if owner, ok := tc.opaqueTypes[inst.ADT]; ok {
			return owner, true
		}
	}
	return "", false
}

// checkOpaqueProjection admits a projection (construction, field access,
// variant naming, matching) of typeName from the code that owns tok exactly
// when modules.ProjectionAllowed does. It returns false after reporting.
func (tc *TypeChecker) checkOpaqueProjection(tok token.Token, typeName string, node ast.Node, action string) bool {
	if len(tc.opaqueTypes) == 0 && len(tc.sealedOpaque) == 0 {
		return true
	}
	if users, sealed := tc.sealedOpaque[typeName]; sealed && users[tc.packageOf(tok)] {
		d := tc.addTypeDiagnostic(node, CodeOpaqueProjection,
			fmt.Sprintf("cannot %s type %s: this package sealed it as an abstract type member", action, modules.DemangleText(typeName)))
		d.AddNote("a sealed import's `Name: type` member hides the definition from the importing package")
		return false
	}
	owner, opaque := tc.opaqueOwner(typeName)
	if !opaque {
		return true
	}
	using := tc.packageOf(tok)
	if modules.ProjectionAllowed(owner, using, true) {
		return true
	}
	d := tc.addTypeDiagnostic(node, CodeOpaqueProjection,
		fmt.Sprintf("cannot %s opaque type %s outside its package %s", action, modules.DemangleText(typeName), owner))
	d.AddNote("pub(opaque) exports the type name only; its fields and variants are private to the declaring package")
	d.AddHelp(fmt.Sprintf("call a pub function of package %s that %ss the value for you", owner, strings.TrimSuffix(action, "e")))
	return false
}

// CheckSignatureObligations verifies sealed-import member types after the
// program has been checked: the declaration's scheme, instantiated, must
// equal the signature's type exactly (no widening, no narrowing —
// docs/spec/25-type-inference.md section 4).
func (tc *TypeChecker) CheckSignatureObligations(obligations []SignatureObligation) {
	for _, obligation := range obligations {
		if obligation.TypeMember {
			tc.checkSharedTypeMember(obligation)
			continue
		}
		scheme, bound := tc.env.Get(obligation.Internal)
		if !bound || scheme == nil {
			tc.addTypeDiagnostic(obligation.Node, CodeSignatureType,
				fmt.Sprintf("signature member %s has no checked declaration", obligation.Member))
			continue
		}
		want := tc.parseTypeExpression(obligation.Type)
		if want == nil {
			continue
		}
		got := Instantiate(scheme, NewUnifier())
		if got == nil || !got.Equals(want) {
			d := tc.addTypeDiagnostic(obligation.Node, CodeSignatureType,
				fmt.Sprintf("signature member %s has type %s, but the signature requires %s", obligation.Member, modules.DemangleText(fmt.Sprint(got)), modules.DemangleText(fmt.Sprint(want))))
			d.AddNote("a sealed import checks the package against the signature exactly; the declaration must have the promised type")
		}
	}
}

// checkSharedTypeMember verifies `Key: type = T`: the package's type is T.
func (tc *TypeChecker) checkSharedTypeMember(obligation SignatureObligation) {
	want := tc.parseTypeExpression(obligation.Type)
	if want == nil {
		return
	}
	var got Type
	if _, isADT := tc.adtTypes[obligation.Internal]; isADT {
		got = &ADTType{Name: obligation.Internal}
	} else if named, ok := tc.env.GetType(obligation.Internal); ok {
		got = named
	} else {
		got = &ADTType{Name: obligation.Internal}
	}
	if !got.Equals(want) {
		d := tc.addTypeDiagnostic(obligation.Node, CodeSignatureType,
			fmt.Sprintf("signature type member %s is %s, but the signature shares it as %s", obligation.Member, modules.DemangleText(fmt.Sprint(got)), modules.DemangleText(fmt.Sprint(want))))
		d.AddNote("`Name: type = T` requires the package's type to be exactly T")
	}
}
