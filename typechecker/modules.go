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

// packageOf reads the package that owns a token. Tokens of imported
// packages are stamped with their package path (optionally followed by
// `|<instantiation>` for monomorphized clones); everything else belongs to
// the root package, spelled "".
func (tc *TypeChecker) packageOf(tok token.Token) string {
	context := tok.SemanticContext
	if index := strings.IndexByte(context, '|'); index >= 0 {
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
	// The root package is spelled "" by packageOf but by its own path in
	// the opaque table only when it is not the root; the elaborator records
	// root-owned opaque types under the root's path, which packageOf never
	// returns, so compare through the packages set.
	using := tc.packageOf(tok)
	if modules.ProjectionAllowed(owner, using, true) || (using == "" && !tc.packagePaths[owner]) {
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
