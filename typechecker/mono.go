package typechecker

// Monomorphization support (docs/spec/20-types.md, docs/spec/30-adts): the
// type checker is the single authority for which concrete instantiations of
// each generic ADT a program uses and which instantiation every variant
// expression and match was checked against. The backend consumes these
// records instead of guessing by variant name — resolution is decided where
// typing happens. Maintained alongside Oak.Monomorphization (Lean), which
// proves payload substitution preserves the variant structure.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// Instantiation identifies one concrete generic-ADT instantiation: the
// declared name plus its argument atoms in order.
type Instantiation struct {
	ADT  string
	Args []string
}

// MangledName is the instantiation's flat Oak-level name (the backend adds
// its usual oak_ prefix). Built only from parser-validated identifiers and
// the primitive table.
func (inst Instantiation) MangledName() string {
	if len(inst.Args) == 0 {
		return inst.ADT
	}
	return inst.ADT + "_" + strings.Join(inst.Args, "_")
}

// typeAtom flattens a concrete type argument into a name atom. Types the
// v1 backend cannot mangle (arrays, views, spans, functions, anonymous
// shapes, unresolved variables) report false, and the instantiation is not
// recorded — the backend then fails closed rather than guessing.
func typeAtom(argType Type) (string, bool) {
	switch t := argType.(type) {
	case *PrimitiveType:
		return normalizePrimitiveName(t.Name), true
	case *BoolType:
		return "Bool", true
	case *StringType:
		return "string", true
	case *ADTType:
		return t.Name, true
	case *RecordType:
		if t.Name != "" {
			return t.Name, true
		}
	case *GenericType:
		inner := make([]string, 0, len(t.TypeArgs))
		for _, arg := range t.TypeArgs {
			atom, ok := typeAtom(arg)
			if !ok {
				return "", false
			}
			inner = append(inner, atom)
		}
		return Instantiation{ADT: t.Name, Args: inner}.MangledName(), true
	}
	return "", false
}

// recordADTInstantiation notes a concrete instantiation and returns its
// mangled name. Unknown ADTs, empty argument lists, and unmangleable
// arguments record nothing.
func (tc *TypeChecker) recordADTInstantiation(name string, args []Type) (string, bool) {
	if len(args) == 0 {
		return "", false
	}
	atoms := make([]string, 0, len(args))
	for _, arg := range args {
		atom, ok := typeAtom(arg)
		if !ok {
			return "", false
		}
		atoms = append(atoms, atom)
	}
	inst := Instantiation{ADT: name, Args: atoms}
	mangled := inst.MangledName()
	if tc.adtInstantiations == nil {
		tc.adtInstantiations = make(map[string]Instantiation)
	}
	tc.adtInstantiations[mangled] = inst
	return mangled, true
}

// recordVariantResolution notes which instantiation a variant expression
// was checked against (called from checkVariantExpression with the
// expected-type context).
func (tc *TypeChecker) recordVariantResolution(expr *ast.VariantExpression, name string, args []Type) {
	if expr == nil {
		return
	}
	mangled, ok := tc.resolutionName(name, args)
	if !ok {
		return
	}
	if tc.variantResolutions == nil {
		tc.variantResolutions = make(map[string]string)
	}
	tc.variantResolutions[positionKey(expr.Token)] = mangled
}

// positionKey identifies a node by source position, so resolutions survive
// the lowering pass's node reconstruction.
func positionKey(tok token.Token) string {
	return fmt.Sprintf("%d:%d:%s", tok.Line, tok.Column, tok.Literal)
}

// recordMatchResolution notes which instantiation a match scrutinee has.
func (tc *TypeChecker) recordMatchResolution(match *ast.MatchExpression, name string, args []Type) {
	if match == nil {
		return
	}
	mangled, ok := tc.resolutionName(name, args)
	if !ok {
		return
	}
	if tc.matchResolutions == nil {
		tc.matchResolutions = make(map[string]string)
	}
	tc.matchResolutions[positionKey(match.Token)] = mangled
}

// resolutionName names the concrete type a construct was checked against:
// the declared name for a plain ADT, the mangled instantiation (recorded
// for emission) for a generic application.
func (tc *TypeChecker) resolutionName(name string, args []Type) (string, bool) {
	if len(args) == 0 {
		return name, true
	}
	return tc.recordADTInstantiation(name, args)
}

// ADTInstantiations returns every recorded concrete instantiation, sorted
// by mangled name for deterministic emission.
func (tc *TypeChecker) ADTInstantiations() []Instantiation {
	names := make([]string, 0, len(tc.adtInstantiations))
	for name := range tc.adtInstantiations {
		names = append(names, name)
	}
	sort.Strings(names)
	instantiations := make([]Instantiation, 0, len(names))
	for _, name := range names {
		instantiations = append(instantiations, tc.adtInstantiations[name])
	}
	return instantiations
}

// VariantResolution reports the mangled instantiation a variant expression
// was checked against, when one was recorded.
func (tc *TypeChecker) VariantResolution(expr *ast.VariantExpression) (string, bool) {
	mangled, ok := tc.variantResolutions[positionKey(expr.Token)]
	return mangled, ok
}

// MatchResolution reports the mangled instantiation of a match scrutinee,
// when one was recorded.
func (tc *TypeChecker) MatchResolution(match *ast.MatchExpression) (string, bool) {
	mangled, ok := tc.matchResolutions[positionKey(match.Token)]
	return mangled, ok
}
