package typechecker

import (
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"hash"
	"strconv"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

const (
	checkedScalarGlobalRegionProposition = "checked.scalar-global-region"
	checkedScalarGlobalWriteProposition  = "checked.scalar-global-write"
)

// ScalarGlobalRegion is the checked identity of one ordinary mutable scalar
// global. Name is the elaborator's exact internal binding name. ID also binds
// that name and type to the declaration's semantic source position, so a
// downstream memory optimization cannot manufacture region identity from a
// source spelling alone.
type ScalarGlobalRegion struct {
	ID               string
	Name             string
	Type             string
	DeclarationScope string
	Provenance       string
	Witness          string
}

// ScalarGlobalWriteProof is the checked authority for one direct assignment
// to a ScalarGlobalRegion. The access ID is source-site-specific while
// RegionID is stable across every write to the same declaration.
type ScalarGlobalWriteProof struct {
	ID           string
	Proposition  string
	RegionID     string
	Global       string
	Type         string
	Scope        string
	Provenance   string
	Witness      string
	Dependencies []string
}

// scalarGlobalDeclaration keeps provisional forward declarations private.
// A function may be checked before an annotated global that it writes, but no
// provisional fact becomes authority unless that exact declaration later
// checks successfully.
type scalarGlobalDeclaration struct {
	declaration *ast.VariableDeclaration
	region      ScalarGlobalRegion
	checked     bool
}

// ScalarGlobalRegion returns checked region authority for the exact
// elaborated global name. Local bindings and unsupported storage have no
// entry.
func (tc *TypeChecker) ScalarGlobalRegion(name string) (ScalarGlobalRegion, bool) {
	if tc == nil {
		return ScalarGlobalRegion{}, false
	}
	declaration, ok := tc.scalarGlobalDeclarations[name]
	if !ok || declaration == nil || !declaration.checked || declaration.region.ID == "" {
		return ScalarGlobalRegion{}, false
	}
	return declaration.region, true
}

// ScalarGlobalRegions returns a defensive authority set keyed by opaque
// region ID.
func (tc *TypeChecker) ScalarGlobalRegions() map[string]ScalarGlobalRegion {
	out := map[string]ScalarGlobalRegion{}
	if tc == nil {
		return out
	}
	for _, declaration := range tc.scalarGlobalDeclarations {
		if declaration == nil || !declaration.checked || declaration.region.ID == "" {
			continue
		}
		out[declaration.region.ID] = declaration.region
	}
	return out
}

// ScalarGlobalWriteProof returns checked write authority for the assignment
// whose ast.AssignmentStatement.Token is tok (the assigned identifier token,
// not the '=' token). A proof whose provisional declaration failed checking
// or whose whole program has a type error is refused.
func (tc *TypeChecker) ScalarGlobalWriteProof(tok token.Token) (ScalarGlobalWriteProof, bool) {
	if tc == nil || (tc.diagnostics != nil && len(tc.diagnostics.Errors()) != 0) {
		return ScalarGlobalWriteProof{}, false
	}
	proof, ok := tc.scalarGlobalWrites[positionKey(tok)]
	if !ok || proof.ID == "" {
		return ScalarGlobalWriteProof{}, false
	}
	region, ok := tc.ScalarGlobalRegion(proof.Global)
	if !ok || region.ID != proof.RegionID || region.Type != proof.Type {
		return ScalarGlobalWriteProof{}, false
	}
	return copyScalarGlobalWriteProof(proof), true
}

// ScalarGlobalWriteProofs returns a defensive authority set keyed by opaque
// access proof ID.
func (tc *TypeChecker) ScalarGlobalWriteProofs() map[string]ScalarGlobalWriteProof {
	out := map[string]ScalarGlobalWriteProof{}
	if tc == nil {
		return out
	}
	for key := range tc.scalarGlobalWrites {
		proof, ok := tc.ScalarGlobalWriteProof(token.Token{
			SemanticContext: key.context,
			Line:            key.line,
			Column:          key.column,
			Literal:         key.literal,
		})
		if ok {
			out[proof.ID] = proof
		}
	}
	return out
}

func copyScalarGlobalWriteProof(proof ScalarGlobalWriteProof) ScalarGlobalWriteProof {
	proof.Dependencies = append([]string(nil), proof.Dependencies...)
	return proof
}

// resetScalarGlobalWriteAuthority starts one whole-program checking pass. The
// TypeChecker is reusable, so authority from a prior AST must never leak into
// a later program.
func (tc *TypeChecker) resetScalarGlobalWriteAuthority() {
	tc.scalarGlobalDeclarations = make(map[string]*scalarGlobalDeclaration)
	tc.scalarGlobalWrites = make(map[tokenKey]ScalarGlobalWriteProof)
}

// provisionScalarGlobalDeclaration records an exact top-level declaration
// candidate. It admits only the first MemorySSA slice: ordinary default
// storage containing Bool or a fixed-width 8/16/32/64-bit integer.
func (tc *TypeChecker) provisionScalarGlobalDeclaration(decl *ast.VariableDeclaration, typ Type) {
	if tc == nil || decl == nil || decl.Name == nil || decl.Section != "" || decl.Measured != nil || decl.Threadgroup {
		return
	}
	if _, targetConstant := TargetConstantCall(decl.Value); targetConstant {
		return
	}
	typeName, ok := scalarGlobalMemoryTypeName(typ)
	if !ok {
		return
	}
	if existing := tc.scalarGlobalDeclarations[decl.Name.Value]; existing != nil {
		return
	}
	key := positionKey(decl.Name.Token)
	region := ScalarGlobalRegion{
		Name:             decl.Name.Value,
		Type:             typeName,
		DeclarationScope: fmtScope(key),
		Provenance:       "checked",
		Witness:          checkedScalarGlobalRegionProposition,
	}
	region.ID = checkedScalarGlobalRegionID(key, region)
	tc.scalarGlobalDeclarations[region.Name] = &scalarGlobalDeclaration{
		declaration: decl,
		region:      region,
	}
}

// finishScalarGlobalDeclaration confirms only the exact declaration that was
// provisioned. Inferred top-level scalars are introduced here once their type
// is known; they cannot be referenced before their declaration.
func (tc *TypeChecker) finishScalarGlobalDeclaration(decl *ast.VariableDeclaration, checked bool) {
	if tc == nil || decl == nil || decl.Name == nil {
		return
	}
	authority := tc.scalarGlobalDeclarations[decl.Name.Value]
	if authority == nil && checked && tc.globalEnv != nil {
		if scheme, ok := tc.globalEnv.Get(decl.Name.Value); ok && scheme != nil {
			tc.provisionScalarGlobalDeclaration(decl, scheme.Type)
			authority = tc.scalarGlobalDeclarations[decl.Name.Value]
		}
	}
	if authority != nil && authority.declaration == decl {
		authority.checked = checked
	}
}

// recordScalarGlobalWrite records a direct write only when its RHS already
// has the region's exact representation type. Ordinary assignability is
// intentionally broader (for widening and refinement erasure); those writes
// remain valid Oak but are not authority for this initial memory lowering.
func (tc *TypeChecker) recordScalarGlobalWrite(stmt *ast.AssignmentStatement, valueType Type) {
	if tc == nil || stmt == nil || stmt.Name == nil {
		return
	}
	declaration := tc.scalarGlobalDeclarations[stmt.Name.Value]
	if declaration == nil || declaration.region.ID == "" || !tc.resolvesScalarGlobalDeclaration(stmt.Name.Value, declaration) {
		return
	}
	typeName, exactScalar := scalarGlobalMemoryTypeName(valueType)
	if !exactScalar || typeName != declaration.region.Type {
		return
	}
	key := positionKey(stmt.Token)
	proof := ScalarGlobalWriteProof{
		Proposition: checkedScalarGlobalWriteProposition,
		RegionID:    declaration.region.ID,
		Global:      declaration.region.Name,
		Type:        declaration.region.Type,
		Scope:       fmtScope(key),
		Provenance:  "checked",
		Witness:     checkedScalarGlobalWriteProposition,
		Dependencies: []string{
			"region=" + declaration.region.ID,
			"type=" + declaration.region.Type,
		},
	}
	proof.ID = checkedScalarGlobalWriteProofID(key, proof)
	if tc.scalarGlobalWrites == nil {
		tc.scalarGlobalWrites = make(map[tokenKey]ScalarGlobalWriteProof)
	}
	tc.scalarGlobalWrites[key] = proof
}

// resolvesScalarGlobalDeclaration proves that normal lexical lookup reaches
// the global frame before any same-named local frame. Oak rejects shadowing,
// but this check makes the authority robust to malformed/recovery ASTs and to
// future changes in the surface shadowing rule.
func (tc *TypeChecker) resolvesScalarGlobalDeclaration(name string, declaration *scalarGlobalDeclaration) bool {
	if tc == nil || declaration == nil || declaration.declaration == nil || tc.globalEnv == nil {
		return false
	}
	for env := tc.env; env != nil; env = env.outer {
		if _, boundHere := env.store[name]; !boundHere {
			continue
		}
		return env == tc.globalEnv && tc.scalarGlobalDeclarations[name] == declaration
	}
	return false
}

func scalarGlobalMemoryTypeName(typ Type) (string, bool) {
	switch concrete := typ.(type) {
	case *BoolType:
		return "Bool", true
	case *PrimitiveType:
		if concrete.Refinement != "" {
			return "", false
		}
		name := normalizePrimitiveName(concrete.Name)
		switch name {
		case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64":
			return name, true
		}
	}
	return "", false
}

func checkedScalarGlobalRegionID(key tokenKey, region ScalarGlobalRegion) string {
	digest := sha256.New()
	writeScalarGlobalProofPart(digest,
		"oak.checked-scalar-global-region.v1",
		key.context,
		strconv.Itoa(key.line),
		strconv.Itoa(key.column),
		key.literal,
		region.Name,
		region.Type,
		region.DeclarationScope,
		region.Provenance,
		region.Witness,
	)
	return hex.EncodeToString(digest.Sum(nil))
}

func checkedScalarGlobalWriteProofID(key tokenKey, proof ScalarGlobalWriteProof) string {
	digest := sha256.New()
	writeScalarGlobalProofPart(digest,
		"oak.checked-scalar-global-write.v1",
		key.context,
		strconv.Itoa(key.line),
		strconv.Itoa(key.column),
		key.literal,
		proof.Proposition,
		proof.RegionID,
		proof.Global,
		proof.Type,
		proof.Scope,
		proof.Provenance,
		proof.Witness,
	)
	for _, dependency := range proof.Dependencies {
		writeScalarGlobalProofPart(digest, dependency)
	}
	return hex.EncodeToString(digest.Sum(nil))
}

func writeScalarGlobalProofPart(digest hash.Hash, values ...string) {
	for _, value := range values {
		var length [8]byte
		binary.BigEndian.PutUint64(length[:], uint64(len(value)))
		_, _ = digest.Write(length[:])
		_, _ = digest.Write([]byte(value))
	}
}
