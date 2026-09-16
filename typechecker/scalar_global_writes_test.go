package typechecker

import (
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

func directAssignments(program *ast.Program) []*ast.AssignmentStatement {
	var out []*ast.AssignmentStatement
	if program == nil {
		return out
	}
	for _, statement := range program.Statements {
		function, ok := statement.(*ast.FunctionStatement)
		if !ok || function.Body == nil {
			continue
		}
		body, ok := function.Body.(*ast.BlockExpression)
		if !ok || body.Block == nil {
			continue
		}
		for _, bodyStatement := range body.Block.Statements {
			if assignment, ok := bodyStatement.(*ast.AssignmentStatement); ok {
				out = append(out, assignment)
			}
		}
	}
	return out
}

func checkScalarGlobalSource(t *testing.T, source string) (*TypeChecker, *ast.Program) {
	t.Helper()
	program := parseProgram(source)
	tc := setupTypeChecker(source)
	tc.CheckProgram(program)
	return tc, program
}

func TestScalarGlobalWriteAuthorityBindsDeclarationAndAccessSites(t *testing.T) {
	source := `
write: (): u32 {
  counter = u32(1)
  counter = u32(2)
  ready = true
  counter
}
counter: u32 = u32(0)
ready: Bool = false
`
	tc, program := checkScalarGlobalSource(t, source)
	if errs := tc.Errors(); len(errs) != 0 {
		t.Fatalf("valid scalar-global writes rejected: %v", errs)
	}
	assignments := directAssignments(program)
	if len(assignments) != 3 {
		t.Fatalf("assignments = %d, want 3", len(assignments))
	}

	first, ok := tc.ScalarGlobalWriteProof(assignments[0].Token)
	if !ok || first.ID == "" || first.Proposition != checkedScalarGlobalWriteProposition ||
		first.Global != "counter" || first.Type != "u32" || first.Provenance != "checked" ||
		first.Witness != checkedScalarGlobalWriteProposition || len(first.Dependencies) != 2 {
		t.Fatalf("first write proof = %+v, ok=%v", first, ok)
	}
	second, ok := tc.ScalarGlobalWriteProof(assignments[1].Token)
	if !ok || second.ID == first.ID || second.RegionID != first.RegionID {
		t.Fatalf("site/region identities: first=%+v second=%+v ok=%v", first, second, ok)
	}
	ready, ok := tc.ScalarGlobalWriteProof(assignments[2].Token)
	if !ok || ready.RegionID == first.RegionID || ready.Type != "Bool" {
		t.Fatalf("ready write proof = %+v, ok=%v", ready, ok)
	}
	region, ok := tc.ScalarGlobalRegion("counter")
	if !ok || region.ID != first.RegionID || region.Name != "counter" || region.Type != "u32" ||
		region.DeclarationScope == "" || region.Provenance != "checked" {
		t.Fatalf("counter region = %+v, ok=%v", region, ok)
	}

	// Both authority collection APIs are copies, including nested slices.
	first.Dependencies[0] = "mutated"
	writes := tc.ScalarGlobalWriteProofs()
	writes[second.ID] = ScalarGlobalWriteProof{}
	delete(writes, ready.ID)
	regions := tc.ScalarGlobalRegions()
	regions[region.ID] = ScalarGlobalRegion{}
	again, _ := tc.ScalarGlobalWriteProof(assignments[0].Token)
	regionAgain, _ := tc.ScalarGlobalRegion("counter")
	if again.Dependencies[0] == "mutated" || again.ID == "" || regionAgain.ID == "" {
		t.Fatalf("caller mutated retained authority: write=%+v region=%+v", again, regionAgain)
	}

	// Identical source produces identical declaration and access identities.
	secondTC, secondProgram := checkScalarGlobalSource(t, source)
	secondAssignments := directAssignments(secondProgram)
	repeated, ok := secondTC.ScalarGlobalWriteProof(secondAssignments[0].Token)
	if !ok || repeated.ID != again.ID || repeated.RegionID != again.RegionID {
		t.Fatalf("authority is not deterministic: first=%+v repeated=%+v", again, repeated)
	}
}

func TestScalarGlobalWriteAuthorityFailsClosedOutsideExactSlice(t *testing.T) {
	tests := []struct {
		name   string
		source string
		mutate func(*ast.Program)
	}{
		{
			name: "local",
			source: `write: (): u32 {
  local: u32 = u32(0)
  local = u32(1)
  local
}`,
		},
		{
			name: "implicit widening",
			source: `wide: u16 = u16(0)
write: (small: u8): u16 {
  wide = small
  wide
}`,
		},
		{
			name: "refinement erasure",
			source: `Small: type = u16 where value < u16(8)
plain: u16 = u16(0)
write: (small: Small): u16 {
  plain = small
  plain
}`,
		},
		{
			name: "refined region",
			source: `Small: type = u16 where value < u16(8)
small: Small = Small(u16(0))
write: (): Small {
  small = Small(u16(1))
  small
}`,
		},
		{
			name: "sectioned",
			source: `counter: u32 (section: ".shared") = u32(0)
write: (): u32 {
  counter = u32(1)
  counter
}`,
		},
		{
			name: "measured",
			source: `counter: u32 (measured: 0, 8) = 1
write: (): u32 {
  counter = u32(2)
  counter
}`,
		},
		{
			name: "atomic",
			source: `counter: Atomic[u32]
write: (): u32 {
  counter = counter
  u32(0)
}`,
		},
		{
			name: "array",
			source: `items: [2]u32
write: (): u32 {
  items = items
  u32(0)
}`,
		},
		{
			name: "float",
			source: `level: f32 = 0.0
write: (): f32 {
  level = 1.0
  level
}`,
		},
		{
			name: "u128",
			source: `wide: u128
write: (): u128 {
  wide = u128(1)
  wide
}`,
		},
		{
			name: "threadgroup marker",
			source: `counter: u32 = u32(0)
write: (): u32 {
  counter = u32(1)
  counter
}`,
			mutate: func(program *ast.Program) {
				for _, statement := range program.Statements {
					if declaration, ok := statement.(*ast.VariableDeclaration); ok {
						declaration.Threadgroup = true
						return
					}
				}
			},
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			program := parseProgram(test.source)
			if test.mutate != nil {
				test.mutate(program)
			}
			tc := setupTypeChecker(test.source)
			tc.CheckProgram(program)
			assignments := directAssignments(program)
			if len(assignments) != 1 {
				t.Fatalf("assignments = %d, want 1 (parse errors may have changed the fixture)", len(assignments))
			}
			if proof, ok := tc.ScalarGlobalWriteProof(assignments[0].Token); ok {
				t.Fatalf("unsupported write acquired authority: %+v (checker errors: %v)", proof, tc.Errors())
			}
		})
	}
}

func TestScalarGlobalWriteAuthorityNilAndSourceSensitive(t *testing.T) {
	var checker *TypeChecker
	tok := token.Token{SemanticContext: "pkg", Line: 4, Column: 2, Literal: "counter"}
	if _, ok := checker.ScalarGlobalRegion("counter"); ok || len(checker.ScalarGlobalRegions()) != 0 {
		t.Fatal("nil checker returned scalar global region authority")
	}
	if _, ok := checker.ScalarGlobalWriteProof(tok); ok || len(checker.ScalarGlobalWriteProofs()) != 0 {
		t.Fatal("nil checker returned scalar global write authority")
	}

	region := ScalarGlobalRegion{
		Name: "counter", Type: "u32", DeclarationScope: "pkg:1:1",
		Provenance: "checked", Witness: checkedScalarGlobalRegionProposition,
	}
	firstKey := tokenKey{context: "pkg", line: 1, column: 1, literal: "counter"}
	secondKey := tokenKey{context: "pkg", line: 2, column: 1, literal: "counter"}
	region.ID = checkedScalarGlobalRegionID(firstKey, region)
	changed := region
	changed.ID = checkedScalarGlobalRegionID(secondKey, changed)
	if region.ID == changed.ID || reflect.DeepEqual(region, changed) {
		t.Fatalf("declaration position did not affect region identity: %+v %+v", region, changed)
	}
}

func TestScalarGlobalWriteAuthorityRequiresExactGlobalResolution(t *testing.T) {
	globalEnv := NewTypeEnvironment()
	globalEnv.SetType("counter", &PrimitiveType{Name: "u32"})
	localEnv := NewEnclosedTypeEnvironment(globalEnv)
	localEnv.SetType("counter", &PrimitiveType{Name: "u32"})
	declaration := &ast.VariableDeclaration{
		Token: token.Token{SemanticContext: "pkg", Line: 1, Column: 1, Literal: "counter"},
		Name:  &ast.Identifier{Token: token.Token{SemanticContext: "pkg", Line: 1, Column: 1, Literal: "counter"}, Value: "counter"},
	}
	region := ScalarGlobalRegion{ID: "global-region", Name: "counter", Type: "u32"}
	tc := &TypeChecker{
		env:       localEnv,
		globalEnv: globalEnv,
		scalarGlobalDeclarations: map[string]*scalarGlobalDeclaration{
			"counter": {declaration: declaration, region: region, checked: true},
		},
		scalarGlobalWrites: map[tokenKey]ScalarGlobalWriteProof{},
	}
	assignment := &ast.AssignmentStatement{
		Token: token.Token{SemanticContext: "pkg", Line: 4, Column: 3, Literal: "counter"},
		Name:  &ast.Identifier{Token: token.Token{SemanticContext: "pkg", Line: 4, Column: 3, Literal: "counter"}, Value: "counter"},
	}
	tc.recordScalarGlobalWrite(assignment, &PrimitiveType{Name: "u32"})
	if len(tc.scalarGlobalWrites) != 0 {
		t.Fatalf("same-named local resolved as global authority: %+v", tc.scalarGlobalWrites)
	}

	// The source rule rejects shadowing; a rejected whole program must not
	// expose a later assignment as checked write authority either.
	tc, program := checkScalarGlobalSource(t, `counter: u32 = u32(0)
write: (): u32 {
  counter: u32 = u32(1)
  counter = u32(2)
  counter
}`)
	if len(tc.Errors()) == 0 {
		t.Fatal("same-named local unexpectedly passed the no-shadowing rule")
	}
	assignments := directAssignments(program)
	if len(assignments) != 1 {
		t.Fatalf("assignments = %d, want 1", len(assignments))
	}
	if proof, ok := tc.ScalarGlobalWriteProof(assignments[0].Token); ok {
		t.Fatalf("rejected shadowing program exposed write authority: %+v", proof)
	}
}
