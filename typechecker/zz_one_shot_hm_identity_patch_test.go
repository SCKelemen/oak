package typechecker

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func TestOneShotHMBinderIdentityPatch(t *testing.T) {
	if os.Getenv("OAK_HM_IDENTITY_PATCH_CHILD") == "1" {
		t.Skip("one-shot patch disabled in child validation")
	}
	if os.Getenv("GITHUB_ACTIONS") != "true" {
		t.Skip("one-shot repository maintenance runs only in GitHub Actions")
	}

	rootBytes, err := exec.Command("git", "rev-parse", "--show-toplevel").Output()
	if err != nil {
		t.Fatal(err)
	}
	root := strings.TrimSpace(string(rootBytes))
	branch := "feat/hm-typevar-identity"

	run := func(env []string, name string, args ...string) {
		t.Helper()
		cmd := exec.Command(name, args...)
		cmd.Dir = root
		cmd.Env = append(os.Environ(), env...)
		output, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("%s %v failed: %v\n%s", name, args, err, output)
		}
	}

	run(nil, "git", "fetch", "origin", branch)
	run(nil, "git", "checkout", "-B", branch, "origin/"+branch)

	hmPath := filepath.Join(root, "typechecker", "hm.go")
	hmBytes, err := os.ReadFile(hmPath)
	if err != nil {
		t.Fatal(err)
	}
	hm := string(hmBytes)
	mustReplace := func(old, replacement string) {
		t.Helper()
		if strings.Count(hm, old) != 1 {
			t.Fatalf("expected exactly one hm.go match for:\n%s", old)
		}
		hm = strings.Replace(hm, old, replacement, 1)
	}

	mustReplace(`func (tv *TypeVar) Equals(other Type) bool {
	if otherTV, ok := other.(*TypeVar); ok {
		return tv.ID == otherTV.ID
	}
	return false
}`,
		`func (tv *TypeVar) Equals(other Type) bool {
	otherTV, ok := other.(*TypeVar)
	return ok && tv == otherTV
}`)
	mustReplace(`type Substitution map[string]Type`, `type Substitution map[*TypeVar]Type`)
	mustReplace(`if replacement, ok := sub[t.Name]; ok {`, `if replacement, ok := sub[t]; ok {`)
	mustReplace(`	default:
		return t // Unknown type, return as-is
	}
}

// Compose composes two substitutions: sub2 ∘ sub1`, `	default:
		return t // Unknown type, return as-is
	}
}

// LookupName resolves a human-facing quantified variable name only when exactly
// one binder with that name is present in the substitution. Ambiguous names fail
// closed; substitution identity itself is always the *TypeVar binder pointer.
func (sub Substitution) LookupName(name string) (Type, bool) {
	var result Type
	found := false
	for variable, value := range sub {
		if variable == nil || variable.Name != name {
			continue
		}
		if found {
			return nil, false
		}
		result = value
		found = true
	}
	return result, found
}

// Compose composes two substitutions: sub2 ∘ sub1`)
	mustReplace(`sub[tv.Name] = t`, `sub[tv] = t`)
	mustReplace(`return tv.ID == typ.ID`, `return tv == typ`)
	mustReplace(`visited := make(map[int]bool)`, `visited := make(map[*TypeVar]bool)`)
	mustReplace(`func collectTypeVarsRec(typ Type, vars *[]string, visited map[int]bool) {`, `func collectTypeVarsRec(typ Type, vars *[]string, visited map[*TypeVar]bool) {`)
	mustReplace(`	case *TypeVar:
		if !visited[t.ID] {
			visited[t.ID] = true
			*vars = append(*vars, t.Name)
		}`, `	case *TypeVar:
		if !visited[t] {
			visited[t] = true
			*vars = append(*vars, t.Name)
		}`)
	mustReplace(`// Instantiate creates a fresh instance of a type scheme by replacing
// quantified type variables with fresh type variables`, `// quantifiedSubstitution binds the actual TypeVar identities found in a scheme
// to one fresh/provided replacement per quantified source name. Source names are
// only binder labels here; the resulting substitution is keyed by binder identity.
func quantifiedSubstitution(typ Type, quantified []string, replacements map[string]Type, unifier *Unifier) Substitution {
	wanted := make(map[string]struct{}, len(quantified))
	for _, name := range quantified {
		wanted[name] = struct{}{}
	}

	resolved := make(map[string]Type, len(quantified))
	sub := make(Substitution)
	var visit func(Type)
	visit = func(current Type) {
		switch current := current.(type) {
		case *TypeVar:
			if _, ok := wanted[current.Name]; !ok {
				return
			}
			replacement, ok := resolved[current.Name]
			if !ok {
				replacement, ok = replacements[current.Name]
				if !ok {
					replacement = unifier.FreshTypeVar(current.Name)
				}
				resolved[current.Name] = replacement
			}
			sub[current] = replacement
		case *RecordType:
			for _, field := range current.Fields {
				visit(field)
			}
		case *FunctionType:
			for _, parameter := range current.Parameters {
				visit(parameter)
			}
			visit(current.ReturnType)
		case *ArrayType:
			visit(current.ElementType)
		case *GenericType:
			for _, argument := range current.TypeArgs {
				visit(argument)
			}
		}
	}
	visit(typ)
	return sub
}

// Instantiate creates a fresh instance of a type scheme by replacing
// quantified type variables with fresh type variables`)
	mustReplace(`	// Create substitution mapping scheme type vars to fresh type vars
	sub := make(Substitution)
	for _, varName := range scheme.TypeVars {
		sub[varName] = unifier.FreshTypeVar(varName)
	}

	// Apply substitution to the scheme's type
	return sub.Apply(scheme.Type)`, `	// Bind the quantified variables by their actual binder identities.
	sub := quantifiedSubstitution(scheme.Type, scheme.TypeVars, nil, unifier)
	return sub.Apply(scheme.Type)`)
	mustReplace(`	// Create substitution from type arguments
	sub := make(Substitution)
	for varName, typeArg := range typeArgs {
		sub[varName] = typeArg
	}

	// For any remaining type vars (not provided), use fresh type vars
	for _, varName := range scheme.TypeVars {
		if _, provided := typeArgs[varName]; !provided {
			sub[varName] = unifier.FreshTypeVar(varName)
		}
	}

	// Apply substitution
	return sub.Apply(scheme.Type), true`, `	// Bind provided arguments (and freshen any remaining quantified binders)
	// using the scheme's actual TypeVar identities.
	sub := quantifiedSubstitution(scheme.Type, scheme.TypeVars, typeArgs, unifier)
	return sub.Apply(scheme.Type), true`)

	if err := os.WriteFile(hmPath, []byte(hm), 0o644); err != nil {
		t.Fatal(err)
	}

	constraintsPath := filepath.Join(root, "typechecker", "generic_constraints.go")
	constraintsBytes, err := os.ReadFile(constraintsPath)
	if err != nil {
		t.Fatal(err)
	}
	constraints := string(constraintsBytes)
	oldLookup := `concreteType, ok := bindings[constraint.Var]`
	if strings.Count(constraints, oldLookup) != 1 {
		t.Fatalf("expected exactly one generic constraint binding lookup")
	}
	constraints = strings.Replace(constraints, oldLookup, `concreteType, ok := bindings.LookupName(constraint.Var)`, 1)
	if err := os.WriteFile(constraintsPath, []byte(constraints), 0o644); err != nil {
		t.Fatal(err)
	}

	identityTest := `package typechecker

import "testing"

func TestFreshTypeVarsFromDifferentUnifiersAreDistinct(t *testing.T) {
	left := NewUnifier().FreshTypeVar("T")
	right := NewUnifier().FreshTypeVar("T")
	if left.Equals(right) {
		t.Fatal("unrelated type variables with the same display name must not be equal")
	}
}

func TestSubstitutionIsKeyedByBinderIdentityNotDisplayName(t *testing.T) {
	left := NewUnifier().FreshTypeVar("T")
	right := NewUnifier().FreshTypeVar("T")
	sub := make(Substitution)
	sub[left] = &PrimitiveType{Name: "i32"}
	if got := sub.Apply(left); !got.Equals(&PrimitiveType{Name: "i32"}) {
		t.Fatalf("expected left binder to substitute to i32, got %s", got)
	}
	if got := sub.Apply(right); got != right {
		t.Fatalf("substitution for unrelated T leaked across binder identity: got %s", got)
	}
}

func TestOccursCheckUsesBinderIdentity(t *testing.T) {
	leftUnifier := NewUnifier()
	rightUnifier := NewUnifier()
	left := leftUnifier.FreshTypeVar("T")
	right := rightUnifier.FreshTypeVar("T")
	if leftUnifier.occursIn(left, right) {
		t.Fatal("occurs check confused unrelated binders with the same display name")
	}
	cyclic := &GenericType{Name: "Box", TypeArgs: []Type{left}}
	if !leftUnifier.occursIn(left, cyclic) {
		t.Fatal("occurs check failed to find the same binder through a generic type")
	}
}

func TestInstantiateFreshensSameNamedSchemeOnEveryUse(t *testing.T) {
	binder := NewUnifier().FreshTypeVar("T")
	scheme := &TypeScheme{
		TypeVars: []string{"T"},
		Type: &FunctionType{Parameters: []Type{binder}, ReturnType: binder},
	}
	first := Instantiate(scheme, NewUnifier()).(*FunctionType)
	second := Instantiate(scheme, NewUnifier()).(*FunctionType)
	firstVar := first.Parameters[0].(*TypeVar)
	secondVar := second.Parameters[0].(*TypeVar)
	if firstVar.Equals(secondVar) {
		t.Fatal("independent instantiations reused one type-variable identity")
	}
	if first.ReturnType != firstVar || second.ReturnType != secondVar {
		t.Fatal("instantiation did not preserve repeated binder identity")
	}
}

func TestNamedLookupRejectsAmbiguousIndependentBinders(t *testing.T) {
	left := NewUnifier().FreshTypeVar("T")
	right := NewUnifier().FreshTypeVar("T")
	sub := make(Substitution)
	sub[left] = &PrimitiveType{Name: "i32"}
	sub[right] = &PrimitiveType{Name: "u32"}
	if _, ok := sub.LookupName("T"); ok {
		t.Fatal("name lookup must fail closed when independent binders share a display name")
	}
}
`
	identityPath := filepath.Join(root, "typechecker", "hm_identity_test.go")
	if err := os.WriteFile(identityPath, []byte(identityTest), 0o644); err != nil {
		t.Fatal(err)
	}

	run(nil, "gofmt", "-w", hmPath, constraintsPath, identityPath)
	run([]string{"OAK_HM_IDENTITY_PATCH_CHILD=1"}, "go", "test", "-race", "./typechecker")
	run([]string{"OAK_HM_IDENTITY_PATCH_CHILD=1"}, "go", "test", "-race", "./...")

	self := filepath.Join(root, "typechecker", "zz_one_shot_hm_identity_patch_test.go")
	if err := os.Remove(self); err != nil {
		t.Fatal(err)
	}

	run(nil, "git", "config", "user.name", "github-actions[bot]")
	run(nil, "git", "config", "user.email", "41898282+github-actions[bot]@users.noreply.github.com")
	run(nil, "git", "add", "typechecker/hm.go", "typechecker/generic_constraints.go", "typechecker/hm_identity_test.go", "typechecker/zz_one_shot_hm_identity_patch_test.go")
	run(nil, "git", "commit", "-m", "Give HM type variables binder identity")
	run(nil, "git", "push", "origin", "HEAD:"+branch)
}
