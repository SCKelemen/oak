package modules

// MemberKind classifies a package-level declaration for signature
// conformance: a signature's `Name: type` member is satisfied only by a type
// declaration, a value member only by a function or value declaration.
type MemberKind uint8

const (
	// KindValue is a function, method, or top-level value binding.
	KindValue MemberKind = iota + 1
	// KindType is an ADT, record, struct, or alias declaration.
	KindType
	// KindInterface is an interface declaration.
	KindInterface
	// KindTag is a tag schema declaration.
	KindTag
)

func (k MemberKind) String() string {
	switch k {
	case KindValue:
		return "value"
	case KindType:
		return "type"
	case KindInterface:
		return "interface"
	case KindTag:
		return "tag"
	}
	return "unknown"
}

// Member is what a package knows about one of its package-level declarations.
type Member struct {
	Name string
	Kind MemberKind
	// Exported is true for declarations marked `pub`. Visibility is never
	// inferred from spelling (docs/spec/82-package-semver.md section 5).
	Exported bool
	// Opaque is true for `pub(opaque)` types: the name is exported, the
	// definition (fields, variants, representation) is not.
	Opaque bool
}

// Exports is a package's member table keyed by source name.
type Exports map[string]Member

// Signature is the member set a sealed import exposes
// (`h: Sig = import("p")`). A nil *Signature means the import is unsealed
// and exposes every exported member.
type Signature struct {
	Members map[string]MemberKind
}

// Outcome is the result of resolving `alias.name`.
type Outcome uint8

const (
	// Resolved: the member exists, is exported, and lies within the
	// signature when the import is sealed.
	Resolved Outcome = iota
	// NoSuchMember: the package declares nothing by that name.
	NoSuchMember
	// NotExported: the package declares the name without `pub`.
	NotExported
	// NotInSignature: the import is sealed and the signature omits the name.
	NotInSignature
)

// Lookup decides whether `alias.name` resolves through an import of a package
// with the given exports, sealed by sig when non-nil. The order of checks is
// the one the laws depend on: sealing narrows first, then existence, then
// visibility (Oak.Modules.Visibility). Private members are never reachable
// from another package (lookup_never_private); a sealed import never exposes
// a member outside its signature (lookup_sealed_subset); whatever resolves
// through a sealed import resolves identically through the unsealed one
// (lookup_sealed_narrows).
func Lookup(exports Exports, sig *Signature, name string) (Member, Outcome) {
	if sig != nil {
		if _, listed := sig.Members[name]; !listed {
			return Member{}, NotInSignature
		}
	}
	member, declared := exports[name]
	if !declared {
		return Member{}, NoSuchMember
	}
	if !member.Exported {
		return Member{}, NotExported
	}
	return member, Resolved
}

// Problem is one signature conformance failure.
type Problem struct {
	Name    string
	Outcome Outcome
	// Want and Got are set when the member exists but has the wrong kind.
	Want, Got MemberKind
}

// Conforms checks that a package's exports provide every member a signature
// demands, with the demanded kind (type members satisfied by type
// declarations, value members by values). Problems are returned in the
// signature's member-name order for deterministic diagnostics. Type
// equality of value members is the type checker's obligation, discharged
// after elaboration (compiler/modules.go); this decides membership and kind.
func Conforms(exports Exports, sig Signature, order []string) []Problem {
	var problems []Problem
	for _, name := range order {
		want := sig.Members[name]
		member, outcome := Lookup(exports, &sig, name)
		if outcome != Resolved {
			problems = append(problems, Problem{Name: name, Outcome: outcome})
			continue
		}
		if !kindSatisfies(want, member.Kind) {
			problems = append(problems, Problem{Name: name, Outcome: Resolved, Want: want, Got: member.Kind})
		}
	}
	return problems
}

func kindSatisfies(want, got MemberKind) bool {
	if want == KindType {
		return got == KindType
	}
	return got == want
}

// ProjectionAllowed decides whether code in package `using` may look inside
// a type declared by package `declaring`: construct its literals, read its
// fields, name or match its variants. Transparent types allow it everywhere;
// opaque types only inside the declaring package
// (Oak.Modules.Visibility.opaque_projection_local).
func ProjectionAllowed(declaring, using string, opaque bool) bool {
	return !opaque || declaring == using
}
