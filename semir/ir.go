package semir

// Module is Oak's checked semantic representation. Syntax, executable lowering,
// verification backends, schema tooling, and documentation should project from
// this model rather than independently reconstructing semantic facts.
type Module struct {
	Definitions []Definition
	Protocols   []Protocol
	Allocators  []Allocator
}

// Definition keeps Oak's five semantic axes orthogonal. A declaration can use
// only the axes it needs, but a fact should have one authoritative home.
type Definition struct {
	Name           string
	Type           Type
	Representation Representation
	Authority      Authority
	Propositions   []Proposition
	Protocol       string
	Attributes     []Attribute
}

// Type describes what a value means, independently of how it is represented.
type Type struct {
	Kind       TypeKind
	Base       string
	Parameters []TypeParameter
	Fields     []Field
	Variants   []Variant
	Methods    []Method
}

type TypeKind string

const (
	TypeInvalid   TypeKind = ""
	TypeScalar    TypeKind = "scalar"
	TypeAlias     TypeKind = "alias"
	TypeRecord    TypeKind = "record"
	TypeSum       TypeKind = "sum"
	TypeFunction  TypeKind = "function"
	TypeInterface TypeKind = "interface"
	TypeOpaque    TypeKind = "opaque"
)

type TypeParameter struct {
	Name       string
	Constraint string
	Phantom    bool
}

type Field struct {
	Name string
	Type string
}

type Variant struct {
	Name    string
	Payload string
}

type Method struct {
	Name       string
	Receiver   string
	Parameters []Field
	Return     string
}

// Representation describes the bits/layout chosen for a semantic type. Empty
// Representation means the declaration has no representation constraint yet.
type Representation struct {
	Kind       RepresentationKind
	Bits       uint16
	Size       uint32
	Alignment  uint32
	Endianness Endianness
	Fields     []FieldLayout
	Tag        *TagLayout
}

type RepresentationKind string

const (
	RepresentationUnspecified RepresentationKind = ""
	RepresentationMachineInt  RepresentationKind = "machine-int"
	RepresentationFloat       RepresentationKind = "float"
	RepresentationPointer     RepresentationKind = "pointer"
	RepresentationRecord      RepresentationKind = "record"
	RepresentationTaggedUnion RepresentationKind = "tagged-union"
	RepresentationView        RepresentationKind = "view"
	RepresentationSpan        RepresentationKind = "span"
	RepresentationOpaque      RepresentationKind = "opaque"
)

type Endianness string

const (
	EndianNative Endianness = ""
	EndianLittle Endianness = "little"
	EndianBig    Endianness = "big"
)

type FieldLayout struct {
	Name   string
	Offset uint32
	Size   uint32
}

type TagLayout struct {
	Bits   uint16
	Offset uint32
}

// Authority describes what code holding a value may do with it. Ownership,
// capabilities, and effects are semantic facts, not comments or tags.
type Authority struct {
	Ownership        Ownership
	Capabilities     []Capability
	RequiredEffects  []Effect
	ForbiddenEffects []Effect
	UnsafeBoundary   bool
}

type Ownership string

const (
	OwnershipUnspecified Ownership = ""
	OwnershipOwned       Ownership = "owned"
	OwnershipSharedRead  Ownership = "shared-read"
	OwnershipUniqueWrite Ownership = "unique-write"
	OwnershipMoved       Ownership = "moved"
	OwnershipExternal    Ownership = "external"
)

type Capability struct {
	Namespace string
	Name      string
}

// Effect is a semantic operation class. Parameters refine an effect without
// inventing a new effect name, e.g. Memory.Allocate[request_region]. An
// unparameterized effect denotes the whole class and therefore overlaps all of
// its parameterized instances for requires/forbids checking.
type Effect struct {
	Namespace  string
	Name       string
	Parameters []string
}

// Proposition is a structured fact suitable for multiple proof backends. The
// expression is intentionally not an arbitrary source string: projections can
// inspect its operators and terms without reparsing Oak syntax.
type Proposition struct {
	Name   string
	Expr   Expr
	Status ProofStatus
}

type ProofStatus string

const (
	ProofSpecified    ProofStatus = "specified"
	ProofChecked      ProofStatus = "checked"
	ProofSMT          ProofStatus = "proved-smt"
	ProofKernel       ProofStatus = "proved-kernel"
	ProofModelChecked ProofStatus = "model-checked"
	ProofTested       ProofStatus = "tested"
	ProofRefined      ProofStatus = "refined"
)

type Expr struct {
	Kind ExprKind
	Ref  string
	Int  int64
	Bool bool
	Op   Operator
	Args []Expr
}

type ExprKind string

const (
	ExprInvalid ExprKind = ""
	ExprRef     ExprKind = "ref"
	ExprInt     ExprKind = "int"
	ExprBool    ExprKind = "bool"
	ExprApply   ExprKind = "apply"
)

type Operator string

const (
	OpNot Operator = "not"
	OpAnd Operator = "and"
	OpOr  Operator = "or"
	OpEq  Operator = "eq"
	OpNe  Operator = "ne"
	OpLt  Operator = "lt"
	OpLe  Operator = "le"
	OpGt  Operator = "gt"
	OpGe  Operator = "ge"
	OpAdd Operator = "add"
	OpSub Operator = "sub"
	OpMul Operator = "mul"
	OpDiv Operator = "div"
	OpMod Operator = "mod"
)

func Ref(name string) Expr { return Expr{Kind: ExprRef, Ref: name} }
func Int(value int64) Expr { return Expr{Kind: ExprInt, Int: value} }
func Bool(value bool) Expr { return Expr{Kind: ExprBool, Bool: value} }
func Apply(op Operator, args ...Expr) Expr {
	return Expr{Kind: ExprApply, Op: op, Args: args}
}

// Protocol describes legal state evolution. Local typestate, temporal-model
// projection, generated DST actions, and debugger state diagrams should all use
// the same transition vocabulary.
type Protocol struct {
	Name        string
	States      []State
	Initial     string
	Transitions []Transition
	Invariants  []Proposition
	Assumptions []TemporalProperty
	Guarantees  []TemporalProperty
}

type State struct {
	Name string
}

type Transition struct {
	Name     string
	From     string
	To       string
	Requires []Proposition
	Effects  []Effect
}

type TemporalProperty struct {
	Name    string
	Formula TemporalExpr
}

type TemporalExpr struct {
	Kind TemporalKind
	Atom string
	Args []TemporalExpr
}

type TemporalKind string

const (
	TemporalInvalid    TemporalKind = ""
	TemporalAtom       TemporalKind = "atom"
	TemporalNot        TemporalKind = "not"
	TemporalAnd        TemporalKind = "and"
	TemporalOr         TemporalKind = "or"
	TemporalAlways     TemporalKind = "always"
	TemporalEventually TemporalKind = "eventually"
	TemporalNext       TemporalKind = "next"
	TemporalUntil      TemporalKind = "until"
	TemporalImplies    TemporalKind = "implies"
)

func Atom(name string) TemporalExpr { return TemporalExpr{Kind: TemporalAtom, Atom: name} }
func Temporal(kind TemporalKind, args ...TemporalExpr) TemporalExpr {
	return TemporalExpr{Kind: kind, Args: args}
}

// Attribute is extensible metadata. Correctness-critical semantics belong in
// the typed axes above rather than in this escape hatch.
type Attribute struct {
	Namespace string
	Name      string
	Value     string
}
