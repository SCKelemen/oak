// Package optir defines Oak's target-independent optimization representation.
//
// OptIR is not semantic authority and contains no machine instructions or
// target costs. It preserves structured control and explicit effects while
// providing a deterministic CFG/SSA projection for generic analyses.
package optir

// ValueID names one SSA value. Zero is invalid so omitted operands fail
// verification instead of accidentally naming a real definition.
type ValueID uint32

// BlockID names one block in a canonical CFG projection.
type BlockID uint32

// Type is a canonical checked type name. OptIR does not choose its physical
// representation; that remains a later target-dependent decision.
type Type string

const TypeBool Type = "Bool"

// Source identifies the stable semantic source location retained by an
// optimization node. Context distinguishes imported and specialized syntax.
type Source struct {
	Context string
	Line    int
	Column  int
}

// Effect is an explicit operation effect. Unknown effects are represented by
// their checked semantic name rather than being silently treated as pure.
type Effect string

const (
	EffectReadMemory  Effect = "Memory.Read"
	EffectWriteMemory Effect = "Memory.Write"
	EffectAllocate    Effect = "Memory.Allocate"
	EffectTrap        Effect = "Control.Trap"
	EffectCall        Effect = "Control.Call"
	EffectSynchronize Effect = "Concurrency.Synchronize"
)

// Attribute is deterministic operation metadata. Slices preserve declaration
// order; maps are deliberately absent from the stable IR.
type Attribute struct {
	Name  string
	Value string
}

// Fact attaches a checked/proved proposition to values without making the
// proposition permission to transform them. Provenance is the stable proof
// vocabulary used by the semantic layer.
type Fact struct {
	ID         string
	Name       string
	Values     []ValueID
	Provenance string
	Witness    string
	Scope      string
	// Dependencies are stable checked proposition identities or normalized
	// premises. Their order is part of fact identity.
	Dependencies []string
}

// Value is one typed SSA definition.
type Value struct {
	ID     ValueID
	Type   Type
	Name   string
	Source Source
}

// Operation is a target-independent scalar, memory, or call operation. Its
// effects must be explicit before a future pass may reorder or remove it.
type Operation struct {
	Code           string
	Results        []Value
	Operands       []ValueID
	Effects        []Effect
	Attributes     []Attribute
	Facts          []Fact
	Source         Source
	MemoryAccessID string
}

// Region is structured control with explicit arguments and yielded values.
// Region arguments are lexical SSA values that the CFG projection remaps to
// block parameters.
type Region struct {
	Arguments []Value
	Nodes     []Node
	Yield     []ValueID
}

// Node is exactly one scalar operation, structured conditional, or structured
// pre-test loop. Verification rejects empty and multiply-populated nodes.
type Node struct {
	Operation *Operation
	If        *If
	While     *While
}

// If retains the source conditional until a CFG analysis is requested. Both
// regions yield one value for every declared result.
type If struct {
	Condition ValueID
	Results   []Value
	Then      Region
	Else      Region
}

// While is a pre-test loop. Initial supplies the first carried values;
// Condition arguments observe the current values and yield one Bool; Body
// arguments observe the same current values and yield the next values. Results
// are the carried values on loop exit, including the zero-trip path.
type While struct {
	Initial   []ValueID
	Results   []Value
	Condition Region
	Body      Region
}

// Function is structured OptIR. Results contains result types; Body.Yield
// identifies the actual returned SSA values.
type Function struct {
	Name       string
	Parameters []Value
	Results    []Type
	Body       Region
	Facts      []Fact
}

// TerminatorKind is the complete control transfer of a CFG block.
type TerminatorKind string

const (
	TerminatorReturn     TerminatorKind = "return"
	TerminatorBranch     TerminatorKind = "branch"
	TerminatorCondBranch TerminatorKind = "cond-branch"
)

// Edge transfers SSA arguments to the target block's parameters.
type Edge struct {
	Target    BlockID
	Arguments []ValueID
}

// Terminator contains only the fields named by Kind. Branch uses True;
// CondBranch uses Condition, True, and False; Return uses Values.
type Terminator struct {
	Kind      TerminatorKind
	Condition ValueID
	True      Edge
	False     Edge
	Values    []ValueID
}

// Block is one canonical CFG/SSA block. Parameters are phi-like definitions
// supplied by every incoming edge.
type Block struct {
	ID         BlockID
	Parameters []Value
	Operations []Operation
	Terminator Terminator
}

// CFG is the deterministic projection used by dominator, SCCP, GVN, and loop
// analyses. It remains target independent.
type CFG struct {
	Name    string
	Entry   BlockID
	Results []Type
	Blocks  []Block
	Facts   []Fact
}
