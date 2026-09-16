package asm

// A deliberately narrow, independently replayed native-equality CNF audit.
// The broad exporter in native_certificate.go remains unchanged.  This path
// accepts only fixed-width parameter/constant terms joined by pointwise
// AND/OR/XOR, then checks the producer's term roots and direct result-
// disequality root without calling blaster.blast during replay.

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// NativeBitwiseEqualityAudit is opaque evidence that the narrow native
// result terms, their CNF roots, the builder memo, and the emitted clauses
// agreed under the replay checks in this file.  It is audit material only:
// it cannot be converted to VerdictProven and compiler selection does not
// consume it.
type NativeBitwiseEqualityAudit struct {
	cnf CNF
}

// DIMACS returns the checked formula for an external, untrusted proof search.
// A future certificate consumer must regenerate this audit rather than accept
// the returned text from storage as authority.
func (a NativeBitwiseEqualityAudit) DIMACS() string { return a.cnf.Text }

// Variables and Clauses are diagnostic counts, not proof authority.
func (a NativeBitwiseEqualityAudit) Variables() int { return a.cnf.Variables }
func (a NativeBitwiseEqualityAudit) Clauses() int   { return a.cnf.Clauses }

// Settled reports the replay-checked constant outcome when no DIMACS formula
// was needed.  The returned value is a copy.
func (a NativeBitwiseEqualityAudit) Settled() (Decision, bool) {
	if a.cnf.Settled == nil {
		return Decision{}, false
	}
	return *a.cnf.Settled, true
}

// ExportNativeBitwiseEqualityAudit constructs a direct result-disequality
// formula for the narrow grammar and independently replays every reachable
// term root.  It deliberately excludes executor-generated fresh inputs even
// though the broad native certificate audit models them universally.
func ExportNativeBitwiseEqualityAudit(fn *Function, decl *ast.FunctionStatement) (NativeBitwiseEqualityAudit, string, bool) {
	refuse := func(format string, args ...interface{}) (NativeBitwiseEqualityAudit, string, bool) {
		return NativeBitwiseEqualityAudit{}, fmt.Sprintf(format, args...), false
	}
	prepared, reason, ok := prepareNativeEqualityTerms(fn, decl)
	if !ok {
		return refuse("native equality preparation: %s", reason)
	}
	if prepared.fresh != 0 {
		return refuse("executor-generated fresh inputs are outside the native bitwise replay")
	}
	if reason := nativeBitwiseTermReason(prepared.asm, prepared.widths); reason != "" {
		return refuse("machine result uses %s", reason)
	}
	if reason := nativeBitwiseTermReason(prepared.oak, prepared.widths); reason != "" {
		return refuse("Oak result uses %s", reason)
	}

	bl := newCNFBlaster(prepared.names, prepared.widths)
	machineBits := bl.blast(prepared.asm)
	oakBits := bl.blast(prepared.oak)
	if len(machineBits) != prepared.width || len(oakBits) != prepared.width || bl.exceeded() {
		return refuse("producer could not construct exact %d-bit result roots", prepared.width)
	}
	difference := bddFalse
	for bit := 0; bit < prepared.width; bit++ {
		bitDifference := bl.apply(opXor, machineBits[bit], oakBits[bit])
		difference = bl.apply(opOr, difference, bitDifference)
		if bl.exceeded() {
			return refuse("direct result disequality exceeded the clause budget")
		}
	}

	if err := validateNativeBitwiseRoots(bl, prepared.asm, prepared.oak, difference); err != nil {
		return refuse("term-root replay: %v", err)
	}
	cnf, reason, ok := serializeNativeBitwiseCNF(
		strings.Replace(prepared.label, "native equality", "native bitwise equality", 1),
		bl, difference,
	)
	if !ok {
		return refuse("%s", reason)
	}
	return NativeBitwiseEqualityAudit{cnf: cnf}, "", true
}

func validateNativeBitwiseRoots(bl *blaster, machine, oak *term, difference int) error {
	replay, err := newNativeCNFReplay(bl)
	if err != nil {
		return err
	}
	replayedMachine, err := replay.term(machine)
	if err != nil {
		return fmt.Errorf("machine roots: %w", err)
	}
	replayedOak, err := replay.term(oak)
	if err != nil {
		return fmt.Errorf("Oak roots: %w", err)
	}
	replayedDifference, err := replay.disequality(replayedMachine, replayedOak)
	if err != nil {
		return fmt.Errorf("result disequality: %w", err)
	}
	if replayedDifference != difference {
		return fmt.Errorf("result-disequality root is %d, replay produced %d", difference, replayedDifference)
	}
	return replay.finish()
}

func nativeBitwiseTermReason(root *term, widths map[string]int) string {
	seen := map[*term]bool{}
	var visit func(*term) string
	visit = func(current *term) string {
		if current == nil {
			return "a missing term"
		}
		if seen[current] {
			return ""
		}
		seen[current] = true
		if current.width < 1 || current.width > 64 {
			return fmt.Sprintf("a %d-bit term", current.width)
		}
		switch current.kind {
		case termParam:
			declared, known := widths[current.name]
			if !known || declared < 1 || declared > 64 || current.declaredWidth() != declared {
				return fmt.Sprintf("an undeclared or retyped input %q", current.name)
			}
			return ""
		case termConst:
			return ""
		case termBinary:
			switch current.op {
			case "and", "or", "xor":
			default:
				return fmt.Sprintf("operation %q outside pointwise and/or/xor", current.op)
			}
		default:
			return fmt.Sprintf("term kind %d outside parameters, constants, and pointwise and/or/xor", current.kind)
		}
		if reason := visit(current.left); reason != "" {
			return reason
		}
		return visit(current.right)
	}
	return visit(root)
}

type nativeCNFReplay struct {
	bl         *blaster
	terms      map[*term][]int
	inputs     map[int]bool
	gateKeys   map[cnfKey]bool
	maxInt     int
	startShape cnfObligationCounts
}

func newNativeCNFReplay(bl *blaster) (*nativeCNFReplay, error) {
	if bl == nil || bl.cnf == nil {
		return nil, fmt.Errorf("the CNF blaster is missing")
	}
	if bl.grouped || bl.assumed || len(bl.selects) != 0 {
		return nil, fmt.Errorf("the CNF blaster uses an ordering or abstraction outside the narrow replay")
	}
	if len(bl.params) != len(bl.index) {
		return nil, fmt.Errorf("the parameter index has %d entries for %d parameters", len(bl.index), len(bl.params))
	}
	seen := make(map[string]bool, len(bl.params))
	for index, name := range bl.params {
		position, indexed := bl.index[name]
		if name == "" || seen[name] || !indexed || position != index {
			return nil, fmt.Errorf("parameter %d has a missing, duplicate, or mismatched index", index)
		}
		width, known := bl.widths[name]
		if !known || width < 1 || width > 64 {
			return nil, fmt.Errorf("parameter %q has an invalid declared width", name)
		}
		seen[name] = true
	}
	if len(bl.widths) != len(bl.params) {
		return nil, fmt.Errorf("the width table contains parameters outside the ordered input list")
	}
	if err := validateCNFGateMemo(bl.cnf); err != nil {
		return nil, fmt.Errorf("gate memo: %w", err)
	}
	return &nativeCNFReplay{
		bl:         bl,
		terms:      map[*term][]int{},
		inputs:     map[int]bool{},
		gateKeys:   map[cnfKey]bool{},
		maxInt:     int(^uint(0) >> 1),
		startShape: snapshotCNFObligationCounts(bl),
	}, nil
}

func (r *nativeCNFReplay) finish() error {
	if len(r.terms) != len(r.bl.memo) {
		return fmt.Errorf("replay reached %d term-memo entries, producer has %d", len(r.terms), len(r.bl.memo))
	}
	if len(r.inputs) != len(r.bl.cnf.inputs) {
		return fmt.Errorf("replay reached %d input allocations, producer has %d", len(r.inputs), len(r.bl.cnf.inputs))
	}
	if len(r.gateKeys) != len(r.bl.cnf.memo) {
		return fmt.Errorf("replay reached %d gate memo keys, producer has %d", len(r.gateKeys), len(r.bl.cnf.memo))
	}
	if snapshotCNFObligationCounts(r.bl) != r.startShape {
		return fmt.Errorf("term-root replay changed the completed CNF builder")
	}
	return nil
}

func (r *nativeCNFReplay) term(t *term) ([]int, error) {
	if t == nil {
		return nil, fmt.Errorf("term is nil")
	}
	if bits, seen := r.terms[t]; seen {
		return bits, nil
	}
	if t.width < 1 || t.width > 64 {
		return nil, fmt.Errorf("term has invalid width %d", t.width)
	}

	var out []int
	switch t.kind {
	case termConst:
		if t.name != "" || t.op != "" || t.left != nil || t.right != nil || t.cond != nil || t.declared != 0 {
			return nil, fmt.Errorf("constant term has nonconstant fields")
		}
		if t.width < 64 && t.value>>uint(t.width) != 0 {
			return nil, fmt.Errorf("constant term has bits above its width")
		}
		out = make([]int, t.width)
		for bit := range out {
			if t.value>>uint(bit)&1 != 0 {
				out[bit] = bddTrue
			}
		}
	case termParam:
		if t.name == "" || t.op != "" || t.left != nil || t.right != nil || t.cond != nil || t.value != 0 {
			return nil, fmt.Errorf("parameter term has nonparameter fields")
		}
		declared, known := r.bl.widths[t.name]
		position, indexed := r.bl.index[t.name]
		if !known || !indexed || t.declaredWidth() != declared {
			return nil, fmt.Errorf("parameter %q is absent or has a mismatched declared width", t.name)
		}
		stride := r.bl.stride()
		if stride <= 0 || position < 0 || position >= len(r.bl.params) {
			return nil, fmt.Errorf("parameter %q has an invalid interleaved position", t.name)
		}
		out = make([]int, t.width)
		for bit := range out {
			if bit >= declared {
				continue
			}
			if bit > (r.maxInt-position)/stride {
				return nil, fmt.Errorf("parameter %q input index overflows int", t.name)
			}
			source := bit*stride + position
			dimacs, allocated := r.bl.cnf.inputs[source]
			if !allocated || dimacs < 1 || dimacs > r.bl.cnf.variables || dimacs > r.maxInt/2 {
				return nil, fmt.Errorf("parameter %q bit %d has no valid CNF input allocation", t.name, bit)
			}
			r.inputs[source] = true
			out[bit] = 2 * dimacs
		}
	case termBinary:
		if t.name != "" || t.value != 0 || t.declared != 0 || t.cond != nil || t.left == nil || t.right == nil {
			return nil, fmt.Errorf("binary term has malformed fields")
		}
		var operation int
		switch t.op {
		case "and":
			operation = opAnd
		case "or":
			operation = opOr
		case "xor":
			operation = opXor
		default:
			return nil, fmt.Errorf("operation %q is outside pointwise and/or/xor", t.op)
		}
		left, err := r.term(t.left)
		if err != nil {
			return nil, fmt.Errorf("left operand: %w", err)
		}
		right, err := r.term(t.right)
		if err != nil {
			return nil, fmt.Errorf("right operand: %w", err)
		}
		left = replayAdapt(left, t.width)
		right = replayAdapt(right, t.width)
		out = make([]int, t.width)
		for bit := range out {
			out[bit], err = r.apply(operation, left[bit], right[bit])
			if err != nil {
				return nil, fmt.Errorf("bit %d: %w", bit, err)
			}
		}
	default:
		return nil, fmt.Errorf("term kind %d is outside parameters, constants, and pointwise and/or/xor", t.kind)
	}

	producer, present := r.bl.memo[t]
	if !present || !sameReplayBits(producer, out) {
		return nil, fmt.Errorf("producer term memo does not contain the replayed roots")
	}
	r.terms[t] = out
	return out, nil
}

func (r *nativeCNFReplay) apply(operation, x, y int) (int, error) {
	if operation != opAnd && operation != opOr && operation != opXor {
		return 0, fmt.Errorf("unknown replay gate operation %d", operation)
	}
	if x < 0 || y < 0 {
		return 0, fmt.Errorf("negative CNF edge")
	}
	if x > y {
		x, y = y, x
	}
	switch {
	case x == y:
		if operation == opXor {
			return bddFalse, nil
		}
		return x, nil
	case x^1 == y:
		if operation == opAnd {
			return bddFalse, nil
		}
		return bddTrue, nil
	case x == bddFalse:
		if operation == opAnd {
			return bddFalse, nil
		}
		return y, nil
	case x == bddTrue:
		switch operation {
		case opAnd:
			return y, nil
		case opOr:
			return bddTrue, nil
		default:
			return y ^ 1, nil
		}
	}
	key := cnfKey{op: operation, x: x, y: y, z: -1}
	gate, present := r.bl.cnf.memo[key]
	if !present || gate < 1 || gate > r.bl.cnf.variables || gate > r.maxInt/2 {
		return 0, fmt.Errorf("non-folded gate has no valid exact memo entry")
	}
	r.gateKeys[key] = true
	return 2 * gate, nil
}

func replayAdapt(bits []int, width int) []int {
	out := make([]int, width)
	copy(out, bits)
	return out
}

func sameReplayBits(left, right []int) bool {
	if len(left) != len(right) {
		return false
	}
	for index := range left {
		if left[index] != right[index] {
			return false
		}
	}
	return true
}

func (r *nativeCNFReplay) disequality(left, right []int) (int, error) {
	if len(left) != len(right) || len(left) == 0 {
		return 0, fmt.Errorf("result roots have unequal or empty widths")
	}
	differs := bddFalse
	for bit := range left {
		difference, err := r.apply(opXor, left[bit], right[bit])
		if err != nil {
			return 0, fmt.Errorf("result bit %d: %w", bit, err)
		}
		differs, err = r.apply(opOr, differs, difference)
		if err != nil {
			return 0, fmt.Errorf("result prefix through bit %d: %w", bit, err)
		}
	}
	return differs, nil
}

func serializeNativeBitwiseCNF(label string, bl *blaster, difference int) (CNF, string, bool) {
	if bl == nil || bl.cnf == nil {
		return CNF{}, "internal native bitwise CNF builder is missing", false
	}
	if _, err := validateCNFAllocation(bl.cnf); err != nil {
		return CNF{}, fmt.Sprintf("internal native bitwise CNF allocation check failed: %v", err), false
	}
	out := CNF{Owners: map[int]VariableOwner{}, Names: append([]string(nil), bl.params...), gates: bl.cnf.gates, inputs: bl.cnf.inputs}
	for variable, dimacs := range bl.cnf.inputs {
		if owner, isParam := bl.owners[variable]; isParam {
			out.Owners[dimacs] = VariableOwner{Param: owner.param, Bit: owner.bit}
		}
	}
	switch difference {
	case bddFalse:
		out.Settled = &Decision{Kind: DecisionProven, Message: "the direct result-disequality root is false"}
		return out, "", true
	case bddTrue:
		out.Settled = &Decision{Kind: DecisionRefuted, Message: "the direct result-disequality root is true"}
		return out, "", true
	}
	obligation := []int{difference}
	final := []int{cnfLit(difference)}
	clauses := make([][]int, 0, len(bl.cnf.clauses)+1)
	clauses = append(clauses, bl.cnf.clauses...)
	clauses = append(clauses, final)
	if err := validateCNFTrace(bl.cnf, obligation, clauses); err != nil {
		return CNF{}, fmt.Sprintf("internal native bitwise CNF trace check failed: %v", err), false
	}
	out.obligation = obligation
	out.Variables = bl.cnf.variables
	out.Clauses = len(clauses)
	var text strings.Builder
	fmt.Fprintf(&text, "c %s\n", label)
	fmt.Fprintf(&text, "p cnf %d %d\n", out.Variables, out.Clauses)
	for _, clause := range clauses {
		for _, literal := range clause {
			text.WriteString(strconv.Itoa(literal))
			text.WriteByte(' ')
		}
		text.WriteString("0\n")
	}
	out.Text = text.String()
	return out, "", true
}
