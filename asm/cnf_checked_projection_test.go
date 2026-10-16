package asm

import (
	"fmt"
	"testing"
)

// Read-only finite projection; all evaluation maps are fresh per invocation.
func (a typedCNFAudit) checkValues(env map[string]uint64, memory func(string, uint32) uint32) error {
	if _, ok := a.stats(); !ok {
		return errInvalidTypedCNFAudit
	}
	bl := a.checked.owned
	values := map[int]bool{}
	memo := map[*term]uint64{}
	for source, owner := range bl.owners {
		values[bl.cnf.inputs[source]] = env[owner.param]>>uint(owner.bit)&1 != 0
	}
	for _, read := range bl.selects {
		word := memory(read.span, uint32(typedCNFValue(read.index, env, memory, memo)))
		for bit, source := range read.vars {
			values[bl.cnf.inputs[source]] = word>>uint(bit)&1 != 0
		}
	}
	edge := func(e int) bool {
		if e < 2 {
			return e == 1
		}
		return values[e>>1] != (e&1 != 0)
	}
	for _, gate := range bl.cnf.gates {
		var v bool
		switch gate.op {
		case opAnd:
			v = edge(gate.x) && edge(gate.y)
		case opOr:
			v = edge(gate.x) || edge(gate.y)
		case opXor:
			v = edge(gate.x) != edge(gate.y)
		case cnfIte:
			if edge(gate.x) {
				v = edge(gate.y)
			} else {
				v = edge(gate.z)
			}
		}
		values[gate.out] = v
	}
	for term, bits := range bl.memo {
		want := typedCNFValue(term, env, memory, memo)
		for bit, root := range bits {
			if edge(root) != (want>>uint(bit)&1 != 0) {
				return fmt.Errorf("typed node kind=%d op=%s width=%d bit=%d", term.kind, term.op, term.width, bit)
			}
		}
	}
	p, l, r := a.checked.roots[0], a.checked.roots[1], a.checked.roots[2]
	violation := typedCNFValue(p, env, memory, memo) != 0 && typedCNFValue(l, env, memory, memo) != typedCNFValue(r, env, memory, memo)
	if edge(a.checked.stats.Obligation) != violation {
		return fmt.Errorf("implication polarity")
	}
	return nil
}

func (a typedCNFAudit) testStats(t *testing.T) typedCNFAuditStats {
	t.Helper()
	stats, ok := a.stats()
	if !ok {
		t.Fatal(errInvalidTypedCNFAudit)
	}
	return stats
}
