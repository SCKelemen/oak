package compiler

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

// Long alias chains must never turn unknown provenance into exclusive
// authority. These are regression controls: the previous conservative joins
// already rejected these examples before the convergence-driven traversal.
func TestResourceLoopPropagatesUnknownThroughAliasChain(t *testing.T) {
	for _, depth := range []int{3, 5, 9} {
		t.Run(fmt.Sprint(depth), func(t *testing.T) {
			var body strings.Builder
			body.WriteString("f: (h: Handle, other: Handle, again: Bool): u32 {\n")
			fmt.Fprintf(&body, "  r%d: Handle = h\n", depth)
			for i := depth - 1; i >= 0; i-- {
				fmt.Fprintf(&body, "  r%d: Handle = r%d\n", i, i+1)
			}
			body.WriteString("  while again {\n")
			for i := 0; i < depth; i++ {
				fmt.Fprintf(&body, "    r%d = r%d\n", i, i+1)
			}
			fmt.Fprintf(&body, "    r%d = project(other)\n", depth)
			body.WriteString("    update_pair(r0, other)\n  }\n  0\n}\n")
			expectCode(t, "loop-alias-chain", checkReassignment(t, "loop-alias-chain", body.String()), typechecker.CodeResourceCallAliasConflict)
		})
	}
}

func TestResourceLoopStableSharedAuthority(t *testing.T) {
	if err := checkReassignment(t, "loop-shared", `
f: (h: Handle, again: Bool): u32 {
  alias: Handle = h
  while again {
    inspect(alias)
  }
  inspect(h)
  0
}
`); err != nil {
		t.Fatalf("a stable shared loop must remain admitted: %v", err)
	}
}
