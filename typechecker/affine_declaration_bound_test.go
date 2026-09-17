package typechecker

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
)

func affinePagesIndexProven(t *testing.T, source string) bool {
	t.Helper()
	tc := setupTypeChecker(source)
	proven := false
	tc.indexDecisionHook = func(_ []extentFact, _ ast.Expression, name string, _ *ArrayType, decision bool) {
		if name == "s.pages" && decision {
			proven = true
		}
	}
	program := parseProgram(source)
	tc.CheckProgram(program)
	if errs := tc.Errors(); len(errs) != 0 {
		t.Fatalf("typecheck failed: %v\n%s", errs, source)
	}
	return proven
}

func TestAffineDeclarationBoundFromImmutableGeometry(t *testing.T) {
	source := `max_pages: u16 = u16(24)
entries: u32 = u32(2048)

Regime: type = struct { pages: [49152]u64 }

reset: (s: [*]Regime, dom: u32): () {
  i: u16 = u16(0)
  while i < max_pages {
    j: u32 = u32(0)
    while j < entries {
      inlined_cell: u32 = u32(i) * entries + j
      s[dom].pages[inlined_cell] = u64(0)
      j = j + u32(1)
    }
    i = i + u16(1)
  }
}
`
	if !affinePagesIndexProven(t, source) {
		t.Fatal("the inlined page-cell binding must inherit i < 24 and j < 2048")
	}
}

func TestAffineDeclarationBoundFailsClosed(t *testing.T) {
	tests := []struct {
		name   string
		source string
	}{
		{
			name: "mutable scale global",
			source: `max_pages: u16 = u16(24)
entries: u32 = u32(2048)
Regime: type = struct { pages: [49152]u64 }
change_entries: (): () { entries = u32(1024) }
reset: (s: [*]Regime, dom: u32): () {
  i: u16 = u16(0)
  while i < max_pages {
    j: u32 = u32(0)
    while j < entries {
      inlined_cell: u32 = u32(i) * entries + j
      s[dom].pages[inlined_cell] = u64(0)
      j = j + u32(1)
    }
    i = i + u16(1)
  }
}
`,
		},
		{
			name: "missing source bound",
			source: `entries: u32 = u32(2048)
Regime: type = struct { pages: [49152]u64 }
reset: (s: [*]Regime, dom: u32, i: u16): () {
  j: u32 = u32(0)
  while j < entries {
    inlined_cell: u32 = u32(i) * entries + j
    s[dom].pages[inlined_cell] = u64(0)
    j = j + u32(1)
  }
}
`,
		},
		{
			name: "unsupported narrowing",
			source: `max_pages: u16 = u16(24)
entries: u8 = u8(8)
Regime: type = struct { pages: [192]u64 }
reset: (s: [*]Regime, dom: u32): () {
  i: u16 = u16(0)
  while i < max_pages {
    j: u8 = u8(0)
    while j < entries {
      inlined_cell: u8 = u8_trunc_u16(i) * entries + j
      s[dom].pages[inlined_cell] = u64(0)
      j = j + u8(1)
    }
    i = i + u16(1)
  }
}
`,
		},
		{
			name: "word overflow",
			source: `rows: u8 = u8(17)
columns: u8 = u8(16)
Regime: type = struct { pages: [272]u64 }
reset: (s: [*]Regime, dom: u32): () {
  i: u8 = u8(0)
  while i < rows {
    j: u8 = u8(0)
    while j < columns {
      inlined_cell: u8 = i * columns + j
      s[dom].pages[inlined_cell] = u64(0)
      j = j + u8(1)
    }
    i = i + u8(1)
  }
}
`,
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if affinePagesIndexProven(t, test.source) {
				t.Fatalf("unsafe affine declaration was proven: %s", strings.TrimSpace(test.source))
			}
		})
	}
}
