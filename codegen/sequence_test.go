package codegen

import (
	"strings"
	"testing"
)

// The left-to-right sequencing lowering (docs/spec/90-backend.md §15,
// codegen/sequence.go) has four shapes: temporaries before a statement,
// a conditional in statement form, a short-circuit operator in statement
// form, and a while condition inside `for ( ;; )`. Each is pinned here so
// the emitted text changes only on purpose; the semantics are held by
// compiler/e2e_evaluation_order_test.go.
func TestSequencingShapes(t *testing.T) {
	prelude := "package main\n\nnext: (c: [*]u32): u32 {\n  c[0] = c[0] + 1\n  c[0]\n}\n"
	for _, tt := range []struct {
		name string
		body string
		want []string
	}{
		{"two calls in one operator", "  next(span(&s)) * 10 + next(span(&s))", []string{
			"    u32 oak__seq_0 = oak_mul_u32( oak_next( (oak_span_u32){ s.v, 1 } ), 10 );\n",
			"    u32 oak__seq_1 = oak_next( (oak_span_u32){ s.v, 1 } );\n",
			"    return oak_add_u32( oak__seq_0, oak__seq_1 )  ;\n",
		}},
		{"conditional arm in statement form", "  r: u32 = s[0] == 0 ? | true => next(span(&s)) * 10 + next(span(&s)) | false => 0\n  r", []string{
			"    u32 oak__seq_0;\n",
			"    if ( s.v[ 0 ] == 0 ) {\n",
			"      u32 oak__seq_1 = oak_mul_u32( oak_next( (oak_span_u32){ s.v, 1 } ), 10 );\n",
			"      u32 oak__seq_2 = oak_next( (oak_span_u32){ s.v, 1 } );\n",
			"      oak__seq_0 = oak_add_u32( oak__seq_1, oak__seq_2 );\n",
			"    } else {\n",
			"      oak__seq_0 = 0;\n",
			"    }\n",
			"    u32 r   = oak__seq_0  ;\n",
		}},
		{"short-circuit in statement form", "  ok: Bool = next(span(&s)) > 0 && next(span(&s)) * 10 + next(span(&s)) == 23\n  ok ? | true => 1 | false => 0", []string{
			"    Bool oak__seq_0;\n",
			"    oak__seq_0 = ( oak_next( (oak_span_u32){ s.v, 1 } ) > 0 );\n",
			"    if ( oak__seq_0 ) {\n",
			"      u32 oak__seq_1 = oak_mul_u32( oak_next( (oak_span_u32){ s.v, 1 } ), 10 );\n",
			"      u32 oak__seq_2 = oak_next( (oak_span_u32){ s.v, 1 } );\n",
			"      oak__seq_0 = ( oak_add_u32( oak__seq_1, oak__seq_2 ) == 23 );\n",
			"    }\n",
			"    Bool ok   = oak__seq_0  ;\n",
		}},
		{"while condition re-sequenced per iteration", "  while next(span(&s)) * 100 + next(span(&s)) < 400 {\n    _ = 0\n  }\n  s[0]", []string{
			"    for ( ;; ) {\n",
			"      u32 oak__seq_0 = oak_mul_u32( oak_next( (oak_span_u32){ s.v, 1 } ), 100 );\n",
			"      u32 oak__seq_1 = oak_next( (oak_span_u32){ s.v, 1 } );\n",
			"      if ( !( ( oak_add_u32( oak__seq_0, oak__seq_1 ) < 400 ) ) ) { break; }\n",
		}},
		{"one effect stays inline", "  next(span(&s)) + 1", []string{
			"    return oak_add_u32( oak_next( (oak_span_u32){ s.v, 1 } ), 1 )  ;\n",
		}},
	} {
		t.Run(tt.name, func(t *testing.T) {
			output := generateC(t, prelude+"main: (): u32 {\n  s: [1]u32\n"+tt.body+"\n}\n")
			for _, want := range tt.want {
				if !strings.Contains(output, want) {
					t.Fatalf("emitted C lacks\n%s\n— output:\n%s", want, output)
				}
			}
			if tt.name == "one effect stays inline" && strings.Contains(output, "oak__seq_") {
				t.Fatalf("a single effect was hoisted:\n%s", output)
			}
		})
	}
}
