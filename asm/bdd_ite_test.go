package asm

import "testing"

// Exercise every condition and then-arm function over three variables. The
// oracle evaluates truth tables, independently of BDD construction.
func TestBDDITESemantics(t *testing.T) {
	b := newBDD(100000)
	var functions [256]int
	for table := range functions {
		var build func(int, int) int
		build = func(v, prefix int) int {
			if v == 3 {
				return table >> prefix & 1
			}
			return b.mk(v, build(v+1, prefix), build(v+1, prefix|1<<v))
		}
		functions[table] = build(0, 0)
	}
	// Cover all condition/then pairs and a deterministic permutation of
	// else arms, including constants, complemented edges, and cache reuse.
	for ct, c := range functions {
		for tt, then := range functions {
			et := (ct*73 + tt*151) & 255
			want := (ct & tt) | ((ct ^ 255) & et)
			if got := b.ite(c, then, functions[et]); got != functions[want] {
				t.Fatalf("ITE(%02x,%02x,%02x): edge %d, want %d", ct, tt, et, got, functions[want])
			}
		}
	}
	if b.exceeded {
		t.Fatal("unexpected budget exhaustion")
	}
}

func TestBDDITEBudget(t *testing.T) {
	b := newBDD(4)
	c, tv, e := b.variable(0), b.variable(1), b.variable(2)
	b.ite(c, tv, e)
	if !b.exceeded {
		t.Fatal("ITE must fail closed at the node budget")
	}
}

func BenchmarkBDDITE(b *testing.B) {
	for _, direct := range []bool{false, true} {
		name := "decomposed"
		if direct {
			name = "ternary"
		}
		b.Run(name, func(b *testing.B) {
			var nodes int
			b.ReportAllocs()
			for b.Loop() {
				d := newBDD(200000)
				x := benchVector(d, 0, 3, 32)
				y := benchVector(d, 1, 3, 32)
				z := benchVector(d, 2, 3, 32)
				for i := range x {
					if direct {
						d.ite(x[i], y[i], z[i])
					} else {
						d.apply(opOr, d.apply(opAnd, x[i], y[i]), d.apply(opAnd, x[i]^1, z[i]))
					}
				}
				if d.exceeded {
					b.Fatal("budget exhausted")
				}
				nodes = len(d.nodes)
			}
			b.ReportMetric(float64(nodes), "nodes/op")
		})
	}
}
