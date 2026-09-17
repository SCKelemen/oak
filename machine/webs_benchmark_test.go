package machine

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
)

// A copy-heavy scalar body resembling the input to Simplify after frame-word
// promotion. Labels vary the CFG size without changing the instruction count.
func websBenchmarkBody(blocks, copies int, loop bool) *asm.Function {
	var items []asm.Item
	for block := 0; block < blocks; block++ {
		items = append(items, label("block_"+itoa(block)))
		for copy := 0; copy < copies; copy++ {
			items = append(items,
				ins("add", w(9), w(0), imm(1)),
				ins("mov", w(10), w(9)),
				ins("eor", w(0), w(10), w(9)))
		}
	}
	if loop {
		items = append(items, ins("cmp", w(0), w(1)), bcond("lo", "block_0"))
	}
	return fn(append(items, ins("ret"))...)
}

func BenchmarkWebs(b *testing.B) {
	for _, shape := range []struct {
		name           string
		blocks, copies int
		loop           bool
	}{
		{"straight", 1, 1024, false},
		{"blocks", 64, 16, false},
		{"loop", 16, 64, true},
	} {
		b.Run(shape.name, func(b *testing.B) {
			f, err := Lift(websBenchmarkBody(shape.blocks, shape.copies, shape.loop))
			if err != nil {
				b.Fatal(err)
			}
			b.ReportAllocs()
			b.ResetTimer()
			for i := 0; i < b.N; i++ {
				webs, err := f.Webs()
				if err != nil || len(webs) < 64 {
					b.Fatalf("webs=%d, error=%v", len(webs), err)
				}
			}
		})
	}
}

func BenchmarkSimplifyCopies(b *testing.B) {
	const copies = 128
	body := websBenchmarkBody(1, copies, false)
	b.ReportAllocs()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		f, err := Lift(cloneFunction(body))
		if err != nil {
			b.Fatal(err)
		}
		propagated, eliminated, err := f.Simplify()
		if err != nil || propagated != copies || eliminated != copies {
			b.Fatalf("propagated=%d eliminated=%d, error=%v", propagated, eliminated, err)
		}
	}
}
