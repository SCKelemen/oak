package asm

import (
	"math/rand"
	"testing"
)

func TestBDDTableGrowthPreservesTriples(t *testing.T) {
	// Deliberately small tables exercise several growths, collisions, negative
	// int32 bit patterns, and cached zero results. The maps are independent oracles.
	unique, memo := newUniqueTable(8), newOpTable(8)
	unique.maxSlots, memo.maxSlots = 1<<16, 1<<16
	want := map[[3]int32]int32{}
	rng := rand.New(rand.NewSource(737))
	never := func() bool { return false }
	for i := int32(0); i < 24000; i++ {
		key := [3]int32{int32(rng.Uint32()), int32(rng.Uint32()), int32(rng.Uint32())}
		if _, exists := want[key]; exists {
			continue
		}
		want[key] = i
		if !unique.insert(key[0], key[1], key[2], i, never) || !memo.insert(key[0], key[1], key[2], i, never) {
			t.Fatal("unexpected interruption")
		}
		if len(unique.entries) > unique.maxSlots || len(memo.entries) > memo.maxSlots {
			t.Fatal("growth exceeded reserved ceiling")
		}
	}
	for key, value := range want {
		if got, ok := unique.lookup(key[0], key[1], key[2]); !ok || got != value {
			t.Fatalf("unique %v: %d/%v want %d", key, got, ok, value)
		}
		if got, ok := memo.lookup(key[0], key[1], key[2]); !ok || got != value {
			t.Fatalf("memo %v: %d/%v want %d", key, got, ok, value)
		}
	}
	if unique.count != len(want) || memo.count != len(want) || memo.resets != 0 {
		t.Fatal("growth lost entries or evicted early")
	}
}

func TestBDDTableGrowthStaysWithinAdmissionEnvelope(t *testing.T) {
	for _, budget := range []int{1, 32768, 32769, 100000, 2000000} {
		b := newBDD(budget)
		if len(b.unique.entries) != 0 || len(b.memo.entries) != 0 {
			t.Fatal("allocated before admission")
		}
		// The preexisting half-full, power-of-two capacity is the ceiling.
		final := 1 << 16
		for final < 2*budget {
			final *= 2
		}
		if bddUniqueTableSlots(budget) != final {
			t.Fatal("changed final capacity")
		}
		for current := 1 << 16; current < final; {
			next := bddTableGrowth(current, bddUniqueTableSlots(budget))
			if next <= current || next > final || current+next > final+final/2 {
				t.Fatal("growth exceeded existing overlap reservation")
			}
			current = next
		}
	}
}

func BenchmarkBDDTableGrowth(b *testing.B) {
	for _, fast := range []bool{false, true} {
		name := "doubling"
		if fast {
			name = "bounded-fourfold"
		}
		b.Run(name, func(b *testing.B) {
			b.ReportAllocs()
			for n := 0; n < b.N; n++ {
				table := newUniqueTable(1 << 16)
				if fast {
					table.maxSlots = 1 << 21
				}
				for i := int32(0); i < 600000; i++ {
					table.insert(i%127, i*2, i*2+1, i, func() bool { return false })
				}
				if table.count != 600000 {
					b.Fatal(table.count)
				}
			}
		})
	}
}

func TestBDDTableGrowthUsesReducedImplicationBudget(t *testing.T) {
	b := newBDD(2000000)
	// The production implication owner lowers its allowance before admission.
	b.budget = 40000
	for i := 0; i < 39999; i++ {
		b.variable(i)
	}
	if b.exceeded || len(b.nodes) != 40000 {
		t.Fatal("node allowance changed")
	}
	if len(b.unique.entries) != 1<<17 {
		t.Fatalf("used constructor budget instead of live allowance: %d slots", len(b.unique.entries))
	}
	b.variable(39999)
	if !b.exceeded || len(b.nodes) != 40000 {
		t.Fatal("exhaustion stopped being fail-closed")
	}
}
