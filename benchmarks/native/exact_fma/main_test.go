package main

import "testing"

func TestObservationsInterleaveAndRotate(t *testing.T) {
	for _, backends := range []int{3, 4, 5} {
		for round := 0; round < 4*backends; round++ {
			seen := map[int]bool{}
			for offset := 0; offset < 4*backends; offset++ {
				index := observationIndex(round, offset, backends)
				if index < 0 || index >= 4*backends || seen[index] {
					t.Fatalf("invalid/duplicate observation %d", index)
				}
				seen[index] = true
			}
			if observationIndex(round, 0, backends) != round {
				t.Fatal("first implementation did not rotate")
			}
		}
	}
}

func TestRejectInvalidOrInconsistentSamples(t *testing.T) {
	checksums := map[int]string{}
	good := sample{Elapsed: 100, Bits: "000000000000002a"}
	if err := acceptSample(good, 32, checksums); err != nil {
		t.Fatal(err)
	}
	if err := acceptSample(good, 32, checksums); err != nil {
		t.Fatal(err)
	}
	for _, bad := range []sample{
		{Bits: good.Bits}, {Elapsed: 100}, {Elapsed: 100, Bits: "not-hex-checksum!"},
		{Elapsed: 100, Bits: "000000000000002b"},
	} {
		if err := acceptSample(bad, 32, checksums); err == nil {
			t.Fatalf("accepted %+v", bad)
		}
		if checksums[32] != good.Bits {
			t.Fatal("bad sample changed the reference checksum")
		}
	}
	// Different widths have distinct encodings, not a shared checksum slot.
	if err := acceptSample(sample{Elapsed: 100, Bits: "000000000000002b"}, 64, checksums); err != nil {
		t.Fatal(err)
	}
}
