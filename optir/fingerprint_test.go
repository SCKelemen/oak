package optir

import "testing"

func TestFingerprintCFGIsCanonicalAndSensitiveToExactInput(t *testing.T) {
	cfg := licmTestCFG()
	first, err := FingerprintCFG(cfg)
	if err != nil {
		t.Fatal(err)
	}
	second, err := FingerprintCFG(cfg)
	if err != nil {
		t.Fatal(err)
	}
	if first == "" || first != second {
		t.Fatalf("CFG fingerprint is not deterministic: %q, %q", first, second)
	}

	empty := cfg
	empty.Facts = []Fact{}
	empty.Blocks = append([]Block(nil), cfg.Blocks...)
	empty.Blocks[0].Operations = append([]Operation(nil), cfg.Blocks[0].Operations...)
	empty.Blocks[0].Operations[0].Effects = []Effect{}
	emptyFingerprint, err := FingerprintCFG(empty)
	if err != nil {
		t.Fatal(err)
	}
	if emptyFingerprint != first {
		t.Fatalf("nil and empty slices have different fingerprints: %q, %q", first, emptyFingerprint)
	}

	changed := cfg
	changed.Blocks = append([]Block(nil), cfg.Blocks...)
	changed.Blocks[2].Operations = append([]Operation(nil), cfg.Blocks[2].Operations...)
	changed.Blocks[2].Operations[1].Source.Column++
	changedFingerprint, err := FingerprintCFG(changed)
	if err != nil {
		t.Fatal(err)
	}
	if changedFingerprint == first {
		t.Fatal("source identity change did not invalidate the CFG fingerprint")
	}
}

func TestFingerprintCFGRejectsMalformedInput(t *testing.T) {
	cfg := licmTestCFG()
	cfg.Blocks[0].Terminator.True.Target = 99
	if fingerprint, err := FingerprintCFG(cfg); err == nil || fingerprint != "" {
		t.Fatalf("malformed CFG fingerprint = %q, err = %v", fingerprint, err)
	}
}
