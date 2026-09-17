package optir

import "testing"

func TestSnapshotCFG(t *testing.T) {
	input := licmTestCFG()
	snapshot, fingerprint, err := SnapshotCFG(input)
	if err != nil {
		t.Fatal(err)
	}
	input.Results[0] = "unknown"
	input.Blocks[0].Operations[0].Attributes[0].Value = "different"
	input.Blocks[0].Operations[0].Results[0].Type = "unknown"
	input.Blocks[0].Terminator.True.Arguments[0] = 999
	if after, err := FingerprintCFG(snapshot); err != nil || after != fingerprint {
		t.Fatal("caller mutation changed published snapshot", after, err)
	}
	if bad, key, err := SnapshotCFG(input); err == nil || len(bad.Blocks) != 0 || key != "" {
		t.Fatal("malformed input received a snapshot identity", err)
	}
}
