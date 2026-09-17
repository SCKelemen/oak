package optir

// SnapshotCFG returns an owned deep copy and its exact verified fingerprint.
// The caller must not mutate cfg concurrently with copying. Published graph
// consumers must treat the snapshot as immutable; this is not proof authority.
func SnapshotCFG(cfg CFG) (CFG, string, error) {
	snapshot := cloneCFG(cfg)
	fingerprint, err := FingerprintCFG(snapshot)
	if err != nil {
		return CFG{}, "", err
	}
	return snapshot, fingerprint, nil
}
