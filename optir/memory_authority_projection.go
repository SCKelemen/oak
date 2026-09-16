package optir

import "fmt"

// checkedMemoryAuthorityCoverage states whether checked authority is an upper
// bound on active operations or must be consumed exactly. Optimized certificate
// roots use the former because a verified rewrite may remove operations;
// original non-root CFGs use the latter.
type checkedMemoryAuthorityCoverage uint8

const (
	checkedMemoryAuthorityUpperBound checkedMemoryAuthorityCoverage = iota + 1
	checkedMemoryAuthorityExact
)

// checkedMemoryAuthorityProjection is the small semantic boundary between a
// checked CFG and call-summary construction. Its records are in CFG order and
// have already been resolved against separate, integrity-checked authority.
type checkedMemoryAuthorityProjection struct {
	direct []CheckedMemoryAccessRecord
	calls  []CheckedMemoryCallRecord
}

// projectActiveCheckedMemoryAuthority checks every active memory claim in a
// CFG and returns only records that are actually attached to operations. It is
// deliberately independent of region-memory metadata construction so summary
// derivation need not trust a second unchecked scan of opaque IDs.
func projectActiveCheckedMemoryAuthority(cfg CFG, authority CheckedMemoryAuthority, coverage checkedMemoryAuthorityCoverage) (checkedMemoryAuthorityProjection, error) {
	if coverage != checkedMemoryAuthorityUpperBound && coverage != checkedMemoryAuthorityExact {
		return checkedMemoryAuthorityProjection{}, fmt.Errorf("optir: invalid checked memory authority coverage %d", coverage)
	}
	if err := Verify(cfg); err != nil {
		return checkedMemoryAuthorityProjection{}, err
	}
	if err := verifyCheckedMemoryAuthorityIntegrity(authority); err != nil {
		return checkedMemoryAuthorityProjection{}, err
	}

	projection := checkedMemoryAuthorityProjection{
		direct: make([]CheckedMemoryAccessRecord, 0, len(authority.records)),
		calls:  make([]CheckedMemoryCallRecord, 0, len(authority.callRecords)),
	}
	types := checkedMemoryValueTypes(cfg)
	seen := make(map[string]bool, len(authority.records)+len(authority.callRecords))
	for _, block := range cfg.Blocks {
		for index, operation := range block.Operations {
			if operation.MemoryAccessID != "" && operation.MemoryCallID != "" {
				return checkedMemoryAuthorityProjection{}, fmt.Errorf("optir: operation %d:%d carries both memory access and call IDs", block.ID, index)
			}

			switch {
			case operation.MemoryCallID != "":
				record, exists := authority.callRecords[operation.MemoryCallID]
				if !exists {
					return checkedMemoryAuthorityProjection{}, fmt.Errorf("optir: call operation %d:%d has stale or unknown call ID %s", block.ID, index, operation.MemoryCallID)
				}
				if seen[record.ID] {
					return checkedMemoryAuthorityProjection{}, fmt.Errorf("optir: checked memory authority ID %s is attached more than once", record.ID)
				}
				if operation.Source != record.Source {
					return checkedMemoryAuthorityProjection{}, fmt.Errorf("optir: checked memory call %s moved from its source scope", record.ID)
				}
				if err := validateCheckedMemoryCallOperation(operation, record); err != nil {
					return checkedMemoryAuthorityProjection{}, fmt.Errorf("optir: checked memory call %d:%d: %w", block.ID, index, err)
				}
				seen[record.ID] = true
				record.Accesses = append([]CheckedMemoryCallAccess(nil), record.Accesses...)
				projection.calls = append(projection.calls, record)

			case operation.MemoryAccessID != "":
				record, exists := authority.records[operation.MemoryAccessID]
				if !exists {
					return checkedMemoryAuthorityProjection{}, fmt.Errorf("optir: memory operation %d:%d has stale or unknown access ID %s", block.ID, index, operation.MemoryAccessID)
				}
				if seen[record.ID] {
					return checkedMemoryAuthorityProjection{}, fmt.Errorf("optir: checked memory authority ID %s is attached more than once", record.ID)
				}
				if operation.Source != record.Source {
					return checkedMemoryAuthorityProjection{}, fmt.Errorf("optir: checked memory access %s moved from its source scope", record.ID)
				}
				if err := validateCheckedMemoryOperation(operation, record, types); err != nil {
					return checkedMemoryAuthorityProjection{}, fmt.Errorf("optir: checked memory operation %d:%d: %w", block.ID, index, err)
				}
				seen[record.ID] = true
				projection.direct = append(projection.direct, record)

			default:
				if operation.Code == OpLoadRegion || operation.Code == OpStoreRegion {
					return checkedMemoryAuthorityProjection{}, fmt.Errorf("optir: unchecked operation %d:%d (%s) has no checked memory access ID", block.ID, index, operation.Code)
				}
				if err := validateOperationMemoryMetadata(operation, nil, "", false); err != nil {
					return checkedMemoryAuthorityProjection{}, fmt.Errorf("optir: unchecked operation %d:%d (%s): %w", block.ID, index, operation.Code, err)
				}
			}
		}
	}

	if coverage == checkedMemoryAuthorityExact {
		for id := range authority.records {
			if !seen[id] {
				return checkedMemoryAuthorityProjection{}, fmt.Errorf("optir: checked memory call summary requires exact active authority coverage; access ID %s is inactive", id)
			}
		}
		for id := range authority.callRecords {
			if !seen[id] {
				return checkedMemoryAuthorityProjection{}, fmt.Errorf("optir: checked memory call summary requires exact active authority coverage; call ID %s is inactive", id)
			}
		}
	}
	return projection, nil
}
