package optir

import (
	"crypto/sha256"
	"fmt"
	"reflect"
	"sort"
)

// RegionMemoryObservability explicitly declares which region states are
// observable on normal function return. An omitted region is not implicitly
// live-out. Callers must derive this boundary from checked function effects;
// this analysis never guesses it from pointer or operation spelling.
type RegionMemoryObservability struct {
	LiveOut []RegionID
}

// MemoryDefinitionLiveness is advisory memory-SSA use evidence. Dead access
// and version candidates are not permission to remove an operation: a later
// transform must additionally establish address/alias legality and pass the
// compiler's semantic verification gate.
type MemoryDefinitionLiveness struct {
	LiveAccesses          []MemoryAccessID
	LiveVersions          []MemoryVersionID
	DeadAccessCandidates  []MemoryAccessID
	DeadVersionCandidates []MemoryVersionID

	inputFingerprint         string
	metadataFingerprint      string
	memorySSAFingerprint     string
	observabilityFingerprint string
	integrity                string
}

// AnalyzeMemoryDefinitionLiveness finds memory definitions that have no use in
// the exact RegionMemorySSA graph under an explicit normal-return observability
// boundary. Reads, read-write operations, and opaque clobbers make their
// reaching definitions live. Live phis recursively make every incoming version
// live, including loop backedges.
func AnalyzeMemoryDefinitionLiveness(
	cfg CFG,
	metadata RegionMemoryMetadata,
	memorySSA RegionMemorySSA,
	observability RegionMemoryObservability,
) (MemoryDefinitionLiveness, error) {
	if err := VerifyRegionMemorySSA(cfg, metadata, memorySSA); err != nil {
		return MemoryDefinitionLiveness{}, err
	}
	normalizedMetadata, err := normalizeMemoryMetadata(cfg, metadata)
	if err != nil {
		return MemoryDefinitionLiveness{}, err
	}
	normalizedObservability, err := normalizeRegionMemoryObservability(memorySSA.Regions, observability)
	if err != nil {
		return MemoryDefinitionLiveness{}, err
	}
	analysis, err := buildMemoryDefinitionLiveness(cfg, memorySSA, normalizedObservability)
	if err != nil {
		return MemoryDefinitionLiveness{}, err
	}
	analysis.inputFingerprint = fingerprintCFG(cfg)
	analysis.metadataFingerprint = fingerprintNormalizedMemoryMetadata(normalizedMetadata)
	analysis.memorySSAFingerprint = memorySSA.integrity
	analysis.observabilityFingerprint = fingerprintRegionMemoryObservability(normalizedObservability)
	analysis.integrity = fingerprintMemoryDefinitionLiveness(analysis)
	return analysis, nil
}

// VerifyMemoryDefinitionLiveness checks exact CFG, metadata, memory-SSA, and
// observability ownership, then independently recomputes the canonical
// liveness result. This is evidence-integrity verification, not a proof that a
// reported candidate may be deleted.
func VerifyMemoryDefinitionLiveness(
	cfg CFG,
	metadata RegionMemoryMetadata,
	memorySSA RegionMemorySSA,
	observability RegionMemoryObservability,
	analysis MemoryDefinitionLiveness,
) error {
	if err := VerifyRegionMemorySSA(cfg, metadata, memorySSA); err != nil {
		return err
	}
	normalizedMetadata, err := normalizeMemoryMetadata(cfg, metadata)
	if err != nil {
		return err
	}
	normalizedObservability, err := normalizeRegionMemoryObservability(memorySSA.Regions, observability)
	if err != nil {
		return err
	}
	if analysis.inputFingerprint == "" || analysis.inputFingerprint != fingerprintCFG(cfg) {
		return fmt.Errorf("optir: memory-definition liveness belongs to a different CFG")
	}
	if analysis.metadataFingerprint == "" || analysis.metadataFingerprint != fingerprintNormalizedMemoryMetadata(normalizedMetadata) {
		return fmt.Errorf("optir: memory-definition liveness belongs to different metadata")
	}
	if analysis.memorySSAFingerprint == "" || analysis.memorySSAFingerprint != memorySSA.integrity {
		return fmt.Errorf("optir: memory-definition liveness belongs to different memory SSA")
	}
	if analysis.observabilityFingerprint == "" || analysis.observabilityFingerprint != fingerprintRegionMemoryObservability(normalizedObservability) {
		return fmt.Errorf("optir: memory-definition liveness belongs to different observability")
	}
	if analysis.integrity == "" || analysis.integrity != fingerprintMemoryDefinitionLiveness(analysis) {
		return fmt.Errorf("optir: memory-definition liveness was mutated")
	}
	expected, err := buildMemoryDefinitionLiveness(cfg, memorySSA, normalizedObservability)
	if err != nil {
		return err
	}
	if !reflect.DeepEqual(analysis.LiveAccesses, expected.LiveAccesses) ||
		!reflect.DeepEqual(analysis.LiveVersions, expected.LiveVersions) ||
		!reflect.DeepEqual(analysis.DeadAccessCandidates, expected.DeadAccessCandidates) ||
		!reflect.DeepEqual(analysis.DeadVersionCandidates, expected.DeadVersionCandidates) {
		return fmt.Errorf("optir: memory-definition liveness does not match its inputs")
	}
	return nil
}

func normalizeRegionMemoryObservability(regions []RegionID, observability RegionMemoryObservability) (RegionMemoryObservability, error) {
	declared := make(map[RegionID]bool, len(regions))
	for _, region := range regions {
		declared[region] = true
	}
	liveOut := append([]RegionID(nil), observability.LiveOut...)
	sort.Slice(liveOut, func(i, j int) bool { return liveOut[i] < liveOut[j] })
	for index, region := range liveOut {
		if region == "" || !declared[region] {
			return RegionMemoryObservability{}, fmt.Errorf("optir: memory observability names undeclared region %q", region)
		}
		if index > 0 && liveOut[index-1] == region {
			return RegionMemoryObservability{}, fmt.Errorf("optir: memory observability repeats region %q", region)
		}
	}
	return RegionMemoryObservability{LiveOut: liveOut}, nil
}

func buildMemoryDefinitionLiveness(cfg CFG, memorySSA RegionMemorySSA, observability RegionMemoryObservability) (MemoryDefinitionLiveness, error) {
	accesses := make(map[MemoryAccessID]MemoryAccess, len(memorySSA.Accesses))
	versions := make(map[MemoryVersionID]MemoryVersion, len(memorySSA.Versions))
	for _, access := range memorySSA.Accesses {
		if access.ID == 0 || accesses[access.ID].ID != 0 {
			return MemoryDefinitionLiveness{}, fmt.Errorf("optir: memory liveness found invalid or duplicate access %d", access.ID)
		}
		accesses[access.ID] = access
	}
	for _, version := range memorySSA.Versions {
		if version.ID == 0 || versions[version.ID].ID != 0 {
			return MemoryDefinitionLiveness{}, fmt.Errorf("optir: memory liveness found invalid or duplicate version %d", version.ID)
		}
		versions[version.ID] = version
	}
	for _, access := range memorySSA.Accesses {
		input, ok := versions[access.Input]
		if !ok || input.Region != access.Region {
			return MemoryDefinitionLiveness{}, fmt.Errorf("optir: memory access %d has invalid input version %d", access.ID, access.Input)
		}
		if memoryAccessDefines(access.Kind) {
			output, ok := versions[access.Output]
			if !ok || output.Region != access.Region || output.Kind != MemoryVersionDefinition || output.Definition != access.ID {
				return MemoryDefinitionLiveness{}, fmt.Errorf("optir: memory access %d has invalid output version %d", access.ID, access.Output)
			}
		} else if access.Output != 0 {
			return MemoryDefinitionLiveness{}, fmt.Errorf("optir: read access %d unexpectedly defines version %d", access.ID, access.Output)
		}
	}
	for _, version := range memorySSA.Versions {
		switch version.Kind {
		case MemoryVersionEntry:
			if version.Definition != 0 || len(version.Incoming) != 0 {
				return MemoryDefinitionLiveness{}, fmt.Errorf("optir: entry memory version %d is malformed", version.ID)
			}
		case MemoryVersionDefinition:
			access, ok := accesses[version.Definition]
			if !ok || access.Output != version.ID || access.Region != version.Region {
				return MemoryDefinitionLiveness{}, fmt.Errorf("optir: definition memory version %d is malformed", version.ID)
			}
		case MemoryVersionPhi:
			if version.Definition != 0 || len(version.Incoming) == 0 {
				return MemoryDefinitionLiveness{}, fmt.Errorf("optir: phi memory version %d is malformed", version.ID)
			}
			for _, incoming := range version.Incoming {
				input, ok := versions[incoming.Version]
				if !ok || input.Region != version.Region {
					return MemoryDefinitionLiveness{}, fmt.Errorf("optir: phi memory version %d has invalid input %d", version.ID, incoming.Version)
				}
			}
		default:
			return MemoryDefinitionLiveness{}, fmt.Errorf("optir: memory version %d has unknown kind %q", version.ID, version.Kind)
		}
	}

	terminal, err := terminalMemoryVersions(cfg, memorySSA)
	if err != nil {
		return MemoryDefinitionLiveness{}, err
	}
	liveAccesses := map[MemoryAccessID]bool{}
	liveVersions := map[MemoryVersionID]bool{}
	work := make([]MemoryVersionID, 0, len(memorySSA.Versions))
	markVersion := func(version MemoryVersionID) error {
		if _, ok := versions[version]; !ok {
			return fmt.Errorf("optir: memory liveness root names missing version %d", version)
		}
		if !liveVersions[version] {
			liveVersions[version] = true
			work = append(work, version)
		}
		return nil
	}
	for _, access := range memorySSA.Accesses {
		switch access.Kind {
		case MemoryRead, MemoryReadWrite:
			liveAccesses[access.ID] = true
			if err := markVersion(access.Input); err != nil {
				return MemoryDefinitionLiveness{}, err
			}
		case MemoryUnknownClobber:
			// Opaque code may observe its input, and its output remains a
			// conservative definition even when the checked caller does not
			// expose this region at normal return.
			liveAccesses[access.ID] = true
			if err := markVersion(access.Input); err != nil {
				return MemoryDefinitionLiveness{}, err
			}
			if err := markVersion(access.Output); err != nil {
				return MemoryDefinitionLiveness{}, err
			}
		case MemoryWrite:
			// A write-only ModRef definition does not itself read its input.
		default:
			return MemoryDefinitionLiveness{}, fmt.Errorf("optir: memory access %d has unknown kind %q", access.ID, access.Kind)
		}
	}
	for _, block := range cfg.Blocks {
		if block.Terminator.Kind != TerminatorReturn {
			continue
		}
		for _, region := range observability.LiveOut {
			version := terminal[memoryVersionKey{block: block.ID, region: region}]
			if version == 0 {
				return MemoryDefinitionLiveness{}, fmt.Errorf("optir: return block %d has no terminal memory version for region %q", block.ID, region)
			}
			if err := markVersion(version); err != nil {
				return MemoryDefinitionLiveness{}, err
			}
		}
	}

	// Each version is appended at most once, so this worklist is bounded by
	// the validated graph cardinality even for cyclic phi webs.
	for cursor := 0; cursor < len(work); cursor++ {
		version := versions[work[cursor]]
		switch version.Kind {
		case MemoryVersionEntry:
		case MemoryVersionPhi:
			for _, incoming := range version.Incoming {
				if err := markVersion(incoming.Version); err != nil {
					return MemoryDefinitionLiveness{}, err
				}
			}
		case MemoryVersionDefinition:
			access := accesses[version.Definition]
			liveAccesses[access.ID] = true
			if access.Kind == MemoryReadWrite || access.Kind == MemoryUnknownClobber {
				if err := markVersion(access.Input); err != nil {
					return MemoryDefinitionLiveness{}, err
				}
			}
		default:
			return MemoryDefinitionLiveness{}, fmt.Errorf("optir: memory version %d has unknown kind %q", version.ID, version.Kind)
		}
	}

	result := MemoryDefinitionLiveness{
		LiveAccesses: sortedMemoryAccessSet(liveAccesses),
		LiveVersions: sortedMemoryVersionSet(liveVersions),
	}
	for _, access := range memorySSA.Accesses {
		if access.Kind == MemoryWrite && !liveVersions[access.Output] {
			result.DeadAccessCandidates = append(result.DeadAccessCandidates, access.ID)
			result.DeadVersionCandidates = append(result.DeadVersionCandidates, access.Output)
		}
	}
	return result, nil
}

func terminalMemoryVersions(cfg CFG, memorySSA RegionMemorySSA) (map[memoryVersionKey]MemoryVersionID, error) {
	blocks := make(map[BlockID]Block, len(cfg.Blocks))
	predecessors := make(map[BlockID][]BlockID, len(cfg.Blocks))
	for _, block := range cfg.Blocks {
		blocks[block.ID] = block
		edges, err := terminatorEdges(block.Terminator)
		if err != nil {
			return nil, err
		}
		for _, edge := range edges {
			predecessors[edge.Target] = appendUniqueBlock(predecessors[edge.Target], block.ID)
		}
	}
	entry := map[RegionID]MemoryVersionID{}
	phis := map[memoryVersionKey]MemoryVersionID{}
	for _, version := range memorySSA.Versions {
		switch version.Kind {
		case MemoryVersionEntry:
			entry[version.Region] = version.ID
		case MemoryVersionPhi:
			phis[memoryVersionKey{block: version.Block, region: version.Region}] = version.ID
		}
	}
	local := map[memoryVersionKey]MemoryVersionID{}
	for _, access := range memorySSA.Accesses {
		key := memoryVersionKey{block: access.Site.Block, region: access.Region}
		if local[key] == 0 {
			local[key] = access.Input
		}
		if access.Output != 0 {
			local[key] = access.Output
		}
	}

	terminal := map[memoryVersionKey]MemoryVersionID{}
	visiting := map[memoryVersionKey]bool{}
	var resolve func(memoryVersionKey) (MemoryVersionID, error)
	resolve = func(key memoryVersionKey) (MemoryVersionID, error) {
		if version := terminal[key]; version != 0 {
			return version, nil
		}
		if visiting[key] {
			return 0, fmt.Errorf("optir: terminal memory version cycle at block %d region %q has no phi", key.block, key.region)
		}
		visiting[key] = true
		defer delete(visiting, key)
		version := local[key]
		if version == 0 {
			version = phis[key]
		}
		if version == 0 && key.block == cfg.Entry {
			version = entry[key.region]
		}
		if version == 0 {
			incoming := predecessors[key.block]
			if len(incoming) != 1 {
				return 0, fmt.Errorf("optir: block %d region %q has %d predecessors but no memory phi", key.block, key.region, len(incoming))
			}
			var err error
			version, err = resolve(memoryVersionKey{block: incoming[0], region: key.region})
			if err != nil {
				return 0, err
			}
		}
		if version == 0 {
			return 0, fmt.Errorf("optir: block %d region %q has no terminal memory version", key.block, key.region)
		}
		terminal[key] = version
		return version, nil
	}
	for block := range blocks {
		for _, region := range memorySSA.Regions {
			if _, err := resolve(memoryVersionKey{block: block, region: region}); err != nil {
				return nil, err
			}
		}
	}
	return terminal, nil
}

func sortedMemoryAccessSet(values map[MemoryAccessID]bool) []MemoryAccessID {
	result := make([]MemoryAccessID, 0, len(values))
	for value := range values {
		result = append(result, value)
	}
	sort.Slice(result, func(i, j int) bool { return result[i] < result[j] })
	return result
}

func sortedMemoryVersionSet(values map[MemoryVersionID]bool) []MemoryVersionID {
	result := make([]MemoryVersionID, 0, len(values))
	for value := range values {
		result = append(result, value)
	}
	sort.Slice(result, func(i, j int) bool { return result[i] < result[j] })
	return result
}

func fingerprintRegionMemoryObservability(observability RegionMemoryObservability) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.region-memory-observability.v1")
	fingerprintUint64(digest, uint64(len(observability.LiveOut)))
	for _, region := range observability.LiveOut {
		fingerprintString(digest, string(region))
	}
	return fmt.Sprintf("%x", digest.Sum(nil))
}

func fingerprintMemoryDefinitionLiveness(analysis MemoryDefinitionLiveness) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.memory-definition-liveness.v1")
	fingerprintString(digest, analysis.inputFingerprint)
	fingerprintString(digest, analysis.metadataFingerprint)
	fingerprintString(digest, analysis.memorySSAFingerprint)
	fingerprintString(digest, analysis.observabilityFingerprint)
	fingerprintUint64(digest, uint64(len(analysis.LiveAccesses)))
	for _, access := range analysis.LiveAccesses {
		fingerprintUint64(digest, uint64(access))
	}
	fingerprintUint64(digest, uint64(len(analysis.LiveVersions)))
	for _, version := range analysis.LiveVersions {
		fingerprintUint64(digest, uint64(version))
	}
	fingerprintUint64(digest, uint64(len(analysis.DeadAccessCandidates)))
	for _, access := range analysis.DeadAccessCandidates {
		fingerprintUint64(digest, uint64(access))
	}
	fingerprintUint64(digest, uint64(len(analysis.DeadVersionCandidates)))
	for _, version := range analysis.DeadVersionCandidates {
		fingerprintUint64(digest, uint64(version))
	}
	return fmt.Sprintf("%x", digest.Sum(nil))
}
