package optir

import (
	"crypto/sha256"
	"fmt"
	"reflect"
	"sort"
)

// RegionID identifies one checked semantic memory region. Region identities
// are target independent; this analysis never manufactures aliasing facts from
// pointer spelling or operation operands.
type RegionID string

// MemoryAccessID identifies one normalized memory access. Zero is invalid.
type MemoryAccessID uint32

// MemoryVersionID identifies one memory definition or phi. Zero is invalid.
type MemoryVersionID uint32

// MemoryAccessKind is the complete ModRef vocabulary accepted by the first
// region-memory analysis. UnknownClobber is deliberately both a use and a
// definition of every declared region.
type MemoryAccessKind string

const (
	MemoryRead           MemoryAccessKind = "read"
	MemoryWrite          MemoryAccessKind = "write"
	MemoryReadWrite      MemoryAccessKind = "read-write"
	MemoryUnknownClobber MemoryAccessKind = "unknown-clobber"
)

// MemoryVersionKind distinguishes entry definitions, control-flow joins, and
// operation definitions.
type MemoryVersionKind string

const (
	MemoryVersionEntry      MemoryVersionKind = "entry"
	MemoryVersionPhi        MemoryVersionKind = "phi"
	MemoryVersionDefinition MemoryVersionKind = "definition"
)

// OperationSite identifies an operation in an exact CFG revision. Index is
// zero-based within Block.
type OperationSite struct {
	Block BlockID
	Index int
}

// MemoryAccessSpec is checked-projection metadata for one operation. Region
// must be declared for exact accesses. WholeRegion certifies that a write
// replaces the entire named semantic region rather than one location in a
// coarser region. Volatile makes the access intrinsically observable.
// UnknownClobber instead has an empty Region and is expanded conservatively to
// every declared region.
type MemoryAccessSpec struct {
	Region      RegionID
	Kind        MemoryAccessKind
	WholeRegion bool
	Volatile    bool
}

// MemoryOperationMetadata gives the complete memory behavior of one operation.
// Access order is not semantic: exact accesses to the same region are rejected,
// and the analysis canonicalizes distinct-region accesses by region identity.
type MemoryOperationMetadata struct {
	Site     OperationSite
	Accesses []MemoryAccessSpec
}

// RegionMemoryMetadata is the explicit input to region-memory analysis. It is
// intentionally separate from Operation.Effects: effects say that memory is
// observable, while this record supplies checked region identity. Missing
// metadata never implies purity.
type RegionMemoryMetadata struct {
	Regions    []RegionID
	Operations []MemoryOperationMetadata
}

// StructuredMemoryOperationMetadata binds checked memory behavior to the
// exact structured operation that produced it. The pointer identity is used
// only while ProjectWithRegionMemory constructs a CFG; the returned metadata
// contains stable CFG operation sites instead.
type StructuredMemoryOperationMetadata struct {
	Operation *Operation
	Accesses  []MemoryAccessSpec
}

// StructuredRegionMemoryMetadata is the lossless handoff between a checked
// structured projection and CFG region-memory analysis. It deliberately does
// not infer memory identity from source positions, operands, or operation
// spelling.
type StructuredRegionMemoryMetadata struct {
	Regions    []RegionID
	Operations []StructuredMemoryOperationMetadata
}

// MemoryIncoming is one incoming definition of a memory phi. Entry is true for
// the conceptual function-entry definition used when the CFG entry is also a
// loop header; otherwise Predecessor names the incoming CFG block.
type MemoryIncoming struct {
	Predecessor BlockID
	Version     MemoryVersionID
	Entry       bool
}

// MemoryVersion is one definition in region memory SSA. Definition is present
// only for MemoryVersionDefinition. Incoming is present only for a phi.
type MemoryVersion struct {
	ID         MemoryVersionID
	Region     RegionID
	Kind       MemoryVersionKind
	Block      BlockID
	Definition MemoryAccessID
	Incoming   []MemoryIncoming
}

// MemoryAccess is one normalized access. Input is the reaching memory
// definition. WholeRegion and Volatile preserve the checked projection
// contract used by later analyses. Output is nonzero exactly for write,
// read-write, and unknown-clobber accesses.
type MemoryAccess struct {
	ID          MemoryAccessID
	Site        OperationSite
	Region      RegionID
	Kind        MemoryAccessKind
	WholeRegion bool
	Volatile    bool
	Input       MemoryVersionID
	Output      MemoryVersionID
}

// RegionMemorySSA is analysis evidence, not permission to transform or emit.
// Its private identities bind every public record to an exact CFG and exact
// normalized metadata. VerifyRegionMemorySSA detects mutation and stale reuse.
type RegionMemorySSA struct {
	Regions  []RegionID
	Accesses []MemoryAccess
	Versions []MemoryVersion

	inputFingerprint    string
	metadataFingerprint string
	integrity           string
}

type normalizedMemoryMetadata struct {
	regions    []RegionID
	operations []MemoryOperationMetadata
	bySite     map[OperationSite][]MemoryAccessSpec
}

type memoryVersionKey struct {
	block  BlockID
	region RegionID
}

type memoryAccessKey struct {
	site   OperationSite
	region RegionID
}

// AnalyzeRegionMemorySSA constructs deterministic region-aware memory SSA from
// explicit checked metadata. It does not perform DSE, load forwarding, GVN, or
// any other transform, and its result cannot authorize emission.
func AnalyzeRegionMemorySSA(cfg CFG, metadata RegionMemoryMetadata) (RegionMemorySSA, error) {
	if err := validateAnalysisCFG(cfg); err != nil {
		return RegionMemorySSA{}, err
	}
	normalized, err := normalizeMemoryMetadata(cfg, metadata)
	if err != nil {
		return RegionMemorySSA{}, err
	}
	analysis, err := buildRegionMemorySSA(cfg, normalized)
	if err != nil {
		return RegionMemorySSA{}, err
	}
	analysis.inputFingerprint = fingerprintCFG(cfg)
	analysis.metadataFingerprint = fingerprintNormalizedMemoryMetadata(normalized)
	analysis.integrity = fingerprintRegionMemorySSA(analysis)
	return analysis, nil
}

// VerifyRegionMemorySSA independently validates the CFG and metadata, checks
// the evidence identities, and recomputes the canonical graph. This explicit
// gate prevents stale or mutated analysis data from becoming optimization
// evidence.
func VerifyRegionMemorySSA(cfg CFG, metadata RegionMemoryMetadata, analysis RegionMemorySSA) error {
	if err := validateAnalysisCFG(cfg); err != nil {
		return err
	}
	normalized, err := normalizeMemoryMetadata(cfg, metadata)
	if err != nil {
		return err
	}
	if analysis.inputFingerprint == "" || analysis.inputFingerprint != fingerprintCFG(cfg) {
		return fmt.Errorf("optir: region memory SSA belongs to a different CFG")
	}
	if analysis.metadataFingerprint == "" || analysis.metadataFingerprint != fingerprintNormalizedMemoryMetadata(normalized) {
		return fmt.Errorf("optir: region memory SSA belongs to different metadata")
	}
	if analysis.integrity == "" || analysis.integrity != fingerprintRegionMemorySSA(analysis) {
		return fmt.Errorf("optir: region memory SSA was mutated")
	}
	expected, err := buildRegionMemorySSA(cfg, normalized)
	if err != nil {
		return err
	}
	if !reflect.DeepEqual(analysis.Regions, expected.Regions) ||
		!reflect.DeepEqual(analysis.Accesses, expected.Accesses) ||
		!reflect.DeepEqual(analysis.Versions, expected.Versions) {
		return fmt.Errorf("optir: region memory SSA does not match its inputs")
	}
	return nil
}

func normalizeMemoryMetadata(cfg CFG, metadata RegionMemoryMetadata) (normalizedMemoryMetadata, error) {
	blocks := make(map[BlockID]*Block, len(cfg.Blocks))
	for index := range cfg.Blocks {
		blocks[cfg.Blocks[index].ID] = &cfg.Blocks[index]
	}

	regions := append([]RegionID(nil), metadata.Regions...)
	sort.Slice(regions, func(i, j int) bool { return regions[i] < regions[j] })
	regionSet := make(map[RegionID]bool, len(regions))
	for _, region := range regions {
		if region == "" {
			return normalizedMemoryMetadata{}, fmt.Errorf("optir: memory region identity is empty")
		}
		if regionSet[region] {
			return normalizedMemoryMetadata{}, fmt.Errorf("optir: memory region %q is declared more than once", region)
		}
		regionSet[region] = true
	}

	operations := make([]MemoryOperationMetadata, len(metadata.Operations))
	for index, operation := range metadata.Operations {
		operations[index] = MemoryOperationMetadata{
			Site:     operation.Site,
			Accesses: append([]MemoryAccessSpec(nil), operation.Accesses...),
		}
	}
	sort.Slice(operations, func(i, j int) bool {
		if operations[i].Site.Block != operations[j].Site.Block {
			return operations[i].Site.Block < operations[j].Site.Block
		}
		return operations[i].Site.Index < operations[j].Site.Index
	})

	bySite := make(map[OperationSite][]MemoryAccessSpec, len(operations))
	for index := range operations {
		operation := &operations[index]
		block, exists := blocks[operation.Site.Block]
		if !exists || operation.Site.Index < 0 || operation.Site.Index >= len(block.Operations) {
			return normalizedMemoryMetadata{}, fmt.Errorf("optir: memory metadata names missing operation %d:%d", operation.Site.Block, operation.Site.Index)
		}
		if _, exists := bySite[operation.Site]; exists {
			return normalizedMemoryMetadata{}, fmt.Errorf("optir: memory metadata repeats operation %d:%d", operation.Site.Block, operation.Site.Index)
		}
		if len(operation.Accesses) == 0 {
			return normalizedMemoryMetadata{}, fmt.Errorf("optir: memory metadata for operation %d:%d has no accesses", operation.Site.Block, operation.Site.Index)
		}
		unknown := false
		seenRegions := map[RegionID]bool{}
		for _, access := range operation.Accesses {
			switch access.Kind {
			case MemoryRead, MemoryWrite, MemoryReadWrite:
				if access.Region == "" || !regionSet[access.Region] {
					return normalizedMemoryMetadata{}, fmt.Errorf("optir: memory metadata for operation %d:%d names undeclared region %q", operation.Site.Block, operation.Site.Index, access.Region)
				}
				if seenRegions[access.Region] {
					return normalizedMemoryMetadata{}, fmt.Errorf("optir: memory metadata for operation %d:%d repeats region %q", operation.Site.Block, operation.Site.Index, access.Region)
				}
				seenRegions[access.Region] = true
				if access.WholeRegion && access.Kind == MemoryRead {
					return normalizedMemoryMetadata{}, fmt.Errorf("optir: memory metadata for operation %d:%d marks a read as a whole-region replacement", operation.Site.Block, operation.Site.Index)
				}
			case MemoryUnknownClobber:
				if access.Region != "" {
					return normalizedMemoryMetadata{}, fmt.Errorf("optir: unknown clobber for operation %d:%d cannot name region %q", operation.Site.Block, operation.Site.Index, access.Region)
				}
				unknown = true
				if access.WholeRegion {
					return normalizedMemoryMetadata{}, fmt.Errorf("optir: unknown clobber for operation %d:%d cannot be a whole-region replacement", operation.Site.Block, operation.Site.Index)
				}
			default:
				return normalizedMemoryMetadata{}, fmt.Errorf("optir: memory metadata for operation %d:%d has unknown access kind %q", operation.Site.Block, operation.Site.Index, access.Kind)
			}
		}
		if unknown {
			if len(operation.Accesses) != 1 {
				return normalizedMemoryMetadata{}, fmt.Errorf("optir: unknown clobber for operation %d:%d must be its only access", operation.Site.Block, operation.Site.Index)
			}
			if len(regions) == 0 {
				return normalizedMemoryMetadata{}, fmt.Errorf("optir: unknown clobber for operation %d:%d has no declared region to clobber", operation.Site.Block, operation.Site.Index)
			}
		} else {
			sort.Slice(operation.Accesses, func(i, j int) bool {
				return operation.Accesses[i].Region < operation.Accesses[j].Region
			})
		}
		bySite[operation.Site] = append([]MemoryAccessSpec(nil), operation.Accesses...)
	}

	for _, block := range cfg.Blocks {
		for index, operation := range block.Operations {
			site := OperationSite{Block: block.ID, Index: index}
			accesses, hasMetadata := bySite[site]
			if err := validateOperationMemoryMetadata(operation, accesses, hasMetadata); err != nil {
				return normalizedMemoryMetadata{}, fmt.Errorf("optir: block %d operation %d (%s): %w", block.ID, index, operation.Code, err)
			}
		}
	}

	return normalizedMemoryMetadata{regions: regions, operations: operations, bySite: bySite}, nil
}

func validateOperationMemoryMetadata(operation Operation, accesses []MemoryAccessSpec, hasMetadata bool) error {
	reads := false
	writes := false
	opaque := operation.Code == OpCall
	for _, effect := range operation.Effects {
		switch effect {
		case EffectReadMemory:
			reads = true
		case EffectWriteMemory:
			writes = true
		case EffectTrap:
			// Trapping changes control, not memory state.
		case EffectCall, EffectAllocate, EffectSynchronize:
			opaque = true
		default:
			opaque = true
		}
	}
	// An extension operation with no explicit memory effect is not silently
	// pure. Explicit read/write effects, however, are exactly the checked hook
	// this metadata-driven substrate uses until memory operations join the
	// closed core vocabulary.
	if !isKnownMemoryOperation(operation.Code) && !reads && !writes {
		opaque = true
	}
	if opaque {
		if !hasMetadata || len(accesses) != 1 || accesses[0].Kind != MemoryUnknownClobber {
			return fmt.Errorf("opaque operation requires one unknown-clobber access")
		}
		return nil
	}
	if !reads && !writes {
		if hasMetadata {
			return fmt.Errorf("operation without memory effects cannot carry region metadata")
		}
		return nil
	}
	if !hasMetadata {
		return fmt.Errorf("memory effect has no region metadata")
	}
	metadataReads := false
	metadataWrites := false
	for _, access := range accesses {
		switch access.Kind {
		case MemoryRead:
			metadataReads = true
		case MemoryWrite:
			metadataWrites = true
		case MemoryReadWrite:
			metadataReads = true
			metadataWrites = true
		case MemoryUnknownClobber:
			return fmt.Errorf("non-opaque memory effect cannot use an unknown clobber")
		}
	}
	if reads != metadataReads || writes != metadataWrites {
		return fmt.Errorf("region metadata ModRef does not match operation effects")
	}
	return nil
}

func isKnownMemoryOperation(code string) bool {
	switch code {
	case OpConstBool, OpConstInt, OpConstUnit, OpCopy, OpCastInt,
		OpBoolNot, OpIntNeg, OpIntAdd, OpIntSub, OpIntMul, OpIntDiv, OpIntRem,
		OpIntAnd, OpIntOr, OpIntXor, OpIntShl, OpIntShr,
		OpEqual, OpNotEqual, OpLess, OpLessEqual, OpGreater, OpGreaterEqual,
		OpStoreRegion:
		return true
	default:
		return false
	}
}

func buildRegionMemorySSA(cfg CFG, metadata normalizedMemoryMetadata) (RegionMemorySSA, error) {
	analysis := RegionMemorySSA{Regions: append([]RegionID(nil), metadata.regions...)}
	if len(metadata.regions) == 0 {
		return analysis, nil
	}

	blocks := make(map[BlockID]*Block, len(cfg.Blocks))
	predecessors := make(map[BlockID][]BlockID, len(cfg.Blocks))
	for index := range cfg.Blocks {
		block := &cfg.Blocks[index]
		blocks[block.ID] = block
		edges, _ := terminatorEdges(block.Terminator)
		for _, edge := range edges {
			predecessors[edge.Target] = appendUniqueBlock(predecessors[edge.Target], block.ID)
		}
	}
	for block := range predecessors {
		sort.Slice(predecessors[block], func(i, j int) bool { return predecessors[block][i] < predecessors[block][j] })
	}

	blockIDs := make([]BlockID, 0, len(blocks))
	for block := range blocks {
		blockIDs = append(blockIDs, block)
	}
	sort.Slice(blockIDs, func(i, j int) bool { return blockIDs[i] < blockIDs[j] })

	nextVersion := MemoryVersionID(1)
	entryVersions := make(map[RegionID]MemoryVersionID, len(metadata.regions))
	for _, region := range metadata.regions {
		version, err := allocateMemoryVersion(&nextVersion)
		if err != nil {
			return RegionMemorySSA{}, err
		}
		entryVersions[region] = version
		analysis.Versions = append(analysis.Versions, MemoryVersion{
			ID: version, Region: region, Kind: MemoryVersionEntry, Block: cfg.Entry,
		})
	}

	phiVersions := map[memoryVersionKey]MemoryVersionID{}
	for _, block := range blockIDs {
		needsPhi := len(predecessors[block]) > 1 || block == cfg.Entry && len(predecessors[block]) > 0
		if !needsPhi {
			continue
		}
		for _, region := range metadata.regions {
			version, err := allocateMemoryVersion(&nextVersion)
			if err != nil {
				return RegionMemorySSA{}, err
			}
			phiVersions[memoryVersionKey{block: block, region: region}] = version
			analysis.Versions = append(analysis.Versions, MemoryVersion{
				ID: version, Region: region, Kind: MemoryVersionPhi, Block: block,
			})
		}
	}

	expanded := make(map[OperationSite][]MemoryAccessSpec, len(metadata.bySite))
	for site, accesses := range metadata.bySite {
		if len(accesses) == 1 && accesses[0].Kind == MemoryUnknownClobber {
			for _, region := range metadata.regions {
				expanded[site] = append(expanded[site], MemoryAccessSpec{
					Region: region, Kind: MemoryUnknownClobber, Volatile: accesses[0].Volatile,
				})
			}
			continue
		}
		expanded[site] = append([]MemoryAccessSpec(nil), accesses...)
	}

	nextAccess := MemoryAccessID(1)
	accessIDs := map[memoryAccessKey]MemoryAccessID{}
	definitionVersions := map[memoryAccessKey]MemoryVersionID{}
	for _, block := range blockIDs {
		for index := range blocks[block].Operations {
			site := OperationSite{Block: block, Index: index}
			for _, access := range expanded[site] {
				key := memoryAccessKey{site: site, region: access.Region}
				accessID, err := allocateMemoryAccess(&nextAccess)
				if err != nil {
					return RegionMemorySSA{}, err
				}
				accessIDs[key] = accessID
				if memoryAccessDefines(access.Kind) {
					version, err := allocateMemoryVersion(&nextVersion)
					if err != nil {
						return RegionMemorySSA{}, err
					}
					definitionVersions[key] = version
				}
			}
		}
	}

	blockOutputs := make(map[BlockID]map[RegionID]MemoryVersionID, len(blocks))
	order := loopReversePostOrder(cfg.Entry, blocks)
	for _, blockID := range order {
		current := make(map[RegionID]MemoryVersionID, len(metadata.regions))
		for _, region := range metadata.regions {
			if phi := phiVersions[memoryVersionKey{block: blockID, region: region}]; phi != 0 {
				current[region] = phi
				continue
			}
			switch {
			case blockID == cfg.Entry:
				current[region] = entryVersions[region]
			case len(predecessors[blockID]) == 1:
				predecessorOutput := blockOutputs[predecessors[blockID][0]]
				if predecessorOutput == nil || predecessorOutput[region] == 0 {
					return RegionMemorySSA{}, fmt.Errorf("optir: cannot resolve memory input for block %d region %q", blockID, region)
				}
				current[region] = predecessorOutput[region]
			default:
				return RegionMemorySSA{}, fmt.Errorf("optir: block %d region %q has no memory input", blockID, region)
			}
		}

		block := blocks[blockID]
		for index := range block.Operations {
			site := OperationSite{Block: blockID, Index: index}
			for _, spec := range expanded[site] {
				key := memoryAccessKey{site: site, region: spec.Region}
				access := MemoryAccess{
					ID: accessIDs[key], Site: site, Region: spec.Region, Kind: spec.Kind,
					WholeRegion: spec.WholeRegion, Volatile: spec.Volatile, Input: current[spec.Region],
				}
				if access.Input == 0 {
					return RegionMemorySSA{}, fmt.Errorf("optir: memory access %d has no reaching definition", access.ID)
				}
				if memoryAccessDefines(spec.Kind) {
					access.Output = definitionVersions[key]
					current[spec.Region] = access.Output
					analysis.Versions = append(analysis.Versions, MemoryVersion{
						ID: access.Output, Region: spec.Region, Kind: MemoryVersionDefinition,
						Block: blockID, Definition: access.ID,
					})
				}
				analysis.Accesses = append(analysis.Accesses, access)
			}
		}
		blockOutputs[blockID] = current
	}

	versionsByID := make(map[MemoryVersionID]*MemoryVersion, len(analysis.Versions))
	for index := range analysis.Versions {
		versionsByID[analysis.Versions[index].ID] = &analysis.Versions[index]
	}
	for key, phiID := range phiVersions {
		phi := versionsByID[phiID]
		if key.block == cfg.Entry {
			phi.Incoming = append(phi.Incoming, MemoryIncoming{Version: entryVersions[key.region], Entry: true})
		}
		for _, predecessor := range predecessors[key.block] {
			version := blockOutputs[predecessor][key.region]
			if version == 0 {
				return RegionMemorySSA{}, fmt.Errorf("optir: memory phi %d has unresolved predecessor %d", phiID, predecessor)
			}
			phi.Incoming = append(phi.Incoming, MemoryIncoming{Predecessor: predecessor, Version: version})
		}
	}

	sort.Slice(analysis.Accesses, func(i, j int) bool { return analysis.Accesses[i].ID < analysis.Accesses[j].ID })
	sort.Slice(analysis.Versions, func(i, j int) bool { return analysis.Versions[i].ID < analysis.Versions[j].ID })
	return analysis, nil
}

func appendUniqueBlock(blocks []BlockID, block BlockID) []BlockID {
	for _, existing := range blocks {
		if existing == block {
			return blocks
		}
	}
	return append(blocks, block)
}

func memoryAccessDefines(kind MemoryAccessKind) bool {
	return kind == MemoryWrite || kind == MemoryReadWrite || kind == MemoryUnknownClobber
}

func allocateMemoryVersion(next *MemoryVersionID) (MemoryVersionID, error) {
	if *next == 0 {
		return 0, fmt.Errorf("optir: memory version identity overflow")
	}
	result := *next
	*next++
	return result, nil
}

func allocateMemoryAccess(next *MemoryAccessID) (MemoryAccessID, error) {
	if *next == 0 {
		return 0, fmt.Errorf("optir: memory access identity overflow")
	}
	result := *next
	*next++
	return result, nil
}

func fingerprintNormalizedMemoryMetadata(metadata normalizedMemoryMetadata) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.region-memory-metadata.v2")
	fingerprintUint64(digest, uint64(len(metadata.regions)))
	for _, region := range metadata.regions {
		fingerprintString(digest, string(region))
	}
	fingerprintUint64(digest, uint64(len(metadata.operations)))
	for _, operation := range metadata.operations {
		fingerprintUint64(digest, uint64(operation.Site.Block))
		fingerprintUint64(digest, uint64(operation.Site.Index))
		fingerprintUint64(digest, uint64(len(operation.Accesses)))
		for _, access := range operation.Accesses {
			fingerprintString(digest, string(access.Region))
			fingerprintString(digest, string(access.Kind))
			fingerprintBool(digest, access.WholeRegion)
			fingerprintBool(digest, access.Volatile)
		}
	}
	return fmt.Sprintf("%x", digest.Sum(nil))
}

func fingerprintRegionMemorySSA(analysis RegionMemorySSA) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.region-memory-ssa.v2")
	fingerprintString(digest, analysis.inputFingerprint)
	fingerprintString(digest, analysis.metadataFingerprint)
	fingerprintUint64(digest, uint64(len(analysis.Regions)))
	for _, region := range analysis.Regions {
		fingerprintString(digest, string(region))
	}
	fingerprintUint64(digest, uint64(len(analysis.Accesses)))
	for _, access := range analysis.Accesses {
		fingerprintUint64(digest, uint64(access.ID))
		fingerprintUint64(digest, uint64(access.Site.Block))
		fingerprintUint64(digest, uint64(access.Site.Index))
		fingerprintString(digest, string(access.Region))
		fingerprintString(digest, string(access.Kind))
		fingerprintBool(digest, access.WholeRegion)
		fingerprintBool(digest, access.Volatile)
		fingerprintUint64(digest, uint64(access.Input))
		fingerprintUint64(digest, uint64(access.Output))
	}
	fingerprintUint64(digest, uint64(len(analysis.Versions)))
	for _, version := range analysis.Versions {
		fingerprintUint64(digest, uint64(version.ID))
		fingerprintString(digest, string(version.Region))
		fingerprintString(digest, string(version.Kind))
		fingerprintUint64(digest, uint64(version.Block))
		fingerprintUint64(digest, uint64(version.Definition))
		fingerprintUint64(digest, uint64(len(version.Incoming)))
		for _, incoming := range version.Incoming {
			fingerprintUint64(digest, uint64(incoming.Predecessor))
			fingerprintUint64(digest, uint64(incoming.Version))
			fingerprintBool(digest, incoming.Entry)
		}
	}
	return fmt.Sprintf("%x", digest.Sum(nil))
}
