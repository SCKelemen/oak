package optir

import (
	"crypto/sha256"
	"fmt"
	"hash"
	"reflect"
	"sort"
)

// RegionLoadForwardingKind records which exact MemorySSA definition supplied
// a removed load's value.
type RegionLoadForwardingKind string

const (
	RegionLoadFromLoad  RegionLoadForwardingKind = "load"
	RegionLoadFromStore RegionLoadForwardingKind = "store"
)

// RegionLoadReplacement identifies one removed closed region load and the SSA
// value that replaces its sole result.
type RegionLoadReplacement struct {
	Access      MemoryAccessID
	Site        OperationSite
	Region      RegionID
	Memory      MemoryVersionID
	Result      ValueID
	Replacement ValueID
	Kind        RegionLoadForwardingKind
}

// RegionLoadForwardingReport is deterministic transform evidence, not a
// semantic-equivalence verdict. Its private identities bind the report to the
// exact input CFG, metadata, MemorySSA, and output revision.
type RegionLoadForwardingReport struct {
	Replacements []RegionLoadReplacement
	DroppedFacts int

	inputFingerprint          string
	metadataFingerprint       string
	memorySSAFingerprint      string
	outputFingerprint         string
	outputMetadataFingerprint string
	integrity                 string
}

func (report RegionLoadForwardingReport) Changes() int { return len(report.Replacements) }

// ForwardRegionLoads removes only canonical, nonvolatile region loads whose
// exact MemorySSA input proves their value is already available from either a
// dominating load of the same version or the operand of the dominating whole-
// region store that defined that version. No alias or address fact is inferred.
func ForwardRegionLoads(
	cfg CFG,
	metadata RegionMemoryMetadata,
	memorySSA RegionMemorySSA,
) (CFG, RegionMemoryMetadata, RegionLoadForwardingReport, error) {
	if err := VerifyRegionMemorySSA(cfg, metadata, memorySSA); err != nil {
		return CFG{}, RegionMemoryMetadata{}, RegionLoadForwardingReport{}, err
	}
	normalized, err := normalizeMemoryMetadata(cfg, metadata)
	if err != nil {
		return CFG{}, RegionMemoryMetadata{}, RegionLoadForwardingReport{}, err
	}
	result, resultMetadata, report, err := forwardRegionLoads(cfg, normalized, memorySSA)
	if err != nil {
		return CFG{}, RegionMemoryMetadata{}, RegionLoadForwardingReport{}, err
	}
	outputMetadata, err := normalizeMemoryMetadata(result, resultMetadata)
	if err != nil {
		return CFG{}, RegionMemoryMetadata{}, RegionLoadForwardingReport{}, fmt.Errorf("optir: region load forwarding produced invalid metadata: %w", err)
	}
	report.inputFingerprint = fingerprintCFG(cfg)
	report.metadataFingerprint = fingerprintNormalizedMemoryMetadata(normalized)
	report.memorySSAFingerprint = memorySSA.integrity
	report.outputFingerprint = fingerprintCFG(result)
	report.outputMetadataFingerprint = fingerprintNormalizedMemoryMetadata(outputMetadata)
	report.integrity = fingerprintRegionLoadForwardingReport(report)
	return result, resultMetadata, report, nil
}

// VerifyRegionLoadForwarding checks all prerequisite and result identities,
// rebuilds output MemorySSA, and independently reruns the complete transform.
// Native emission still requires semantic translation validation.
func VerifyRegionLoadForwarding(
	cfg CFG,
	metadata RegionMemoryMetadata,
	memorySSA RegionMemorySSA,
	result CFG,
	resultMetadata RegionMemoryMetadata,
	report RegionLoadForwardingReport,
) error {
	if err := VerifyRegionMemorySSA(cfg, metadata, memorySSA); err != nil {
		return err
	}
	normalized, err := normalizeMemoryMetadata(cfg, metadata)
	if err != nil {
		return err
	}
	if err := validateAnalysisCFG(result); err != nil {
		return fmt.Errorf("optir: region load forwarding result is invalid: %w", err)
	}
	normalizedOutput, err := normalizeMemoryMetadata(result, resultMetadata)
	if err != nil {
		return fmt.Errorf("optir: region load forwarding result metadata is invalid: %w", err)
	}
	if _, err := AnalyzeRegionMemorySSA(result, resultMetadata); err != nil {
		return fmt.Errorf("optir: region load forwarding result memory SSA is invalid: %w", err)
	}
	if report.inputFingerprint == "" || report.inputFingerprint != fingerprintCFG(cfg) {
		return fmt.Errorf("optir: region load forwarding report belongs to a different input CFG")
	}
	if report.metadataFingerprint == "" || report.metadataFingerprint != fingerprintNormalizedMemoryMetadata(normalized) {
		return fmt.Errorf("optir: region load forwarding report belongs to different input metadata")
	}
	if report.memorySSAFingerprint == "" || report.memorySSAFingerprint != memorySSA.integrity {
		return fmt.Errorf("optir: region load forwarding report belongs to different memory SSA")
	}
	if report.outputFingerprint == "" || report.outputFingerprint != fingerprintCFG(result) {
		return fmt.Errorf("optir: region load forwarding report belongs to a different output CFG")
	}
	if report.outputMetadataFingerprint == "" || report.outputMetadataFingerprint != fingerprintNormalizedMemoryMetadata(normalizedOutput) {
		return fmt.Errorf("optir: region load forwarding report belongs to different output metadata")
	}
	if report.integrity == "" || report.integrity != fingerprintRegionLoadForwardingReport(report) {
		return fmt.Errorf("optir: region load forwarding report was mutated")
	}
	expectedCFG, expectedMetadata, expectedReport, err := forwardRegionLoads(cfg, normalized, memorySSA)
	if err != nil {
		return err
	}
	if !reflect.DeepEqual(result, expectedCFG) || !reflect.DeepEqual(resultMetadata, expectedMetadata) ||
		!reflect.DeepEqual(report.Replacements, expectedReport.Replacements) || report.DroppedFacts != expectedReport.DroppedFacts {
		return fmt.Errorf("optir: region load forwarding result does not match its inputs")
	}
	return nil
}

type regionLoadKey struct {
	region RegionID
	memory MemoryVersionID
	typ    Type
}

type availableRegionLoad struct {
	location operationLocation
	result   ValueID
}

func forwardRegionLoads(
	cfg CFG,
	metadata normalizedMemoryMetadata,
	memorySSA RegionMemorySSA,
) (CFG, RegionMemoryMetadata, RegionLoadForwardingReport, error) {
	definitions, predecessors := transformGraphInfo(cfg)
	reachable := make(map[BlockID]bool, len(cfg.Blocks))
	blocks := make(map[BlockID]*Block, len(cfg.Blocks))
	for index := range cfg.Blocks {
		block := &cfg.Blocks[index]
		reachable[block.ID] = true
		blocks[block.ID] = block
	}
	dominators := computeDominators(cfg.Entry, reachable, predecessors)

	accessesBySite := make(map[OperationSite][]MemoryAccess)
	accessesByID := make(map[MemoryAccessID]MemoryAccess, len(memorySSA.Accesses))
	for _, access := range memorySSA.Accesses {
		accessesBySite[access.Site] = append(accessesBySite[access.Site], access)
		accessesByID[access.ID] = access
	}
	versions := make(map[MemoryVersionID]MemoryVersion, len(memorySSA.Versions))
	for _, version := range memorySSA.Versions {
		versions[version.ID] = version
	}

	type blockOrder struct {
		id    BlockID
		depth int
	}
	order := make([]blockOrder, 0, len(cfg.Blocks))
	for _, block := range cfg.Blocks {
		order = append(order, blockOrder{id: block.ID, depth: len(dominators[block.ID])})
	}
	sort.Slice(order, func(i, j int) bool {
		if order[i].depth != order[j].depth {
			return order[i].depth < order[j].depth
		}
		return order[i].id < order[j].id
	})

	available := map[regionLoadKey][]availableRegionLoad{}
	replacements := map[ValueID]ValueID{}
	removed := map[OperationSite]bool{}
	report := RegionLoadForwardingReport{}
	for _, ordered := range order {
		block := blocks[ordered.id]
		for index, operation := range block.Operations {
			site := OperationSite{Block: block.ID, Index: index}
			accesses := accessesBySite[site]
			if !canonicalForwardableRegionLoad(operation, accesses) {
				continue
			}
			access := accesses[0]
			result := operation.Results[0]
			key := regionLoadKey{region: access.Region, memory: access.Input, typ: result.Type}
			current := operationLocation{block: block.ID, index: index}
			replacement, kind := storedRegionValue(access.Input, access.Region, result.Type, current, blocks, metadata, versions, accessesByID, definitions, dominators, replacements)
			if replacement == 0 {
				for candidateIndex := len(available[key]) - 1; candidateIndex >= 0; candidateIndex-- {
					candidate := available[key][candidateIndex]
					if locationDominates(candidate.location.block, candidate.location.index, current.block, current.index, dominators) {
						replacement = candidate.result
						kind = RegionLoadFromLoad
						break
					}
				}
			}
			if replacement == 0 {
				available[key] = append(available[key], availableRegionLoad{location: current, result: result.ID})
				continue
			}
			replacements[result.ID] = replacement
			removed[site] = true
			report.Replacements = append(report.Replacements, RegionLoadReplacement{
				Access: access.ID, Site: site, Region: access.Region, Memory: access.Input,
				Result: result.ID, Replacement: replacement, Kind: kind,
			})
		}
	}

	result := cloneCFG(cfg)
	siteRemap := make(map[OperationSite]OperationSite, len(metadata.operations))
	for blockIndex := range result.Blocks {
		block := &result.Blocks[blockIndex]
		operations := make([]Operation, 0, len(block.Operations))
		for operationIndex, operation := range block.Operations {
			oldSite := OperationSite{Block: block.ID, Index: operationIndex}
			if removed[oldSite] {
				report.DroppedFacts += len(operation.Facts)
				continue
			}
			operation.Facts, report.DroppedFacts = dropReplacementFacts(operation.Facts, replacements, report.DroppedFacts)
			siteRemap[oldSite] = OperationSite{Block: block.ID, Index: len(operations)}
			operations = append(operations, operation)
		}
		block.Operations = operations
	}
	result.Facts, report.DroppedFacts = dropReplacementFacts(result.Facts, replacements, report.DroppedFacts)
	remapCFGUses(&result, replacements)

	resultMetadata := RegionMemoryMetadata{Regions: append([]RegionID(nil), metadata.regions...)}
	for _, operation := range metadata.operations {
		if removed[operation.Site] {
			continue
		}
		newSite, ok := siteRemap[operation.Site]
		if !ok {
			return CFG{}, RegionMemoryMetadata{}, RegionLoadForwardingReport{}, fmt.Errorf("optir: region load forwarding could not remap memory operation %d:%d", operation.Site.Block, operation.Site.Index)
		}
		resultMetadata.Operations = append(resultMetadata.Operations, MemoryOperationMetadata{
			Site:       newSite,
			Accesses:   append([]MemoryAccessSpec(nil), operation.Accesses...),
			CallEffect: operation.CallEffect,
		})
	}
	if err := validateAnalysisCFG(result); err != nil {
		return CFG{}, RegionMemoryMetadata{}, RegionLoadForwardingReport{}, fmt.Errorf("optir: region load forwarding produced invalid CFG: %w", err)
	}
	if _, err := AnalyzeRegionMemorySSA(result, resultMetadata); err != nil {
		return CFG{}, RegionMemoryMetadata{}, RegionLoadForwardingReport{}, fmt.Errorf("optir: region load forwarding produced invalid memory graph: %w", err)
	}
	return result, resultMetadata, report, nil
}

func canonicalForwardableRegionLoad(operation Operation, accesses []MemoryAccess) bool {
	return len(accesses) == 1 && accesses[0].Kind == MemoryRead && !accesses[0].WholeRegion && !accesses[0].Volatile &&
		operation.Code == OpLoadRegion && len(operation.Results) == 1 && len(operation.Operands) == 0 && len(operation.Attributes) == 0 &&
		len(operation.Effects) == 1 && operation.Effects[0] == EffectReadMemory
}

func storedRegionValue(
	memory MemoryVersionID,
	region RegionID,
	typ Type,
	use operationLocation,
	blocks map[BlockID]*Block,
	metadata normalizedMemoryMetadata,
	versions map[MemoryVersionID]MemoryVersion,
	accesses map[MemoryAccessID]MemoryAccess,
	definitions map[ValueID]definition,
	dominators map[BlockID]map[BlockID]bool,
	replacements map[ValueID]ValueID,
) (ValueID, RegionLoadForwardingKind) {
	version, exists := versions[memory]
	if !exists || version.Kind != MemoryVersionDefinition || version.Region != region {
		return 0, ""
	}
	access, exists := accesses[version.Definition]
	if !exists || access.Output != memory || access.Region != region || access.Kind != MemoryWrite || !access.WholeRegion || access.Volatile {
		return 0, ""
	}
	operationAccesses := metadata.bySite[access.Site]
	if len(operationAccesses) != 1 || operationAccesses[0].Kind != MemoryWrite || !operationAccesses[0].WholeRegion || operationAccesses[0].Volatile {
		return 0, ""
	}
	block := blocks[access.Site.Block]
	if block == nil || access.Site.Index < 0 || access.Site.Index >= len(block.Operations) {
		return 0, ""
	}
	operation := &block.Operations[access.Site.Index]
	if operation.Code != OpStoreRegion || len(operation.Results) != 0 || len(operation.Operands) != 1 ||
		len(operation.Attributes) != 0 || len(operation.Effects) != 1 || operation.Effects[0] != EffectWriteMemory {
		return 0, ""
	}
	storeLocation := operationLocation{block: access.Site.Block, index: access.Site.Index}
	if !locationDominates(storeLocation.block, storeLocation.index, use.block, use.index, dominators) {
		return 0, ""
	}
	value := resolveReplacement(operation.Operands[0], replacements)
	definition, exists := definitions[value]
	if !exists || definition.typeOf != typ || !locationDominates(definition.block, definition.index, use.block, use.index, dominators) {
		return 0, ""
	}
	return value, RegionLoadFromStore
}

func dropReplacementFacts(facts []Fact, replacements map[ValueID]ValueID, dropped int) ([]Fact, int) {
	kept := make([]Fact, 0, len(facts))
	for _, fact := range facts {
		remove := false
		for _, value := range fact.Values {
			if _, replaced := replacements[value]; replaced {
				remove = true
				break
			}
		}
		if remove {
			dropped++
			continue
		}
		kept = append(kept, fact)
	}
	return kept, dropped
}

func fingerprintRegionLoadForwardingReport(report RegionLoadForwardingReport) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.region-load-forwarding.v4")
	fingerprintString(digest, report.inputFingerprint)
	fingerprintString(digest, report.metadataFingerprint)
	fingerprintString(digest, report.memorySSAFingerprint)
	fingerprintString(digest, report.outputFingerprint)
	fingerprintString(digest, report.outputMetadataFingerprint)
	fingerprintUint64(digest, uint64(len(report.Replacements)))
	for _, replacement := range report.Replacements {
		fingerprintRegionLoadReplacement(digest, replacement)
	}
	fingerprintUint64(digest, uint64(report.DroppedFacts))
	return fmt.Sprintf("%x", digest.Sum(nil))
}

func fingerprintRegionLoadReplacement(digest hash.Hash, replacement RegionLoadReplacement) {
	fingerprintUint64(digest, uint64(replacement.Access))
	fingerprintUint64(digest, uint64(replacement.Site.Block))
	fingerprintUint64(digest, uint64(replacement.Site.Index))
	fingerprintString(digest, string(replacement.Region))
	fingerprintUint64(digest, uint64(replacement.Memory))
	fingerprintUint64(digest, uint64(replacement.Result))
	fingerprintUint64(digest, uint64(replacement.Replacement))
	fingerprintString(digest, string(replacement.Kind))
}
