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
	RegionLoadFromPhi   RegionLoadForwardingKind = "memory-phi"
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
// exact MemorySSA input proves their value is already available from a
// dominating load, a dominating whole-region store, or a memory phi whose
// every real predecessor already has the exact typed value from either such a
// store or a canonical load of its incoming version. The phi case creates an
// SSA block parameter and supplies each available value on its exact edge, so
// it covers closed joins and loop-carried values without inserting a load.
// Conceptual function-entry inputs remain unavailable. No load is inserted or
// speculated, and no alias or address fact is inferred.
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

type regionLoadPhiPlan struct {
	block     BlockID
	parameter Value
	incoming  []regionLoadPhiIncoming
}

type regionLoadPhiIncoming struct {
	predecessor BlockID
	value       ValueID
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
	nextValue := nextRegionLoadValueID(cfg)

	accessesBySite := make(map[OperationSite][]MemoryAccess)
	accessesByID := make(map[MemoryAccessID]MemoryAccess, len(memorySSA.Accesses))
	for _, access := range memorySSA.Accesses {
		accessesBySite[access.Site] = append(accessesBySite[access.Site], access)
		accessesByID[access.ID] = access
	}
	edgeLoads := indexRegionLoads(cfg, accessesBySite)
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
	phiPlans := map[regionLoadKey]*regionLoadPhiPlan{}
	var plannedPhis []*regionLoadPhiPlan
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
				plan := phiPlans[key]
				if plan == nil {
					planned, planErr := planRegionLoadPhi(
						access.Input, access.Region, result, current, blocks, metadata, versions,
						accessesByID, definitions, dominators, edgeLoads, replacements, &nextValue,
					)
					if planErr != nil {
						return CFG{}, RegionMemoryMetadata{}, RegionLoadForwardingReport{}, planErr
					}
					plan = planned
					if plan != nil {
						phiPlans[key] = plan
						plannedPhis = append(plannedPhis, plan)
						definitions[plan.parameter.ID] = definition{typeOf: plan.parameter.Type, block: plan.block, index: -1}
					}
				}
				if plan != nil {
					replacement = plan.parameter.ID
					kind = RegionLoadFromPhi
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
	resultBlocks := make(map[BlockID]*Block, len(result.Blocks))
	for index := range result.Blocks {
		resultBlocks[result.Blocks[index].ID] = &result.Blocks[index]
	}
	for _, plan := range plannedPhis {
		block := resultBlocks[plan.block]
		if block == nil {
			return CFG{}, RegionMemoryMetadata{}, RegionLoadForwardingReport{}, fmt.Errorf("optir: region load forwarding phi plan names a missing block %d", plan.block)
		}
		block.Parameters = append(block.Parameters, plan.parameter)
		for _, incoming := range plan.incoming {
			predecessor := resultBlocks[incoming.predecessor]
			value := resolveReplacement(incoming.value, replacements)
			if predecessor == nil || value == 0 || appendRegionLoadEdgeArgument(&predecessor.Terminator, plan.block, value) == 0 {
				return CFG{}, RegionMemoryMetadata{}, RegionLoadForwardingReport{}, fmt.Errorf("optir: region load forwarding phi has no edge from block %d to %d", incoming.predecessor, plan.block)
			}
		}
	}
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

func indexRegionLoads(cfg CFG, accessesBySite map[OperationSite][]MemoryAccess) map[regionLoadKey][]availableRegionLoad {
	loads := map[regionLoadKey][]availableRegionLoad{}
	for _, block := range cfg.Blocks {
		for index, operation := range block.Operations {
			site := OperationSite{Block: block.ID, Index: index}
			accesses := accessesBySite[site]
			if !canonicalForwardableRegionLoad(operation, accesses) {
				continue
			}
			access := accesses[0]
			result := operation.Results[0]
			key := regionLoadKey{region: access.Region, memory: access.Input, typ: result.Type}
			loads[key] = append(loads[key], availableRegionLoad{
				location: operationLocation{block: block.ID, index: index},
				result:   result.ID,
			})
		}
	}
	return loads
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
	value, storeLocation, exists := canonicalStoredRegionValue(memory, region, typ, blocks, metadata, versions, accesses, definitions, replacements)
	if !exists || !locationDominates(storeLocation.block, storeLocation.index, use.block, use.index, dominators) {
		return 0, ""
	}
	definition := definitions[value]
	if !locationDominates(definition.block, definition.index, use.block, use.index, dominators) {
		return 0, ""
	}
	return value, RegionLoadFromStore
}

func canonicalStoredRegionValue(
	memory MemoryVersionID,
	region RegionID,
	typ Type,
	blocks map[BlockID]*Block,
	metadata normalizedMemoryMetadata,
	versions map[MemoryVersionID]MemoryVersion,
	accesses map[MemoryAccessID]MemoryAccess,
	definitions map[ValueID]definition,
	replacements map[ValueID]ValueID,
) (ValueID, operationLocation, bool) {
	version, exists := versions[memory]
	if !exists || version.Kind != MemoryVersionDefinition || version.Region != region {
		return 0, operationLocation{}, false
	}
	access, exists := accesses[version.Definition]
	if !exists || access.Output != memory || access.Region != region || access.Kind != MemoryWrite || !access.WholeRegion || access.Volatile {
		return 0, operationLocation{}, false
	}
	operationAccesses := metadata.bySite[access.Site]
	if len(operationAccesses) != 1 || operationAccesses[0].Kind != MemoryWrite || !operationAccesses[0].WholeRegion || operationAccesses[0].Volatile {
		return 0, operationLocation{}, false
	}
	block := blocks[access.Site.Block]
	if block == nil || access.Site.Index < 0 || access.Site.Index >= len(block.Operations) {
		return 0, operationLocation{}, false
	}
	operation := &block.Operations[access.Site.Index]
	if operation.Code != OpStoreRegion || len(operation.Results) != 0 || len(operation.Operands) != 1 ||
		len(operation.Attributes) != 0 || len(operation.Effects) != 1 || operation.Effects[0] != EffectWriteMemory {
		return 0, operationLocation{}, false
	}
	value := resolveReplacement(operation.Operands[0], replacements)
	definition, exists := definitions[value]
	if !exists || definition.typeOf != typ {
		return 0, operationLocation{}, false
	}
	return value, operationLocation{block: access.Site.Block, index: access.Site.Index}, true
}

func planRegionLoadPhi(
	memory MemoryVersionID,
	region RegionID,
	result Value,
	use operationLocation,
	blocks map[BlockID]*Block,
	metadata normalizedMemoryMetadata,
	versions map[MemoryVersionID]MemoryVersion,
	accesses map[MemoryAccessID]MemoryAccess,
	definitions map[ValueID]definition,
	dominators map[BlockID]map[BlockID]bool,
	edgeLoads map[regionLoadKey][]availableRegionLoad,
	replacements map[ValueID]ValueID,
	nextValue *ValueID,
) (*regionLoadPhiPlan, error) {
	version, exists := versions[memory]
	if !exists || version.Kind != MemoryVersionPhi || version.Region != region || len(version.Incoming) < 2 ||
		(version.Block != use.block && !dominators[use.block][version.Block]) {
		return nil, nil
	}
	plan := &regionLoadPhiPlan{block: version.Block}
	seen := map[BlockID]bool{}
	for _, incoming := range version.Incoming {
		if incoming.Entry || seen[incoming.Predecessor] {
			return nil, nil
		}
		predecessor := blocks[incoming.Predecessor]
		if predecessor == nil || countRegionLoadEdges(predecessor.Terminator, version.Block) == 0 {
			return nil, nil
		}
		predecessorExit := operationLocation{block: incoming.Predecessor, index: len(predecessor.Operations)}
		value, _ := storedRegionValue(
			incoming.Version, region, result.Type, predecessorExit, blocks, metadata, versions,
			accesses, definitions, dominators, replacements,
		)
		if value == 0 {
			value = availableRegionValueAt(
				regionLoadKey{region: region, memory: incoming.Version, typ: result.Type},
				predecessorExit, edgeLoads, definitions, dominators, replacements,
			)
		}
		if value == 0 {
			return nil, nil
		}
		seen[incoming.Predecessor] = true
		plan.incoming = append(plan.incoming, regionLoadPhiIncoming{predecessor: incoming.Predecessor, value: value})
	}
	if *nextValue == 0 {
		return nil, fmt.Errorf("optir: region load forwarding value identity overflow")
	}
	plan.parameter = result
	plan.parameter.ID = *nextValue
	plan.parameter.Name = result.Name + ".memory-phi"
	*nextValue++
	return plan, nil
}

func availableRegionValueAt(
	key regionLoadKey,
	use operationLocation,
	available map[regionLoadKey][]availableRegionLoad,
	definitions map[ValueID]definition,
	dominators map[BlockID]map[BlockID]bool,
	replacements map[ValueID]ValueID,
) ValueID {
	candidates := available[key]
	for index := len(candidates) - 1; index >= 0; index-- {
		candidate := candidates[index]
		if !locationDominates(candidate.location.block, candidate.location.index, use.block, use.index, dominators) {
			continue
		}
		value := resolveReplacement(candidate.result, replacements)
		definition, exists := definitions[value]
		if exists && definition.typeOf == key.typ && locationDominates(definition.block, definition.index, use.block, use.index, dominators) {
			return value
		}
	}
	return 0
}

func nextRegionLoadValueID(cfg CFG) ValueID {
	maximum := ValueID(0)
	for _, block := range cfg.Blocks {
		for _, parameter := range block.Parameters {
			if parameter.ID > maximum {
				maximum = parameter.ID
			}
		}
		for _, operation := range block.Operations {
			for _, result := range operation.Results {
				if result.ID > maximum {
					maximum = result.ID
				}
			}
		}
	}
	if maximum == ^ValueID(0) {
		return 0
	}
	return maximum + 1
}

func countRegionLoadEdges(terminator Terminator, target BlockID) int {
	count := 0
	if terminator.True.Target == target && (terminator.Kind == TerminatorBranch || terminator.Kind == TerminatorCondBranch) {
		count++
	}
	if terminator.False.Target == target && terminator.Kind == TerminatorCondBranch {
		count++
	}
	return count
}

func appendRegionLoadEdgeArgument(terminator *Terminator, target BlockID, value ValueID) int {
	count := 0
	if terminator.True.Target == target && (terminator.Kind == TerminatorBranch || terminator.Kind == TerminatorCondBranch) {
		terminator.True.Arguments = append(terminator.True.Arguments, value)
		count++
	}
	if terminator.False.Target == target && terminator.Kind == TerminatorCondBranch {
		terminator.False.Arguments = append(terminator.False.Arguments, value)
		count++
	}
	return count
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
	fingerprintString(digest, "oak.optir.region-load-forwarding.v7")
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
