package optir

import (
	"crypto/sha256"
	"fmt"
	"hash"
	"reflect"
)

// DeadStoreRefusalReason records why an advisory liveness candidate stayed in
// the CFG. Refusal is the default for anything outside the first closed,
// whole-region store vocabulary.
type DeadStoreRefusalReason string

const (
	DeadStoreNotWholeRegion   DeadStoreRefusalReason = "not-whole-region"
	DeadStoreVolatile         DeadStoreRefusalReason = "volatile"
	DeadStoreMultipleAccesses DeadStoreRefusalReason = "multiple-accesses"
	DeadStoreUnknownOperation DeadStoreRefusalReason = "unknown-operation"
	DeadStoreProducesValue    DeadStoreRefusalReason = "produces-value"
	DeadStoreHasAttributes    DeadStoreRefusalReason = "has-attributes"
	DeadStoreObservableEffect DeadStoreRefusalReason = "observable-effect"
)

// DeadStoreCandidate identifies one exact MemorySSA definition and source CFG
// site removed from a candidate CFG.
type DeadStoreCandidate struct {
	Access  MemoryAccessID
	Version MemoryVersionID
	Region  RegionID
	Site    OperationSite
}

// DeadStoreRefusal identifies an advisory liveness candidate that could not be
// removed under the closed transform vocabulary.
type DeadStoreRefusal struct {
	Candidate DeadStoreCandidate
	Reason    DeadStoreRefusalReason
}

// DeadStoreEliminationReport is deterministic transform evidence, not a
// semantic-equivalence verdict or emission license. Private identities bind it
// to the exact input and output CFG/metadata revisions and prerequisite
// analyses.
type DeadStoreEliminationReport struct {
	Removed      []DeadStoreCandidate
	Refused      []DeadStoreRefusal
	DroppedFacts int

	inputFingerprint          string
	metadataFingerprint       string
	memorySSAFingerprint      string
	livenessFingerprint       string
	observabilityFingerprint  string
	outputFingerprint         string
	outputMetadataFingerprint string
	integrity                 string
}

// EliminateDeadRegionStores removes only closed OpStoreRegion operations whose
// checked metadata says they are nonvolatile whole-region writes and whose
// exact MemorySSA definition is unused under the supplied observability
// boundary. The rewritten metadata is returned with renumbered operation sites.
// A caller must still submit the candidate to semantic verification before it
// may be emitted.
func EliminateDeadRegionStores(
	cfg CFG,
	metadata RegionMemoryMetadata,
	memorySSA RegionMemorySSA,
	observability RegionMemoryObservability,
	liveness MemoryDefinitionLiveness,
) (CFG, RegionMemoryMetadata, DeadStoreEliminationReport, error) {
	if err := VerifyMemoryDefinitionLiveness(cfg, metadata, memorySSA, observability, liveness); err != nil {
		return CFG{}, RegionMemoryMetadata{}, DeadStoreEliminationReport{}, err
	}
	normalizedMetadata, err := normalizeMemoryMetadata(cfg, metadata)
	if err != nil {
		return CFG{}, RegionMemoryMetadata{}, DeadStoreEliminationReport{}, err
	}
	normalizedObservability, err := normalizeRegionMemoryObservability(memorySSA.Regions, observability)
	if err != nil {
		return CFG{}, RegionMemoryMetadata{}, DeadStoreEliminationReport{}, err
	}
	result, resultMetadata, report, err := eliminateDeadRegionStores(cfg, normalizedMetadata, memorySSA, liveness)
	if err != nil {
		return CFG{}, RegionMemoryMetadata{}, DeadStoreEliminationReport{}, err
	}
	outputMetadata, err := normalizeMemoryMetadata(result, resultMetadata)
	if err != nil {
		return CFG{}, RegionMemoryMetadata{}, DeadStoreEliminationReport{}, fmt.Errorf("optir: DSE produced invalid memory metadata: %w", err)
	}
	report.inputFingerprint = fingerprintCFG(cfg)
	report.metadataFingerprint = fingerprintNormalizedMemoryMetadata(normalizedMetadata)
	report.memorySSAFingerprint = memorySSA.integrity
	report.livenessFingerprint = liveness.integrity
	report.observabilityFingerprint = fingerprintRegionMemoryObservability(normalizedObservability)
	report.outputFingerprint = fingerprintCFG(result)
	report.outputMetadataFingerprint = fingerprintNormalizedMemoryMetadata(outputMetadata)
	report.integrity = fingerprintDeadStoreEliminationReport(report)
	return result, resultMetadata, report, nil
}

// VerifyDeadStoreElimination independently checks the prerequisite evidence,
// report identities, resulting CFG and rewritten metadata, then reruns the
// complete transform. It verifies deterministic construction, not source-level
// semantic equivalence.
func VerifyDeadStoreElimination(
	cfg CFG,
	metadata RegionMemoryMetadata,
	memorySSA RegionMemorySSA,
	observability RegionMemoryObservability,
	liveness MemoryDefinitionLiveness,
	result CFG,
	resultMetadata RegionMemoryMetadata,
	report DeadStoreEliminationReport,
) error {
	if err := VerifyMemoryDefinitionLiveness(cfg, metadata, memorySSA, observability, liveness); err != nil {
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
	if err := validateAnalysisCFG(result); err != nil {
		return fmt.Errorf("optir: DSE result is invalid: %w", err)
	}
	normalizedOutputMetadata, err := normalizeMemoryMetadata(result, resultMetadata)
	if err != nil {
		return fmt.Errorf("optir: DSE result metadata is invalid: %w", err)
	}
	if _, err := AnalyzeRegionMemorySSA(result, resultMetadata); err != nil {
		return fmt.Errorf("optir: DSE result memory SSA is invalid: %w", err)
	}
	if report.inputFingerprint == "" || report.inputFingerprint != fingerprintCFG(cfg) {
		return fmt.Errorf("optir: DSE report belongs to a different input CFG")
	}
	if report.metadataFingerprint == "" || report.metadataFingerprint != fingerprintNormalizedMemoryMetadata(normalizedMetadata) {
		return fmt.Errorf("optir: DSE report belongs to different input metadata")
	}
	if report.memorySSAFingerprint == "" || report.memorySSAFingerprint != memorySSA.integrity {
		return fmt.Errorf("optir: DSE report belongs to different memory SSA")
	}
	if report.livenessFingerprint == "" || report.livenessFingerprint != liveness.integrity {
		return fmt.Errorf("optir: DSE report belongs to different liveness evidence")
	}
	if report.observabilityFingerprint == "" || report.observabilityFingerprint != fingerprintRegionMemoryObservability(normalizedObservability) {
		return fmt.Errorf("optir: DSE report belongs to different observability")
	}
	if report.outputFingerprint == "" || report.outputFingerprint != fingerprintCFG(result) {
		return fmt.Errorf("optir: DSE report belongs to a different output CFG")
	}
	if report.outputMetadataFingerprint == "" || report.outputMetadataFingerprint != fingerprintNormalizedMemoryMetadata(normalizedOutputMetadata) {
		return fmt.Errorf("optir: DSE report belongs to different output metadata")
	}
	if report.integrity == "" || report.integrity != fingerprintDeadStoreEliminationReport(report) {
		return fmt.Errorf("optir: DSE report was mutated")
	}
	expectedCFG, expectedMetadata, expectedReport, err := eliminateDeadRegionStores(cfg, normalizedMetadata, memorySSA, liveness)
	if err != nil {
		return err
	}
	if !reflect.DeepEqual(result, expectedCFG) || !reflect.DeepEqual(resultMetadata, expectedMetadata) ||
		!reflect.DeepEqual(report.Removed, expectedReport.Removed) ||
		!reflect.DeepEqual(report.Refused, expectedReport.Refused) ||
		report.DroppedFacts != expectedReport.DroppedFacts {
		return fmt.Errorf("optir: DSE result does not match its inputs")
	}
	return nil
}

func eliminateDeadRegionStores(
	cfg CFG,
	metadata normalizedMemoryMetadata,
	memorySSA RegionMemorySSA,
	liveness MemoryDefinitionLiveness,
) (CFG, RegionMemoryMetadata, DeadStoreEliminationReport, error) {
	blocks := make(map[BlockID]*Block, len(cfg.Blocks))
	for index := range cfg.Blocks {
		blocks[cfg.Blocks[index].ID] = &cfg.Blocks[index]
	}
	accesses := make(map[MemoryAccessID]MemoryAccess, len(memorySSA.Accesses))
	for _, access := range memorySSA.Accesses {
		accesses[access.ID] = access
	}
	deadVersions := make(map[MemoryVersionID]bool, len(liveness.DeadVersionCandidates))
	for _, version := range liveness.DeadVersionCandidates {
		deadVersions[version] = true
	}

	removedSites := map[OperationSite]bool{}
	report := DeadStoreEliminationReport{}
	for _, accessID := range liveness.DeadAccessCandidates {
		access, ok := accesses[accessID]
		if !ok || access.Kind != MemoryWrite || access.Output == 0 || !deadVersions[access.Output] {
			return CFG{}, RegionMemoryMetadata{}, DeadStoreEliminationReport{}, fmt.Errorf("optir: DSE liveness candidate access %d is inconsistent", accessID)
		}
		candidate := DeadStoreCandidate{Access: access.ID, Version: access.Output, Region: access.Region, Site: access.Site}
		operationAccesses := metadata.bySite[access.Site]
		if len(operationAccesses) != 1 {
			report.Refused = append(report.Refused, DeadStoreRefusal{Candidate: candidate, Reason: DeadStoreMultipleAccesses})
			continue
		}
		if !access.WholeRegion {
			report.Refused = append(report.Refused, DeadStoreRefusal{Candidate: candidate, Reason: DeadStoreNotWholeRegion})
			continue
		}
		if access.Volatile {
			report.Refused = append(report.Refused, DeadStoreRefusal{Candidate: candidate, Reason: DeadStoreVolatile})
			continue
		}
		block := blocks[access.Site.Block]
		if block == nil || access.Site.Index < 0 || access.Site.Index >= len(block.Operations) {
			return CFG{}, RegionMemoryMetadata{}, DeadStoreEliminationReport{}, fmt.Errorf("optir: DSE candidate access %d names missing operation %d:%d", access.ID, access.Site.Block, access.Site.Index)
		}
		operation := block.Operations[access.Site.Index]
		switch {
		case operation.Code != OpStoreRegion:
			report.Refused = append(report.Refused, DeadStoreRefusal{Candidate: candidate, Reason: DeadStoreUnknownOperation})
		case len(operation.Results) != 0:
			report.Refused = append(report.Refused, DeadStoreRefusal{Candidate: candidate, Reason: DeadStoreProducesValue})
		case len(operation.Attributes) != 0:
			report.Refused = append(report.Refused, DeadStoreRefusal{Candidate: candidate, Reason: DeadStoreHasAttributes})
		case len(operation.Effects) != 1 || operation.Effects[0] != EffectWriteMemory:
			report.Refused = append(report.Refused, DeadStoreRefusal{Candidate: candidate, Reason: DeadStoreObservableEffect})
		default:
			removedSites[access.Site] = true
			report.Removed = append(report.Removed, candidate)
			report.DroppedFacts += len(operation.Facts)
		}
	}

	result := cloneCFG(cfg)
	siteRemap := make(map[OperationSite]OperationSite, len(metadata.operations))
	for blockIndex := range result.Blocks {
		block := &result.Blocks[blockIndex]
		operations := make([]Operation, 0, len(block.Operations))
		for operationIndex, operation := range block.Operations {
			oldSite := OperationSite{Block: block.ID, Index: operationIndex}
			if removedSites[oldSite] {
				continue
			}
			siteRemap[oldSite] = OperationSite{Block: block.ID, Index: len(operations)}
			operations = append(operations, operation)
		}
		block.Operations = operations
	}
	resultMetadata := RegionMemoryMetadata{Regions: append([]RegionID(nil), metadata.regions...)}
	for _, operation := range metadata.operations {
		if removedSites[operation.Site] {
			continue
		}
		newSite, ok := siteRemap[operation.Site]
		if !ok {
			return CFG{}, RegionMemoryMetadata{}, DeadStoreEliminationReport{}, fmt.Errorf("optir: DSE could not remap memory operation %d:%d", operation.Site.Block, operation.Site.Index)
		}
		resultMetadata.Operations = append(resultMetadata.Operations, MemoryOperationMetadata{
			Site:       newSite,
			Accesses:   append([]MemoryAccessSpec(nil), operation.Accesses...),
			CallEffect: operation.CallEffect,
		})
	}
	if err := validateAnalysisCFG(result); err != nil {
		return CFG{}, RegionMemoryMetadata{}, DeadStoreEliminationReport{}, fmt.Errorf("optir: DSE produced invalid CFG: %w", err)
	}
	if _, err := AnalyzeRegionMemorySSA(result, resultMetadata); err != nil {
		return CFG{}, RegionMemoryMetadata{}, DeadStoreEliminationReport{}, fmt.Errorf("optir: DSE produced invalid memory graph: %w", err)
	}
	return result, resultMetadata, report, nil
}

func fingerprintDeadStoreEliminationReport(report DeadStoreEliminationReport) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.dead-store-elimination.v2")
	fingerprintString(digest, report.inputFingerprint)
	fingerprintString(digest, report.metadataFingerprint)
	fingerprintString(digest, report.memorySSAFingerprint)
	fingerprintString(digest, report.livenessFingerprint)
	fingerprintString(digest, report.observabilityFingerprint)
	fingerprintString(digest, report.outputFingerprint)
	fingerprintString(digest, report.outputMetadataFingerprint)
	fingerprintUint64(digest, uint64(len(report.Removed)))
	for _, removed := range report.Removed {
		fingerprintDeadStoreCandidate(digest, removed)
	}
	fingerprintUint64(digest, uint64(len(report.Refused)))
	for _, refused := range report.Refused {
		fingerprintDeadStoreCandidate(digest, refused.Candidate)
		fingerprintString(digest, string(refused.Reason))
	}
	fingerprintUint64(digest, uint64(report.DroppedFacts))
	return fmt.Sprintf("%x", digest.Sum(nil))
}

func fingerprintDeadStoreCandidate(digest hash.Hash, candidate DeadStoreCandidate) {
	fingerprintUint64(digest, uint64(candidate.Access))
	fingerprintUint64(digest, uint64(candidate.Version))
	fingerprintString(digest, string(candidate.Region))
	fingerprintUint64(digest, uint64(candidate.Site.Block))
	fingerprintUint64(digest, uint64(candidate.Site.Index))
}
