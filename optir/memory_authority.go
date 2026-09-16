package optir

import (
	"crypto/sha256"
	"fmt"
	"reflect"
	"sort"
)

// CheckedMemoryAccessRecord is semantic authority for one exact memory
// operation. ID is derived from every field; an Operation carries only that
// opaque ID and cannot authorize its own region, kind, or exactness.
type CheckedMemoryAccessRecord struct {
	ID          string
	Source      Source
	Region      RegionID
	Kind        MemoryAccessKind
	ValueType   Type
	WholeRegion bool
	Volatile    bool
}

// CheckedMemoryAuthority is an immutable set of checked access records. The
// private maps and fingerprint keep transformed IR metadata separate from the
// authority that permits memory analysis.
type CheckedMemoryAuthority struct {
	records     map[string]CheckedMemoryAccessRecord
	regionTypes map[RegionID]Type
	fingerprint string
}

// NewCheckedMemoryAccessRecord constructs the canonical authority record for
// one closed scalar region access.
func NewCheckedMemoryAccessRecord(source Source, region RegionID, kind MemoryAccessKind, valueType Type, wholeRegion, volatile bool) (CheckedMemoryAccessRecord, error) {
	record := CheckedMemoryAccessRecord{
		Source: source, Region: region, Kind: kind, ValueType: valueType,
		WholeRegion: wholeRegion, Volatile: volatile,
	}
	if err := validateCheckedMemoryAccessRecord(record, false); err != nil {
		return CheckedMemoryAccessRecord{}, err
	}
	record.ID = fingerprintCheckedMemoryAccess(record)
	return record, nil
}

// NewCheckedMemoryAuthority validates and defensively copies a closed set of
// access records. Every access to one region must agree on its checked type.
func NewCheckedMemoryAuthority(records []CheckedMemoryAccessRecord) (CheckedMemoryAuthority, error) {
	authority := CheckedMemoryAuthority{
		records:     make(map[string]CheckedMemoryAccessRecord, len(records)),
		regionTypes: map[RegionID]Type{},
	}
	for _, record := range records {
		if err := validateCheckedMemoryAccessRecord(record, true); err != nil {
			return CheckedMemoryAuthority{}, err
		}
		if _, exists := authority.records[record.ID]; exists {
			return CheckedMemoryAuthority{}, fmt.Errorf("optir: checked memory authority repeats access ID %s", record.ID)
		}
		if typ, exists := authority.regionTypes[record.Region]; exists && typ != record.ValueType {
			return CheckedMemoryAuthority{}, fmt.Errorf("optir: checked memory region %q has both %s and %s", record.Region, typ, record.ValueType)
		}
		authority.records[record.ID] = record
		authority.regionTypes[record.Region] = record.ValueType
	}
	authority.fingerprint = fingerprintCheckedMemoryAuthority(authority.records)
	return authority, nil
}

// Fingerprint identifies the complete authority set in canonical access-ID
// order.
func (authority CheckedMemoryAuthority) Fingerprint() string { return authority.fingerprint }

// Records returns a canonical defensive copy for inspection and transport.
func (authority CheckedMemoryAuthority) Records() []CheckedMemoryAccessRecord {
	ids := make([]string, 0, len(authority.records))
	for id := range authority.records {
		ids = append(ids, id)
	}
	sort.Strings(ids)
	records := make([]CheckedMemoryAccessRecord, 0, len(ids))
	for _, id := range ids {
		records = append(records, authority.records[id])
	}
	return records
}

// ProjectWithCheckedMemory binds checked memory authority to exact structured
// operation identities while constructing the CFG, then independently resolves
// the opaque access IDs on the resulting CFG. Both projections must produce
// identical operation sites and Mod/Ref metadata.
func ProjectWithCheckedMemory(function Function, authority CheckedMemoryAuthority) (CFG, CheckedMemoryProjection, error) {
	if err := verifyCheckedMemoryAuthorityIntegrity(authority); err != nil {
		return CFG{}, CheckedMemoryProjection{}, err
	}
	metadata, err := checkedStructuredMemoryMetadata(function.Body, authority)
	if err != nil {
		return CFG{}, CheckedMemoryProjection{}, err
	}
	cfg, projectedMetadata, err := ProjectWithRegionMemory(function, metadata)
	if err != nil {
		return CFG{}, CheckedMemoryProjection{}, err
	}
	projection, err := ProjectCheckedMemory(cfg, authority)
	if err != nil {
		return CFG{}, CheckedMemoryProjection{}, err
	}
	if !reflect.DeepEqual(projectedMetadata, projection.Metadata) {
		return CFG{}, CheckedMemoryProjection{}, fmt.Errorf("optir: structured and authority-bound memory projections disagree")
	}
	return cfg, projection, nil
}

// CheckedMemoryProjection is exact RegionMemorySSA input derived from a CFG
// and separate semantic authority. Mutable global regions are observable on
// every normal return.
type CheckedMemoryProjection struct {
	Metadata      RegionMemoryMetadata
	Observability RegionMemoryObservability

	cfgFingerprint       string
	authorityFingerprint string
	integrity            string
}

// ProjectCheckedMemory resolves opaque operation IDs against independently
// supplied authority and constructs exact Mod/Ref metadata. It fails closed on
// every unmodeled memory effect.
func ProjectCheckedMemory(cfg CFG, authority CheckedMemoryAuthority) (CheckedMemoryProjection, error) {
	if err := Verify(cfg); err != nil {
		return CheckedMemoryProjection{}, err
	}
	if err := verifyCheckedMemoryAuthorityIntegrity(authority); err != nil {
		return CheckedMemoryProjection{}, err
	}
	projection, err := projectCheckedMemory(cfg, authority)
	if err != nil {
		return CheckedMemoryProjection{}, err
	}
	projection.cfgFingerprint = fingerprintCFG(cfg)
	projection.authorityFingerprint = authority.fingerprint
	projection.integrity = fingerprintCheckedMemoryProjection(projection)
	return projection, nil
}

// VerifyCheckedMemoryProjection checks identities and reruns the projection.
func VerifyCheckedMemoryProjection(cfg CFG, authority CheckedMemoryAuthority, projection CheckedMemoryProjection) error {
	if err := Verify(cfg); err != nil {
		return err
	}
	if err := verifyCheckedMemoryAuthorityIntegrity(authority); err != nil {
		return err
	}
	if projection.cfgFingerprint == "" || projection.cfgFingerprint != fingerprintCFG(cfg) {
		return fmt.Errorf("optir: checked memory projection belongs to a different CFG")
	}
	if projection.authorityFingerprint == "" || projection.authorityFingerprint != authority.fingerprint {
		return fmt.Errorf("optir: checked memory projection belongs to different authority")
	}
	if projection.integrity == "" || projection.integrity != fingerprintCheckedMemoryProjection(projection) {
		return fmt.Errorf("optir: checked memory projection was mutated")
	}
	expected, err := projectCheckedMemory(cfg, authority)
	if err != nil {
		return err
	}
	if !reflect.DeepEqual(projection.Metadata, expected.Metadata) || !reflect.DeepEqual(projection.Observability, expected.Observability) {
		return fmt.Errorf("optir: checked memory projection does not match its inputs")
	}
	return nil
}

func projectCheckedMemory(cfg CFG, authority CheckedMemoryAuthority) (CheckedMemoryProjection, error) {
	types := checkedMemoryValueTypes(cfg)
	seen := map[string]bool{}
	regions := map[RegionID]bool{}
	metadata := RegionMemoryMetadata{}
	for _, block := range cfg.Blocks {
		for index, operation := range block.Operations {
			hasMemoryEffect := operationHasEffect(operation, EffectReadMemory) || operationHasEffect(operation, EffectWriteMemory)
			if operation.MemoryAccessID == "" {
				if hasMemoryEffect {
					return CheckedMemoryProjection{}, fmt.Errorf("optir: memory operation %d:%d has no checked access ID", block.ID, index)
				}
				continue
			}
			if !hasMemoryEffect {
				return CheckedMemoryProjection{}, fmt.Errorf("optir: operation %d:%d carries memory access ID without a memory effect", block.ID, index)
			}
			record, exists := authority.records[operation.MemoryAccessID]
			if !exists {
				return CheckedMemoryProjection{}, fmt.Errorf("optir: memory operation %d:%d has stale or unknown access ID %s", block.ID, index, operation.MemoryAccessID)
			}
			if seen[record.ID] {
				return CheckedMemoryProjection{}, fmt.Errorf("optir: checked memory access ID %s is attached more than once", record.ID)
			}
			if operation.Source != record.Source {
				return CheckedMemoryProjection{}, fmt.Errorf("optir: checked memory access %s moved from its source scope", record.ID)
			}
			if err := validateCheckedMemoryOperation(operation, record, types); err != nil {
				return CheckedMemoryProjection{}, fmt.Errorf("optir: checked memory operation %d:%d: %w", block.ID, index, err)
			}
			seen[record.ID] = true
			regions[record.Region] = true
			metadata.Operations = append(metadata.Operations, MemoryOperationMetadata{
				Site: OperationSite{Block: block.ID, Index: index},
				Accesses: []MemoryAccessSpec{{
					Region: record.Region, Kind: record.Kind,
					WholeRegion: record.WholeRegion, Volatile: record.Volatile,
				}},
			})
		}
	}
	for region := range regions {
		metadata.Regions = append(metadata.Regions, region)
	}
	sort.Slice(metadata.Regions, func(i, j int) bool { return metadata.Regions[i] < metadata.Regions[j] })
	observability := RegionMemoryObservability{LiveOut: append([]RegionID(nil), metadata.Regions...)}
	if _, err := normalizeMemoryMetadata(cfg, metadata); err != nil {
		return CheckedMemoryProjection{}, err
	}
	return CheckedMemoryProjection{Metadata: metadata, Observability: observability}, nil
}

func checkedStructuredMemoryMetadata(region Region, authority CheckedMemoryAuthority) (StructuredRegionMemoryMetadata, error) {
	metadata := StructuredRegionMemoryMetadata{}
	regions := map[RegionID]bool{}
	seen := map[string]bool{}
	var visit func(Region) error
	visit = func(current Region) error {
		for _, node := range current.Nodes {
			switch {
			case node.Operation != nil:
				operation := node.Operation
				hasMemoryEffect := operationHasEffect(*operation, EffectReadMemory) || operationHasEffect(*operation, EffectWriteMemory)
				if operation.MemoryAccessID == "" {
					if hasMemoryEffect {
						return fmt.Errorf("optir: structured memory operation %s has no checked access ID", operation.Code)
					}
					continue
				}
				if !hasMemoryEffect {
					return fmt.Errorf("optir: structured operation %s carries a memory access ID without a memory effect", operation.Code)
				}
				record, exists := authority.records[operation.MemoryAccessID]
				if !exists {
					return fmt.Errorf("optir: structured memory operation %s has stale or unknown access ID %s", operation.Code, operation.MemoryAccessID)
				}
				if seen[record.ID] {
					return fmt.Errorf("optir: checked memory access ID %s is attached more than once", record.ID)
				}
				if operation.Source != record.Source {
					return fmt.Errorf("optir: checked memory access %s moved from its source scope", record.ID)
				}
				seen[record.ID] = true
				regions[record.Region] = true
				metadata.Operations = append(metadata.Operations, StructuredMemoryOperationMetadata{
					Operation: operation,
					Accesses: []MemoryAccessSpec{{
						Region: record.Region, Kind: record.Kind,
						WholeRegion: record.WholeRegion, Volatile: record.Volatile,
					}},
				})
			case node.If != nil:
				if err := visit(node.If.Then); err != nil {
					return err
				}
				if err := visit(node.If.Else); err != nil {
					return err
				}
			case node.While != nil:
				if err := visit(node.While.Condition); err != nil {
					return err
				}
				if err := visit(node.While.Body); err != nil {
					return err
				}
			}
		}
		return nil
	}
	if err := visit(region); err != nil {
		return StructuredRegionMemoryMetadata{}, err
	}
	for region := range regions {
		metadata.Regions = append(metadata.Regions, region)
	}
	sort.Slice(metadata.Regions, func(i, j int) bool { return metadata.Regions[i] < metadata.Regions[j] })
	return metadata, nil
}

func validateCheckedMemoryOperation(operation Operation, record CheckedMemoryAccessRecord, types map[ValueID]Type) error {
	if len(operation.Attributes) != 0 {
		return fmt.Errorf("closed region access has attributes")
	}
	switch record.Kind {
	case MemoryRead:
		if record.WholeRegion || operation.Code != OpLoadRegion || len(operation.Results) != 1 || len(operation.Operands) != 0 ||
			len(operation.Effects) != 1 || operation.Effects[0] != EffectReadMemory || operation.Results[0].Type != record.ValueType {
			return fmt.Errorf("load does not match checked authority %s", record.ID)
		}
	case MemoryWrite:
		if !record.WholeRegion || operation.Code != OpStoreRegion || len(operation.Results) != 0 || len(operation.Operands) != 1 ||
			len(operation.Effects) != 1 || operation.Effects[0] != EffectWriteMemory || types[operation.Operands[0]] != record.ValueType {
			return fmt.Errorf("store does not match checked authority %s", record.ID)
		}
	default:
		return fmt.Errorf("unsupported checked access kind %s", record.Kind)
	}
	return nil
}

func validateCheckedMemoryAccessRecord(record CheckedMemoryAccessRecord, requireID bool) error {
	if record.Region == "" || record.ValueType == "" || record.Source.Line <= 0 || record.Source.Column <= 0 {
		return fmt.Errorf("optir: malformed checked memory access record %q", record.ID)
	}
	if record.ValueType != TypeBool {
		if _, _, ok := integerType(record.ValueType); !ok {
			return fmt.Errorf("optir: checked memory access %q has unsupported type %s", record.ID, record.ValueType)
		}
	}
	if record.Volatile {
		return fmt.Errorf("optir: checked memory access %q is volatile; the closed global-cell vocabulary is nonvolatile", record.ID)
	}
	if record.Kind != MemoryRead && record.Kind != MemoryWrite {
		return fmt.Errorf("optir: checked memory access %q has unsupported kind %s", record.ID, record.Kind)
	}
	if record.Kind == MemoryRead && record.WholeRegion || record.Kind == MemoryWrite && !record.WholeRegion {
		return fmt.Errorf("optir: checked memory access %q has invalid whole-region contract", record.ID)
	}
	if requireID && (record.ID == "" || record.ID != fingerprintCheckedMemoryAccess(record)) {
		return fmt.Errorf("optir: checked memory access record has stale or forged ID %q", record.ID)
	}
	return nil
}

func verifyCheckedMemoryAuthorityIntegrity(authority CheckedMemoryAuthority) error {
	if authority.records == nil || authority.regionTypes == nil || authority.fingerprint == "" ||
		authority.fingerprint != fingerprintCheckedMemoryAuthority(authority.records) {
		return fmt.Errorf("optir: checked memory authority is missing or corrupted")
	}
	regions := map[RegionID]Type{}
	for id, record := range authority.records {
		if id != record.ID || validateCheckedMemoryAccessRecord(record, true) != nil || authority.regionTypes[record.Region] != record.ValueType {
			return fmt.Errorf("optir: checked memory authority is corrupted")
		}
		regions[record.Region] = record.ValueType
	}
	if !reflect.DeepEqual(authority.regionTypes, regions) {
		return fmt.Errorf("optir: checked memory authority is corrupted")
	}
	return nil
}

func checkedMemoryValueTypes(cfg CFG) map[ValueID]Type {
	types := map[ValueID]Type{}
	for _, block := range cfg.Blocks {
		for _, parameter := range block.Parameters {
			types[parameter.ID] = parameter.Type
		}
		for _, operation := range block.Operations {
			for _, result := range operation.Results {
				types[result.ID] = result.Type
			}
		}
	}
	return types
}

func operationHasEffect(operation Operation, want Effect) bool {
	for _, effect := range operation.Effects {
		if effect == want {
			return true
		}
	}
	return false
}

func fingerprintCheckedMemoryAccess(record CheckedMemoryAccessRecord) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.checked-memory-access.v1")
	fingerprintSource(digest, record.Source)
	fingerprintString(digest, string(record.Region))
	fingerprintString(digest, string(record.Kind))
	fingerprintString(digest, string(record.ValueType))
	fingerprintBool(digest, record.WholeRegion)
	fingerprintBool(digest, record.Volatile)
	return fmt.Sprintf("%x", digest.Sum(nil))
}

func fingerprintCheckedMemoryAuthority(records map[string]CheckedMemoryAccessRecord) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.checked-memory-authority.v1")
	ids := make([]string, 0, len(records))
	for id := range records {
		ids = append(ids, id)
	}
	sort.Strings(ids)
	fingerprintUint64(digest, uint64(len(ids)))
	for _, id := range ids {
		fingerprintString(digest, id)
		fingerprintString(digest, fingerprintCheckedMemoryAccess(records[id]))
	}
	return fmt.Sprintf("%x", digest.Sum(nil))
}

func fingerprintCheckedMemoryProjection(projection CheckedMemoryProjection) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.checked-memory-projection.v1")
	fingerprintString(digest, projection.cfgFingerprint)
	fingerprintString(digest, projection.authorityFingerprint)
	normalized := normalizedMemoryMetadata{
		regions:    append([]RegionID(nil), projection.Metadata.Regions...),
		operations: append([]MemoryOperationMetadata(nil), projection.Metadata.Operations...),
	}
	fingerprintString(digest, fingerprintNormalizedMemoryMetadata(normalized))
	fingerprintString(digest, fingerprintRegionMemoryObservability(projection.Observability))
	return fmt.Sprintf("%x", digest.Sum(nil))
}
