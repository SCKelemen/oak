package optir

import (
	"crypto/sha256"
	"fmt"
	"sort"
)

const checkedTypeFactName = "checked.type"

// CheckedFactRecord is one independently supplied semantic authority record.
// ValueType is the canonical OptIR type established for the fact's value; the
// authority intentionally does not pin a ValueID because verified SSA
// congruence transforms may replace an identity with an equal dominating one.
type CheckedFactRecord struct {
	ID           string
	Name         string
	ValueType    Type
	Provenance   string
	Witness      string
	Scope        string
	Dependencies []string
}

// CheckedFactAuthority is an immutable exact set of checked fact records.
// Its fields remain private so a caller cannot turn transformed IR metadata
// into authority by mutating a map or a fingerprint string.
type CheckedFactAuthority struct {
	records     map[string]CheckedFactRecord
	fingerprint string
}

// NewCheckedFactAuthority validates and defensively copies the first closed
// authority vocabulary. Additional checked fact kinds must add their own
// structural validation before entering this constructor.
func NewCheckedFactAuthority(records []CheckedFactRecord) (CheckedFactAuthority, error) {
	authority := CheckedFactAuthority{records: make(map[string]CheckedFactRecord, len(records))}
	for _, record := range records {
		if record.ID == "" || record.Name != checkedTypeFactName || record.ValueType == "" ||
			record.Provenance != "checked" || record.Witness == "" || record.Scope == "" {
			return CheckedFactAuthority{}, fmt.Errorf("optir: malformed checked fact authority record %q", record.ID)
		}
		for _, dependency := range record.Dependencies {
			if dependency == "" {
				return CheckedFactAuthority{}, fmt.Errorf("optir: checked fact authority %s has an empty dependency", record.ID)
			}
		}
		if _, exists := authority.records[record.ID]; exists {
			return CheckedFactAuthority{}, fmt.Errorf("optir: checked fact authority repeats ID %s", record.ID)
		}
		record.Dependencies = append([]string(nil), record.Dependencies...)
		authority.records[record.ID] = record
	}
	authority.fingerprint = fingerprintCheckedFactAuthority(authority.records)
	return authority, nil
}

// Fingerprint identifies every authority field in canonical ID order.
func (authority CheckedFactAuthority) Fingerprint() string { return authority.fingerprint }

// Records returns a canonical defensive copy for inspection and transport.
func (authority CheckedFactAuthority) Records() []CheckedFactRecord {
	ids := make([]string, 0, len(authority.records))
	for id := range authority.records {
		ids = append(ids, id)
	}
	sort.Strings(ids)
	records := make([]CheckedFactRecord, 0, len(ids))
	for _, id := range ids {
		record := authority.records[id]
		record.Dependencies = append([]string(nil), record.Dependencies...)
		records = append(records, record)
	}
	return records
}

// VerifyFunctionCheckedFacts validates every checked fact in structured OptIR
// against separate semantic authority before CFG projection.
func VerifyFunctionCheckedFacts(function Function, authority CheckedFactAuthority) error {
	if _, err := validateStructured(function); err != nil {
		return err
	}
	types := make(map[ValueID]Type)
	for _, parameter := range function.Parameters {
		types[parameter.ID] = parameter.Type
	}
	seen := map[string]ValueID{}
	if err := verifyCheckedFactList(function.Facts, nil, types, authority, seen); err != nil {
		return fmt.Errorf("optir: function facts: %w", err)
	}
	if err := visitStructuredCheckedFacts(function.Body, types, authority, seen); err != nil {
		return err
	}
	return verifyCheckedFactAuthorityIntegrity(authority)
}

// VerifyCFGCheckedFacts rechecks checked fact authority after CFG projection
// or an SSA transform. Extra authority records are permitted because an exact
// SCCP/DCE result may remove the only operation that carried one.
func VerifyCFGCheckedFacts(cfg CFG, authority CheckedFactAuthority) error {
	if err := Verify(cfg); err != nil {
		return err
	}
	types := make(map[ValueID]Type)
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
	seen := map[string]ValueID{}
	if err := verifyCheckedFactList(cfg.Facts, nil, types, authority, seen); err != nil {
		return fmt.Errorf("optir: CFG function facts: %w", err)
	}
	for _, block := range cfg.Blocks {
		for index, operation := range block.Operations {
			owners := make(map[ValueID]bool, len(operation.Results))
			for _, result := range operation.Results {
				owners[result.ID] = true
			}
			if err := verifyCheckedFactList(operation.Facts, owners, types, authority, seen); err != nil {
				return fmt.Errorf("optir: block %d operation %d checked facts: %w", block.ID, index, err)
			}
		}
	}
	return verifyCheckedFactAuthorityIntegrity(authority)
}

func visitStructuredCheckedFacts(region Region, types map[ValueID]Type, authority CheckedFactAuthority, seen map[string]ValueID) error {
	for _, argument := range region.Arguments {
		types[argument.ID] = argument.Type
	}
	for _, node := range region.Nodes {
		switch {
		case node.Operation != nil:
			owners := make(map[ValueID]bool, len(node.Operation.Results))
			for _, result := range node.Operation.Results {
				types[result.ID] = result.Type
				owners[result.ID] = true
			}
			if err := verifyCheckedFactList(node.Operation.Facts, owners, types, authority, seen); err != nil {
				return fmt.Errorf("optir: operation %s checked facts: %w", node.Operation.Code, err)
			}
		case node.If != nil:
			for _, result := range node.If.Results {
				types[result.ID] = result.Type
			}
			if err := visitStructuredCheckedFacts(node.If.Then, types, authority, seen); err != nil {
				return err
			}
			if err := visitStructuredCheckedFacts(node.If.Else, types, authority, seen); err != nil {
				return err
			}
		case node.While != nil:
			for _, result := range node.While.Results {
				types[result.ID] = result.Type
			}
			if err := visitStructuredCheckedFacts(node.While.Condition, types, authority, seen); err != nil {
				return err
			}
			if err := visitStructuredCheckedFacts(node.While.Body, types, authority, seen); err != nil {
				return err
			}
		}
	}
	return nil
}

func verifyCheckedFactList(facts []Fact, owners map[ValueID]bool, types map[ValueID]Type, authority CheckedFactAuthority, seen map[string]ValueID) error {
	for _, fact := range facts {
		if fact.ID == "" && fact.Provenance != "checked" {
			continue
		}
		if fact.ID == "" {
			return fmt.Errorf("checked fact %s has no authority ID", fact.Name)
		}
		if fact.Name != checkedTypeFactName || fact.Provenance != "checked" {
			return fmt.Errorf("authority-bound fact %s uses unsupported provenance %q", fact.Name, fact.Provenance)
		}
		record, exists := authority.records[fact.ID]
		if !exists {
			return fmt.Errorf("checked fact %s has stale or unknown authority ID %s", fact.Name, fact.ID)
		}
		if fact.Name != record.Name || fact.Provenance != record.Provenance || fact.Witness != record.Witness || fact.Scope != record.Scope ||
			!equalCheckedFactDependencies(fact.Dependencies, record.Dependencies) {
			return fmt.Errorf("checked fact %s does not match authority %s", fact.Name, fact.ID)
		}
		if len(fact.Values) != 1 {
			return fmt.Errorf("checked type fact %s has %d values, want 1", fact.ID, len(fact.Values))
		}
		value := fact.Values[0]
		if owners == nil || !owners[value] {
			return fmt.Errorf("checked type fact %s is not attached to its defining operation value %d", fact.ID, value)
		}
		if types[value] != record.ValueType {
			return fmt.Errorf("checked type fact %s value %d has type %s, authority requires %s", fact.ID, value, types[value], record.ValueType)
		}
		if prior, duplicate := seen[fact.ID]; duplicate {
			return fmt.Errorf("checked fact authority ID %s is attached more than once (%d and %d)", fact.ID, prior, value)
		}
		seen[fact.ID] = value
	}
	return nil
}

func verifyCheckedFactAuthorityIntegrity(authority CheckedFactAuthority) error {
	if authority.records == nil || authority.fingerprint == "" || authority.fingerprint != fingerprintCheckedFactAuthority(authority.records) {
		return fmt.Errorf("optir: checked fact authority is missing or corrupted")
	}
	return nil
}

func equalCheckedFactDependencies(left, right []string) bool {
	if len(left) != len(right) {
		return false
	}
	for index := range left {
		if left[index] != right[index] {
			return false
		}
	}
	return true
}

func fingerprintCheckedFactAuthority(records map[string]CheckedFactRecord) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.checked-fact-authority.v1")
	ids := make([]string, 0, len(records))
	for id := range records {
		ids = append(ids, id)
	}
	sort.Strings(ids)
	fingerprintUint64(digest, uint64(len(ids)))
	for _, id := range ids {
		record := records[id]
		fingerprintString(digest, record.ID)
		fingerprintString(digest, record.Name)
		fingerprintString(digest, string(record.ValueType))
		fingerprintString(digest, record.Provenance)
		fingerprintString(digest, record.Witness)
		fingerprintString(digest, record.Scope)
		fingerprintUint64(digest, uint64(len(record.Dependencies)))
		for _, dependency := range record.Dependencies {
			fingerprintString(digest, dependency)
		}
	}
	return fmt.Sprintf("%x", digest.Sum(nil))
}
