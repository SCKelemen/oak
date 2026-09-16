package optir

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"hash"
	"sort"

	"github.com/SCKelemen/oak/opt"
)

// AnalysisAspect names one independently comparable part of OptIR. Analyses
// declare every aspect they read; reuse across CFG versions requires a checked
// preservation result for every declared aspect.
type AnalysisAspect string

const (
	AspectCFGTopology        AnalysisAspect = "CFGTopology"
	AspectSSAIdentity        AnalysisAspect = "SSAIdentity"
	AspectOperationSemantics AnalysisAspect = "OperationSemantics"
	AspectMemoryEffects      AnalysisAspect = "MemoryEffects"
	AspectTypes              AnalysisAspect = "Types"
	AspectProofFacts         AnalysisAspect = "ProofFacts"
	AspectLayout             AnalysisAspect = "Layout"
)

var orderedAnalysisAspects = []AnalysisAspect{
	AspectCFGTopology,
	AspectSSAIdentity,
	AspectOperationSemantics,
	AspectMemoryEffects,
	AspectTypes,
	AspectProofFacts,
	AspectLayout,
}

// AnalysisRequirements is an immutable declaration of the OptIR aspects read
// by one analysis or transform.
type AnalysisRequirements struct {
	name    string
	aspects []AnalysisAspect
}

func NewAnalysisRequirements(name string, aspects ...AnalysisAspect) (AnalysisRequirements, error) {
	if name == "" {
		return AnalysisRequirements{}, fmt.Errorf("optir: analysis requirements have an empty name")
	}
	normalized, err := normalizeAnalysisAspects(aspects)
	if err != nil {
		return AnalysisRequirements{}, err
	}
	if len(normalized) == 0 {
		return AnalysisRequirements{}, fmt.Errorf("optir: analysis %s declares no requirements", name)
	}
	return AnalysisRequirements{name: name, aspects: normalized}, nil
}

func (requirements AnalysisRequirements) Name() string { return requirements.name }

func (requirements AnalysisRequirements) Aspects() []AnalysisAspect {
	return append([]AnalysisAspect(nil), requirements.aspects...)
}

func SCCPAnalysisRequirements() AnalysisRequirements {
	return knownAnalysisRequirements("SCCP", AspectCFGTopology, AspectSSAIdentity, AspectOperationSemantics, AspectTypes)
}

func LoopStructureAnalysisRequirements() AnalysisRequirements {
	return knownAnalysisRequirements("LoopStructure", AspectCFGTopology)
}

func LoopAnalysisRequirements() AnalysisRequirements {
	return knownAnalysisRequirements("Loops", AspectCFGTopology, AspectSSAIdentity, AspectOperationSemantics, AspectTypes)
}

func GVNDCERequirements() AnalysisRequirements {
	return knownAnalysisRequirements("GVN/DCE", AspectCFGTopology, AspectSSAIdentity, AspectOperationSemantics, AspectMemoryEffects, AspectTypes, AspectProofFacts)
}

func LICMRequirements() AnalysisRequirements {
	return knownAnalysisRequirements("LICM", AspectCFGTopology, AspectSSAIdentity, AspectOperationSemantics, AspectMemoryEffects, AspectTypes, AspectProofFacts)
}

func knownAnalysisRequirements(name string, aspects ...AnalysisAspect) AnalysisRequirements {
	requirements, err := NewAnalysisRequirements(name, aspects...)
	if err != nil {
		panic(err)
	}
	return requirements
}

// PreservationCheck records the independently computed before/after digest of
// one aspect. Preserved is redundant evidence for reports; certificate
// validation recomputes it from the two digests.
type PreservationCheck struct {
	Aspect            AnalysisAspect
	BeforeFingerprint string
	AfterFingerprint  string
	Preserved         bool
}

// PreservationCertificate binds checked aspect comparisons to exact artifact
// and content identities. Its control fields are private and inspection slices
// are copied, so callers cannot manufacture reuse by flipping a boolean.
type PreservationCertificate struct {
	before            opt.ArtifactKey
	after             opt.ArtifactKey
	beforeFingerprint string
	afterFingerprint  string
	checkerRevision   string
	checks            []PreservationCheck
	integrity         string
}

const cfgPreservationCheckerRevision = "oak.optir.preservation.v1"

func (certificate PreservationCertificate) Before() opt.ArtifactKey { return certificate.before }
func (certificate PreservationCertificate) After() opt.ArtifactKey  { return certificate.after }
func (certificate PreservationCertificate) BeforeFingerprint() string {
	return certificate.beforeFingerprint
}
func (certificate PreservationCertificate) AfterFingerprint() string {
	return certificate.afterFingerprint
}
func (certificate PreservationCertificate) CheckerRevision() string {
	return certificate.checkerRevision
}
func (certificate PreservationCertificate) Checks() []PreservationCheck {
	return append([]PreservationCheck(nil), certificate.checks...)
}

// CheckCFGPreservation verifies two CFGs and compares the requested aspects.
// A changed aspect is recorded rather than treated as a checker failure.
func CheckCFGPreservation(beforeKey opt.ArtifactKey, before CFG, afterKey opt.ArtifactKey, after CFG, aspects ...AnalysisAspect) (PreservationCertificate, error) {
	if err := validateCFGArtifactKey(beforeKey, "before"); err != nil {
		return PreservationCertificate{}, err
	}
	if err := validateCFGArtifactKey(afterKey, "after"); err != nil {
		return PreservationCertificate{}, err
	}
	normalized, err := normalizeAnalysisAspects(aspects)
	if err != nil {
		return PreservationCertificate{}, err
	}
	if len(normalized) == 0 {
		return PreservationCertificate{}, fmt.Errorf("optir: preservation check requests no aspects")
	}
	beforeFingerprint, err := FingerprintCFG(before)
	if err != nil {
		return PreservationCertificate{}, fmt.Errorf("optir: preservation before CFG: %w", err)
	}
	afterFingerprint, err := FingerprintCFG(after)
	if err != nil {
		return PreservationCertificate{}, fmt.Errorf("optir: preservation after CFG: %w", err)
	}
	certificate := PreservationCertificate{
		before:            beforeKey,
		after:             afterKey,
		beforeFingerprint: beforeFingerprint,
		afterFingerprint:  afterFingerprint,
		checkerRevision:   cfgPreservationCheckerRevision,
		checks:            make([]PreservationCheck, 0, len(normalized)),
	}
	for _, aspect := range normalized {
		beforeAspect := fingerprintCFGAspect(before, aspect)
		afterAspect := fingerprintCFGAspect(after, aspect)
		certificate.checks = append(certificate.checks, PreservationCheck{
			Aspect:            aspect,
			BeforeFingerprint: beforeAspect,
			AfterFingerprint:  afterAspect,
			Preserved:         beforeAspect == afterAspect,
		})
	}
	certificate.integrity = fingerprintPreservationCertificate(certificate)
	return certificate, nil
}

// Preserves reports whether this intact certificate establishes every aspect
// required by an analysis. It does not make the candidate selectable or prove
// semantic equivalence.
func (certificate PreservationCertificate) Preserves(requirements AnalysisRequirements) bool {
	return certificate.valid() == nil && requirementsSatisfied(certificate.checks, requirements)
}

func (certificate PreservationCertificate) permitsContentReuse(beforeFingerprint, afterFingerprint string, requirements AnalysisRequirements) error {
	if err := certificate.valid(); err != nil {
		return err
	}
	if certificate.beforeFingerprint != beforeFingerprint || certificate.afterFingerprint != afterFingerprint {
		return fmt.Errorf("optir: preservation certificate belongs to different CFG contents")
	}
	if !requirementsSatisfied(certificate.checks, requirements) {
		return fmt.Errorf("optir: preservation certificate does not satisfy %s requirements", requirements.Name())
	}
	return nil
}

func (certificate PreservationCertificate) valid() error {
	if err := validateCFGArtifactKey(certificate.before, "certificate before"); err != nil {
		return err
	}
	if err := validateCFGArtifactKey(certificate.after, "certificate after"); err != nil {
		return err
	}
	if certificate.beforeFingerprint == "" || certificate.afterFingerprint == "" || certificate.checkerRevision != cfgPreservationCheckerRevision {
		return fmt.Errorf("optir: preservation certificate has incomplete provenance")
	}
	if len(certificate.checks) == 0 {
		return fmt.Errorf("optir: preservation certificate has no checks")
	}
	previous := -1
	for _, check := range certificate.checks {
		rank, valid := analysisAspectRank(check.Aspect)
		if !valid || rank <= previous || check.BeforeFingerprint == "" || check.AfterFingerprint == "" || check.Preserved != (check.BeforeFingerprint == check.AfterFingerprint) {
			return fmt.Errorf("optir: preservation certificate has invalid check for %s", check.Aspect)
		}
		previous = rank
	}
	if certificate.integrity == "" || certificate.integrity != fingerprintPreservationCertificate(certificate) {
		return fmt.Errorf("optir: preservation certificate was mutated")
	}
	return nil
}

func requirementsSatisfied(checks []PreservationCheck, requirements AnalysisRequirements) bool {
	if requirements.name == "" || len(requirements.aspects) == 0 {
		return false
	}
	preserved := make(map[AnalysisAspect]bool, len(checks))
	for _, check := range checks {
		preserved[check.Aspect] = check.Preserved
	}
	for _, aspect := range requirements.aspects {
		if !preserved[aspect] {
			return false
		}
	}
	return true
}

func validateCFGArtifactKey(key opt.ArtifactKey, role string) error {
	if key.Kind != opt.ArtifactIR || key.Name == "" || key.Version == "" {
		return fmt.Errorf("optir: %s artifact key %s is not an exact IR identity", role, key)
	}
	return nil
}

func normalizeAnalysisAspects(aspects []AnalysisAspect) ([]AnalysisAspect, error) {
	seen := make(map[AnalysisAspect]bool, len(aspects))
	result := append([]AnalysisAspect(nil), aspects...)
	for _, aspect := range result {
		if _, valid := analysisAspectRank(aspect); !valid {
			return nil, fmt.Errorf("optir: unknown analysis aspect %q", aspect)
		}
		if seen[aspect] {
			return nil, fmt.Errorf("optir: analysis aspect %s is repeated", aspect)
		}
		seen[aspect] = true
	}
	sort.Slice(result, func(i, j int) bool {
		left, _ := analysisAspectRank(result[i])
		right, _ := analysisAspectRank(result[j])
		return left < right
	})
	return result, nil
}

func analysisAspectRank(aspect AnalysisAspect) (int, bool) {
	for rank, candidate := range orderedAnalysisAspects {
		if aspect == candidate {
			return rank, true
		}
	}
	return 0, false
}

func fingerprintCFGAspect(cfg CFG, aspect AnalysisAspect) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.aspect.v1")
	fingerprintString(digest, string(aspect))
	switch aspect {
	case AspectCFGTopology:
		fingerprintCFGTopology(digest, cfg)
	case AspectSSAIdentity:
		fingerprintCFGSSA(digest, cfg)
	case AspectOperationSemantics:
		fingerprintCFGOperations(digest, cfg)
	case AspectMemoryEffects:
		fingerprintCFGEffects(digest, cfg)
	case AspectTypes:
		fingerprintCFGTypes(digest, cfg)
	case AspectProofFacts:
		fingerprintCFGProofFacts(digest, cfg)
	case AspectLayout:
		fingerprintString(digest, "optir-has-no-physical-layout")
	}
	return hex.EncodeToString(digest.Sum(nil))
}

func fingerprintCFGTopology(digest hash.Hash, cfg CFG) {
	fingerprintUint64(digest, uint64(cfg.Entry))
	fingerprintUint64(digest, uint64(len(cfg.Blocks)))
	for _, block := range cfg.Blocks {
		fingerprintUint64(digest, uint64(block.ID))
		fingerprintString(digest, string(block.Terminator.Kind))
		switch block.Terminator.Kind {
		case TerminatorBranch:
			fingerprintUint64(digest, uint64(block.Terminator.True.Target))
		case TerminatorCondBranch:
			fingerprintUint64(digest, uint64(block.Terminator.True.Target))
			fingerprintUint64(digest, uint64(block.Terminator.False.Target))
		}
	}
}

func fingerprintCFGSSA(digest hash.Hash, cfg CFG) {
	fingerprintUint64(digest, uint64(len(cfg.Blocks)))
	for _, block := range cfg.Blocks {
		fingerprintUint64(digest, uint64(block.ID))
		fingerprintUint64(digest, uint64(len(block.Parameters)))
		for _, parameter := range block.Parameters {
			fingerprintUint64(digest, uint64(parameter.ID))
		}
		fingerprintUint64(digest, uint64(len(block.Operations)))
		for _, operation := range block.Operations {
			fingerprintUint64(digest, uint64(len(operation.Results)))
			for _, result := range operation.Results {
				fingerprintUint64(digest, uint64(result.ID))
			}
			fingerprintValueIDs(digest, operation.Operands)
		}
		fingerprintTerminatorSSA(digest, block.Terminator)
	}
}

func fingerprintTerminatorSSA(digest hash.Hash, terminator Terminator) {
	switch terminator.Kind {
	case TerminatorReturn:
		fingerprintValueIDs(digest, terminator.Values)
	case TerminatorBranch:
		fingerprintValueIDs(digest, terminator.True.Arguments)
	case TerminatorCondBranch:
		fingerprintUint64(digest, uint64(terminator.Condition))
		fingerprintValueIDs(digest, terminator.True.Arguments)
		fingerprintValueIDs(digest, terminator.False.Arguments)
	}
}

func fingerprintCFGOperations(digest hash.Hash, cfg CFG) {
	fingerprintUint64(digest, uint64(len(cfg.Blocks)))
	for _, block := range cfg.Blocks {
		fingerprintUint64(digest, uint64(block.ID))
		fingerprintUint64(digest, uint64(len(block.Operations)))
		for _, operation := range block.Operations {
			fingerprintString(digest, operation.Code)
			fingerprintString(digest, operation.MemoryAccessID)
			fingerprintString(digest, operation.MemoryCallID)
			fingerprintUint64(digest, uint64(len(operation.Results)))
			fingerprintUint64(digest, uint64(len(operation.Operands)))
			fingerprintUint64(digest, uint64(len(operation.Attributes)))
			for _, attribute := range operation.Attributes {
				fingerprintString(digest, attribute.Name)
				fingerprintString(digest, attribute.Value)
			}
		}
	}
}

func fingerprintCFGEffects(digest hash.Hash, cfg CFG) {
	fingerprintUint64(digest, uint64(len(cfg.Blocks)))
	for _, block := range cfg.Blocks {
		fingerprintUint64(digest, uint64(block.ID))
		observable := 0
		for _, operation := range block.Operations {
			if !isClosedPureOperation(operation) {
				observable++
			}
		}
		fingerprintUint64(digest, uint64(observable))
		for _, operation := range block.Operations {
			// Unknown, trapping, call, and explicit-effect operations are all
			// part of the conservative effect trace. Missing metadata never
			// turns an unknown operation into a reusable-pure one.
			if isClosedPureOperation(operation) {
				continue
			}
			fingerprintString(digest, operation.Code)
			fingerprintString(digest, operation.MemoryAccessID)
			fingerprintString(digest, operation.MemoryCallID)
			// Operand identities are conservative region/effect inputs. A
			// future RegionMemorySSA projection can replace this with proved
			// region identities; until then, an address/value remap invalidates
			// effect-dependent analyses.
			fingerprintValueIDs(digest, operation.Operands)
			fingerprintUint64(digest, uint64(len(operation.Effects)))
			for _, effect := range operation.Effects {
				fingerprintString(digest, string(effect))
			}
			fingerprintUint64(digest, uint64(len(operation.Attributes)))
			for _, attribute := range operation.Attributes {
				fingerprintString(digest, attribute.Name)
				fingerprintString(digest, attribute.Value)
			}
		}
	}
}

func fingerprintCFGTypes(digest hash.Hash, cfg CFG) {
	fingerprintUint64(digest, uint64(len(cfg.Results)))
	for _, result := range cfg.Results {
		fingerprintString(digest, string(result))
	}
	fingerprintUint64(digest, uint64(len(cfg.Blocks)))
	for _, block := range cfg.Blocks {
		fingerprintUint64(digest, uint64(block.ID))
		fingerprintUint64(digest, uint64(len(block.Parameters)))
		for _, parameter := range block.Parameters {
			fingerprintUint64(digest, uint64(parameter.ID))
			fingerprintString(digest, string(parameter.Type))
		}
		fingerprintUint64(digest, uint64(len(block.Operations)))
		for _, operation := range block.Operations {
			fingerprintUint64(digest, uint64(len(operation.Results)))
			for _, result := range operation.Results {
				fingerprintUint64(digest, uint64(result.ID))
				fingerprintString(digest, string(result.Type))
			}
		}
	}
}

func fingerprintCFGProofFacts(digest hash.Hash, cfg CFG) {
	fingerprintFacts(digest, cfg.Facts)
	fingerprintUint64(digest, uint64(len(cfg.Blocks)))
	for _, block := range cfg.Blocks {
		fingerprintUint64(digest, uint64(block.ID))
		fingerprintUint64(digest, uint64(len(block.Operations)))
		for _, operation := range block.Operations {
			fingerprintFacts(digest, operation.Facts)
		}
	}
}

func fingerprintPreservationCertificate(certificate PreservationCertificate) string {
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.preservation-certificate.v1")
	fingerprintArtifactKey(digest, certificate.before)
	fingerprintArtifactKey(digest, certificate.after)
	fingerprintString(digest, certificate.beforeFingerprint)
	fingerprintString(digest, certificate.afterFingerprint)
	fingerprintString(digest, certificate.checkerRevision)
	fingerprintUint64(digest, uint64(len(certificate.checks)))
	for _, check := range certificate.checks {
		fingerprintString(digest, string(check.Aspect))
		fingerprintString(digest, check.BeforeFingerprint)
		fingerprintString(digest, check.AfterFingerprint)
		fingerprintBool(digest, check.Preserved)
	}
	return hex.EncodeToString(digest.Sum(nil))
}

func fingerprintArtifactKey(digest hash.Hash, key opt.ArtifactKey) {
	fingerprintString(digest, string(key.Kind))
	fingerprintString(digest, key.Name)
	fingerprintString(digest, key.Version)
}
