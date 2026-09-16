package optir

import (
	"crypto/sha256"
	"fmt"
	"reflect"
	"sort"
)

// CheckedMemoryCallSummary is an independently derived transitive may-effect
// summary for one exact checked CFG. Its state is private so callers cannot
// manufacture evidence by pairing arbitrary text with arbitrary accesses.
type CheckedMemoryCallSummary struct {
	fingerprint string
	accesses    []CheckedMemoryCallAccess
}

// Fingerprint identifies the exact CFG, active child summaries, and canonical
// transitive access set from which the summary was derived.
func (summary CheckedMemoryCallSummary) Fingerprint() string { return summary.fingerprint }

// Accesses returns a defensive copy in canonical region order.
func (summary CheckedMemoryCallSummary) Accesses() []CheckedMemoryCallAccess {
	return append([]CheckedMemoryCallAccess(nil), summary.accesses...)
}

// DeriveCheckedMemoryCallSummary derives a summary for an original checked
// projection. Every authority record must still be attached exactly once.
// Certificate roots use the same derivation internally with upper-bound
// authority because verified rewrites may have removed root operations.
func DeriveCheckedMemoryCallSummary(cfg CFG, authority CheckedMemoryAuthority) (CheckedMemoryCallSummary, error) {
	summary, _, err := deriveCheckedMemoryCallSummary(cfg, authority, true)
	return summary, err
}

// CheckedMemoryCallCertificateNode supplies one exact CFG and its separate
// checked authority to the standalone call-summary checker. The constructor
// defensively copies both fields.
type CheckedMemoryCallCertificateNode struct {
	Name      string
	CFG       CFG
	Authority CheckedMemoryAuthority
}

type checkedMemoryCallCertificateNode struct {
	cfg       CFG
	authority CheckedMemoryAuthority
}

// CheckedMemoryCallCertificate authenticates every active call summary
// reachable from one exact optimized root CFG. Its graph is deliberately
// private; consumers can inspect only the accepted graph fingerprint.
type CheckedMemoryCallCertificate struct {
	root        string
	nodes       map[string]checkedMemoryCallCertificateNode
	summaries   map[string]CheckedMemoryCallSummary
	fingerprint string
}

// Fingerprint identifies the exact accepted root and canonical certificate
// graph. Consumers must call VerifyCheckedMemoryCallCertificate before use.
func (certificate CheckedMemoryCallCertificate) Fingerprint() string {
	return certificate.fingerprint
}

// NewCheckedMemoryCallCertificate independently checks a finite, closed call
// graph. The root may carry unused upper-bound authority after a verified
// rewrite; every non-root node must be an exact original checked projection.
func NewCheckedMemoryCallCertificate(root string, input []CheckedMemoryCallCertificateNode) (CheckedMemoryCallCertificate, error) {
	if root == "" {
		return CheckedMemoryCallCertificate{}, fmt.Errorf("optir: checked memory call certificate has an empty root")
	}
	if len(input) == 0 {
		return CheckedMemoryCallCertificate{}, fmt.Errorf("optir: checked memory call certificate has no nodes")
	}
	nodes := make(map[string]checkedMemoryCallCertificateNode, len(input))
	for _, supplied := range input {
		if supplied.Name == "" || supplied.CFG.Name == "" || supplied.Name != supplied.CFG.Name {
			return CheckedMemoryCallCertificate{}, fmt.Errorf("optir: checked memory call certificate node %q does not match CFG %q", supplied.Name, supplied.CFG.Name)
		}
		if _, exists := nodes[supplied.Name]; exists {
			return CheckedMemoryCallCertificate{}, fmt.Errorf("optir: checked memory call certificate repeats node %q", supplied.Name)
		}
		authority, err := cloneCheckedMemoryAuthority(supplied.Authority)
		if err != nil {
			return CheckedMemoryCallCertificate{}, fmt.Errorf("optir: checked memory call certificate node %q: %w", supplied.Name, err)
		}
		nodes[supplied.Name] = checkedMemoryCallCertificateNode{
			cfg: cloneCFG(supplied.CFG), authority: authority,
		}
	}
	if _, exists := nodes[root]; !exists {
		return CheckedMemoryCallCertificate{}, fmt.Errorf("optir: checked memory call certificate is missing root %q", root)
	}

	summaries, err := verifyCheckedMemoryCallCertificateGraph(root, nodes)
	if err != nil {
		return CheckedMemoryCallCertificate{}, err
	}
	certificate := CheckedMemoryCallCertificate{root: root, nodes: nodes, summaries: summaries}
	certificate.fingerprint = fingerprintCheckedMemoryCallCertificate(certificate)
	return certificate, nil
}

// VerifyCheckedMemoryCallCertificate reruns the standalone graph checker and
// binds the certificate to the exact optimized root CFG and authority supplied
// to a consumer.
func VerifyCheckedMemoryCallCertificate(root string, cfg CFG, authority CheckedMemoryAuthority, certificate CheckedMemoryCallCertificate) error {
	if certificate.root == "" || certificate.nodes == nil || certificate.summaries == nil || certificate.fingerprint == "" {
		return fmt.Errorf("optir: checked memory call certificate is missing or corrupted")
	}
	if root == "" || root != certificate.root || cfg.Name != root {
		return fmt.Errorf("optir: checked memory call certificate belongs to a different root")
	}
	if err := verifyCheckedMemoryAuthorityIntegrity(authority); err != nil {
		return err
	}
	if _, err := ProjectCheckedMemory(cfg, authority); err != nil {
		return fmt.Errorf("optir: checked memory call certificate root projection: %w", err)
	}
	rootNode, exists := certificate.nodes[root]
	if !exists || fingerprintCFG(cfg) != fingerprintCFG(rootNode.cfg) || authority.Fingerprint() != rootNode.authority.Fingerprint() {
		return fmt.Errorf("optir: checked memory call certificate belongs to different root inputs")
	}
	summaries, err := verifyCheckedMemoryCallCertificateGraph(certificate.root, certificate.nodes)
	if err != nil {
		return err
	}
	if !reflect.DeepEqual(summaries, certificate.summaries) || certificate.fingerprint != fingerprintCheckedMemoryCallCertificate(certificate) {
		return fmt.Errorf("optir: checked memory call certificate was mutated")
	}
	return nil
}

// FingerprintCertifiedRegionMemoryInput identifies one exact region-memory
// analysis boundary together with the independently checked transitive call
// graph that authorizes its call summaries.
func FingerprintCertifiedRegionMemoryInput(
	cfg CFG,
	metadata RegionMemoryMetadata,
	observability RegionMemoryObservability,
	root string,
	authority CheckedMemoryAuthority,
	certificate CheckedMemoryCallCertificate,
) (string, error) {
	if err := VerifyCheckedMemoryCallCertificate(root, cfg, authority, certificate); err != nil {
		return "", err
	}
	projection, err := ProjectCheckedMemory(cfg, authority)
	if err != nil {
		return "", err
	}
	if !reflect.DeepEqual(metadata, projection.Metadata) || !reflect.DeepEqual(observability, projection.Observability) {
		return "", fmt.Errorf("optir: certified region-memory input does not match its checked authority")
	}
	regionFingerprint, err := FingerprintRegionMemoryInput(cfg, metadata, observability)
	if err != nil {
		return "", err
	}
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.certified-region-memory-input.v1")
	fingerprintString(digest, regionFingerprint)
	fingerprintString(digest, authority.Fingerprint())
	fingerprintString(digest, certificate.Fingerprint())
	return fmt.Sprintf("%x", digest.Sum(nil)), nil
}

func deriveCheckedMemoryCallSummary(cfg CFG, authority CheckedMemoryAuthority, requireExact bool) (CheckedMemoryCallSummary, []CheckedMemoryCallRecord, error) {
	if _, err := ProjectCheckedMemory(cfg, authority); err != nil {
		return CheckedMemoryCallSummary{}, nil, err
	}
	activeAccesses, activeCalls := activeCheckedMemoryAuthority(cfg, authority)
	if requireExact && (len(activeAccesses) != len(authority.records) || len(activeCalls) != len(authority.callRecords)) {
		return CheckedMemoryCallSummary{}, nil, fmt.Errorf("optir: checked memory call summary requires exact active authority coverage")
	}

	byRegion := make(map[RegionID]CheckedMemoryCallAccess)
	add := func(access CheckedMemoryCallAccess) error {
		if access.Region == "" || access.ValueType == "" || access.WholeRegion || access.Volatile || !checkedMemoryCallEffectKind(access.Kind) {
			return fmt.Errorf("optir: malformed checked memory call summary access for region %q", access.Region)
		}
		if prior, exists := byRegion[access.Region]; exists {
			if prior.ValueType != access.ValueType {
				return fmt.Errorf("optir: checked memory call summary region %q has conflicting types %s and %s", access.Region, prior.ValueType, access.ValueType)
			}
			access.Kind = joinCheckedMemoryCallEffectKinds(prior.Kind, access.Kind)
		}
		byRegion[access.Region] = access
		return nil
	}
	for _, record := range activeAccesses {
		if err := add(CheckedMemoryCallAccess{
			Region: record.Region, Kind: record.Kind, ValueType: record.ValueType,
			WholeRegion: false, Volatile: false,
		}); err != nil {
			return CheckedMemoryCallSummary{}, nil, err
		}
	}
	for _, call := range activeCalls {
		for _, access := range call.Accesses {
			if err := add(access); err != nil {
				return CheckedMemoryCallSummary{}, nil, err
			}
		}
	}
	accesses := make([]CheckedMemoryCallAccess, 0, len(byRegion))
	for _, access := range byRegion {
		accesses = append(accesses, access)
	}
	sort.Slice(accesses, func(i, j int) bool { return accesses[i].Region < accesses[j].Region })
	summary := CheckedMemoryCallSummary{accesses: accesses}
	summary.fingerprint = fingerprintCheckedMemoryCallSummary(cfg, activeCalls, accesses)
	return summary, activeCalls, nil
}

func activeCheckedMemoryAuthority(cfg CFG, authority CheckedMemoryAuthority) ([]CheckedMemoryAccessRecord, []CheckedMemoryCallRecord) {
	accesses := make([]CheckedMemoryAccessRecord, 0, len(authority.records))
	calls := make([]CheckedMemoryCallRecord, 0, len(authority.callRecords))
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			if operation.MemoryAccessID != "" {
				accesses = append(accesses, authority.records[operation.MemoryAccessID])
			}
			if operation.MemoryCallID != "" {
				record := authority.callRecords[operation.MemoryCallID]
				record.Accesses = append([]CheckedMemoryCallAccess(nil), record.Accesses...)
				calls = append(calls, record)
			}
		}
	}
	return accesses, calls
}

func verifyCheckedMemoryCallCertificateGraph(root string, nodes map[string]checkedMemoryCallCertificateNode) (map[string]CheckedMemoryCallSummary, error) {
	states := make(map[string]uint8, len(nodes))
	summaries := make(map[string]CheckedMemoryCallSummary, len(nodes))
	var visit func(string) (CheckedMemoryCallSummary, error)
	visit = func(name string) (CheckedMemoryCallSummary, error) {
		switch states[name] {
		case 1:
			return CheckedMemoryCallSummary{}, fmt.Errorf("optir: checked memory call certificate contains a cycle through %q", name)
		case 2:
			return summaries[name], nil
		}
		node, exists := nodes[name]
		if !exists {
			return CheckedMemoryCallSummary{}, fmt.Errorf("optir: checked memory call certificate is missing callee %q", name)
		}
		states[name] = 1
		summary, calls, err := deriveCheckedMemoryCallSummary(node.cfg, node.authority, name != root)
		if err != nil {
			return CheckedMemoryCallSummary{}, fmt.Errorf("optir: checked memory call certificate node %q: %w", name, err)
		}
		for _, call := range calls {
			child, err := visit(call.Callee)
			if err != nil {
				return CheckedMemoryCallSummary{}, err
			}
			if call.SummaryFingerprint != child.Fingerprint() || !reflect.DeepEqual(call.Accesses, child.Accesses()) {
				return CheckedMemoryCallSummary{}, fmt.Errorf("optir: checked memory call certificate node %q has a forged summary for callee %q", name, call.Callee)
			}
		}
		states[name] = 2
		summaries[name] = summary
		return summary, nil
	}
	if _, err := visit(root); err != nil {
		return nil, err
	}
	if len(summaries) != len(nodes) {
		return nil, fmt.Errorf("optir: checked memory call certificate contains unreachable extra nodes")
	}
	return summaries, nil
}

func checkedMemoryCallEffectKind(kind MemoryAccessKind) bool {
	return kind == MemoryRead || kind == MemoryWrite || kind == MemoryReadWrite
}

func joinCheckedMemoryCallEffectKinds(left, right MemoryAccessKind) MemoryAccessKind {
	if left == right {
		return left
	}
	return MemoryReadWrite
}

func fingerprintCheckedMemoryCallSummary(cfg CFG, calls []CheckedMemoryCallRecord, accesses []CheckedMemoryCallAccess) string {
	children := append([]CheckedMemoryCallRecord(nil), calls...)
	sort.Slice(children, func(i, j int) bool { return children[i].ID < children[j].ID })
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.checked-memory-call-summary.v1")
	fingerprintString(digest, fingerprintCFG(cfg))
	fingerprintUint64(digest, uint64(len(children)))
	for _, child := range children {
		fingerprintString(digest, child.ID)
		fingerprintString(digest, child.Callee)
		fingerprintString(digest, child.SummaryFingerprint)
	}
	fingerprintUint64(digest, uint64(len(accesses)))
	for _, access := range accesses {
		fingerprintString(digest, string(access.Region))
		fingerprintString(digest, string(access.Kind))
		fingerprintString(digest, string(access.ValueType))
		fingerprintBool(digest, access.WholeRegion)
		fingerprintBool(digest, access.Volatile)
	}
	return fmt.Sprintf("%x", digest.Sum(nil))
}

func fingerprintCheckedMemoryCallCertificate(certificate CheckedMemoryCallCertificate) string {
	names := make([]string, 0, len(certificate.nodes))
	for name := range certificate.nodes {
		names = append(names, name)
	}
	sort.Strings(names)
	digest := sha256.New()
	fingerprintString(digest, "oak.optir.checked-memory-call-certificate.v1")
	fingerprintString(digest, certificate.root)
	fingerprintUint64(digest, uint64(len(names)))
	for _, name := range names {
		node := certificate.nodes[name]
		fingerprintString(digest, name)
		fingerprintString(digest, fingerprintCFG(node.cfg))
		fingerprintString(digest, node.authority.Fingerprint())
		fingerprintString(digest, certificate.summaries[name].Fingerprint())
	}
	return fmt.Sprintf("%x", digest.Sum(nil))
}

func cloneCheckedMemoryAuthority(authority CheckedMemoryAuthority) (CheckedMemoryAuthority, error) {
	if err := verifyCheckedMemoryAuthorityIntegrity(authority); err != nil {
		return CheckedMemoryAuthority{}, err
	}
	return NewCheckedMemoryAuthorityWithCalls(authority.Records(), authority.CallRecords())
}
