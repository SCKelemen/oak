// Package bitwisecheck admits one canonical source/Wasm/ARM64/RV64 bundle with
// the pinned Lean kernel. It does not promote legacy compiler verdicts.
//
// The authentic Oak executable, embedded reviewed proof and auditor, pinned
// official Lean distribution, /usr/bin/zstd, system libraries, host OS and
// same-user filesystem custody are trusted. Private snapshots are not protection
// against a malicious same-UID process or unsafe code inside the caller process.
package bitwisecheck

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
)

const (
	Schema               = "oak.checked-bundle.v1"
	Profile              = "bitwise-source-wasm-arm64-rv64-v1"
	ProofPackage         = "698f6a7b013df508a831d391fe425f4f27cf4581"
	LeanVersion          = "4.33.1"
	LeanCommit           = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
	ArchiveSHA256        = "890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235"
	ArchiveSize    int64 = 570405234
	MaxSourceBytes       = 2048
	MaxWasmBytes         = 1024
	MaxObjectBytes       = 2048
	MaxDriverBytes       = 65536
	MaxOutputBytes       = 65536
)

var ErrInvalidInstallation = errors.New("bitwisecheck: installation is nil, uninitialized, or closed")
var ErrInvalidBundle = errors.New("bitwisecheck: bundle has no live admission authority")
var ErrBounds = errors.New("bitwisecheck: resource bound exceeded")
var ErrProtocol = errors.New("bitwisecheck: invalid checker protocol")

type seal struct{ marker byte }

var bundleSeal = &seal{1}

// CheckedBundle has no public success constructor. Its zero value is invalid.
// A valid value owns the exact bytes checked together in one successful request.
// Payloads use immutable strings, so safe reflection cannot obtain mutable byte
// backing storage through reflect.Value.Bytes on an unexported slice.
// Closing its Installation does not revoke the historical completed admission.
type CheckedBundle struct {
	authority             *seal
	source, wasm, arm, rv string
	receipt               Receipt
}

func (b *CheckedBundle) Valid() bool { return b != nil && b.authority == bundleSeal }
func (b *CheckedBundle) SourceBytes() []byte {
	if !b.Valid() {
		return nil
	}
	return []byte(b.source)
}
func (b *CheckedBundle) WasmBytes() []byte {
	if !b.Valid() {
		return nil
	}
	return []byte(b.wasm)
}
func (b *CheckedBundle) ARM64Bytes() []byte {
	if !b.Valid() {
		return nil
	}
	return []byte(b.arm)
}
func (b *CheckedBundle) RV64Bytes() []byte {
	if !b.Valid() {
		return nil
	}
	return []byte(b.rv)
}
func (b *CheckedBundle) Receipt() Receipt {
	if !b.Valid() {
		return Receipt{}
	}
	return cloneReceipt(b.receipt)
}
func (b *CheckedBundle) MarshalJSON() ([]byte, error) {
	if !b.Valid() {
		return nil, ErrInvalidBundle
	}
	return json.Marshal(b.Receipt())
}

// UnmarshalJSON deliberately cannot turn historical JSON into admission authority.
func (b *CheckedBundle) UnmarshalJSON([]byte) error {
	return errors.New("bitwisecheck: receipts cannot restore authority; rerun CheckBundle on actual bytes")
}

// Receipt is a historical diagnostic report, never an admission capability.
// Digests help identify files; admission compares all four byte arrays exactly.
type Receipt struct {
	Schema            string       `json:"schema"`
	Profile           string       `json:"profile"`
	ProofPackage      string       `json:"proof_package"`
	ProofSourceSHA256 string       `json:"proof_source_sha256"`
	LeanVersion       string       `json:"lean_version"`
	LeanCommit        string       `json:"lean_commit"`
	ArchiveSHA256     string       `json:"archive_sha256"`
	Source            ByteIdentity `json:"source"`
	Wasm              ByteIdentity `json:"wasm"`
	ARM64             ByteIdentity `json:"arm64"`
	RV64              ByteIdentity `json:"rv64"`
	Declaration       Declaration  `json:"declaration"`
	Targets           [3]Target    `json:"targets"`
	Roots             [3]Root      `json:"roots"`
	Assumptions       []string     `json:"assumptions"`
	Exclusions        []string     `json:"exclusions"`
}
type ByteIdentity struct {
	Length int    `json:"length"`
	SHA256 string `json:"sha256"`
}
type Declaration struct {
	Name        string    `json:"name"`
	Parameters  [2]string `json:"parameters"`
	Operation   string    `json:"operation"`
	InputWidths [2]int    `json:"input_widths"`
	ResultWidth int       `json:"result_width"`
}

// Target reports the checked export/symbol. SectionIndex, FileOffset, BodySize
// and Entry describe native ELF binding only; Wasm leaves these fields zero.
type Target struct {
	Target       string `json:"target"`
	Container    string `json:"container"`
	ABI          string `json:"abi"`
	Symbol       string `json:"symbol"`
	SectionIndex int    `json:"section_index"`
	FileOffset   int    `json:"file_offset"`
	BodySize     int    `json:"body_size"`
	Entry        int    `json:"entry"`
}
type Root struct {
	Name   string   `json:"name"`
	Axioms []string `json:"axioms"`
}

func identify(b string) ByteIdentity {
	h := sha256.Sum256([]byte(b))
	return ByteIdentity{len(b), hex.EncodeToString(h[:])}
}
func cloneReceipt(r Receipt) Receipt {
	for n := range r.Roots {
		r.Roots[n].Axioms = append([]string{}, r.Roots[n].Axioms...)
	}
	r.Assumptions = append([]string{}, r.Assumptions...)
	r.Exclusions = append([]string{}, r.Exclusions...)
	return r
}
func makeReceipt(w wireRecord, in [4]string, sourceHash string) Receipt {
	name := string(intBytes(w.Declaration.Name))
	return Receipt{Schema: Schema, Profile: Profile, ProofPackage: ProofPackage, ProofSourceSHA256: sourceHash, LeanVersion: LeanVersion, LeanCommit: LeanCommit, ArchiveSHA256: ArchiveSHA256,
		Source: identify(in[0]), Wasm: identify(in[1]), ARM64: identify(in[2]), RV64: identify(in[3]),
		Declaration: Declaration{Name: name, Parameters: [2]string{string(intBytes(w.Declaration.First)), string(intBytes(w.Declaration.Second))}, Operation: w.Declaration.Op, InputWidths: [2]int{32, 32}, ResultWidth: 32},
		Targets:     [3]Target{{Target: "core/wasm32", Container: "Wasm", ABI: "two i32 inputs, one i32 result", Symbol: name}, {Target: "linux/arm64", Container: "ELF64 ET_REL", ABI: "low W0/W1 u32 inputs; no-fault scalar projection", Symbol: "oak_" + name, SectionIndex: 1, FileOffset: 64, BodySize: 8}, {Target: "linux/riscv64", Container: "ELF64 ET_REL", ABI: "LP64D; 96-byte stack frame", Symbol: "oak_" + name, SectionIndex: 1, FileOffset: 64, BodySize: 36}},
		Roots:       [3]Root{w.Roots[0], w.Roots[1], w.Roots[2]},
		Assumptions: []string{"Canonical ASCII single-function source grammar and existing typed-expression interpretation.", "Wasm bounded module loader/interpreter.", "ARM low W0/W1 inputs, arbitrary high halves; aligned base and base + 8 < 2^64; no-fault scalar projection.", "RV LP64D entry; aligned base and base + 36 < 2^64; SP >= 96 and 16-byte aligned; ordinary coherent readable/writable noninterfering 96-byte stack frame.", "Native flat section loading with immutable/separate instructions."},
		Exclusions:  []string{"Whole-language, package, parser/compiler correctness and external Wasm engine/Core refinement.", "System linker, physical fetch/mapping/coherence, faults and physical return-destination correctness.", "Composed SP/callee-save guarantees; the audited composed theorem observes full-u32 results.", "Malicious same-UID processes, unsafe in-process code and compromised host/toolchain."}}
}
