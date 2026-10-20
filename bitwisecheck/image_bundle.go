package bitwisecheck

import (
	"encoding/json"
	"errors"
)

const (
	ImageSchema       = "oak.checked-image-bundle.v1"
	ImageProfile      = "bitwise-source-complete-images-local-invocation-v1"
	ImageProofPackage = "c9452b2c3772ccf9367be36735063855b0cef5d1"
	MaxImageBytes     = 5120
)

var imageBundleSeal = &seal{3}

// CheckedImageBundle has no public success constructor. Its zero value is invalid.
// A valid value owns the exact bytes checked together in one successful request.
// Payloads use immutable strings, so safe reflection cannot obtain mutable byte
// backing storage through reflect.Value.Bytes on an unexported slice.
// Closing its ImageInstallation does not revoke the historical completed admission.
type CheckedImageBundle struct {
	authority             *seal
	source, wasm, arm, rv string
	receipt               ImageReceipt
}

func (b *CheckedImageBundle) Valid() bool { return b != nil && b.authority == imageBundleSeal }
func (b *CheckedImageBundle) SourceBytes() []byte {
	if !b.Valid() {
		return nil
	}
	return []byte(b.source)
}
func (b *CheckedImageBundle) WasmBytes() []byte {
	if !b.Valid() {
		return nil
	}
	return []byte(b.wasm)
}
func (b *CheckedImageBundle) ARM64ImageBytes() []byte {
	if !b.Valid() {
		return nil
	}
	return []byte(b.arm)
}
func (b *CheckedImageBundle) RV64ImageBytes() []byte {
	if !b.Valid() {
		return nil
	}
	return []byte(b.rv)
}
func (b *CheckedImageBundle) Receipt() ImageReceipt {
	if !b.Valid() {
		return ImageReceipt{}
	}
	return cloneImageReceipt(b.receipt)
}
func (b *CheckedImageBundle) MarshalJSON() ([]byte, error) {
	if !b.Valid() {
		return nil, ErrInvalidBundle
	}
	return json.Marshal(b.Receipt())
}

// UnmarshalJSON deliberately cannot turn historical JSON into admission authority.
func (b *CheckedImageBundle) UnmarshalJSON([]byte) error {
	return errors.New("bitwisecheck: receipts cannot restore authority; rerun CheckImageBundle on actual bytes")
}

// ImageReceipt is a historical diagnostic report, never an admission capability.
// Digests help identify files; admission compares all four byte arrays exactly.
type ImageReceipt struct {
	Schema            string         `json:"schema"`
	Profile           string         `json:"profile"`
	ProofPackage      string         `json:"proof_package"`
	ProofSourceSHA256 string         `json:"proof_source_sha256"`
	LeanVersion       string         `json:"lean_version"`
	LeanCommit        string         `json:"lean_commit"`
	ArchiveSHA256     string         `json:"archive_sha256"`
	Source            ByteIdentity   `json:"source"`
	Wasm              ByteIdentity   `json:"wasm"`
	ARM64             ByteIdentity   `json:"arm64"`
	RV64              ByteIdentity   `json:"rv64"`
	Declaration       Declaration    `json:"declaration"`
	Targets           [3]ImageTarget `json:"targets"`
	Roots             [3]Root        `json:"roots"`
	Assumptions       []string       `json:"assumptions"`
	Guarantees        []string       `json:"guarantees"`
	Exclusions        []string       `json:"exclusions"`
}

// ImageTarget distinguishes the ELF entry from the named function address.
type ImageTarget struct {
	Target          string `json:"target"`
	Container       string `json:"container"`
	ABI             string `json:"abi"`
	Symbol          string `json:"symbol"`
	SectionIndex    int    `json:"section_index"`
	FileOffset      int    `json:"file_offset"`
	BodySize        int    `json:"body_size"`
	ELFEntry        int    `json:"elf_entry"`
	FunctionAddress int    `json:"function_address"`
}

func cloneImageReceipt(r ImageReceipt) ImageReceipt {
	for n := range r.Roots {
		r.Roots[n].Axioms = append([]string{}, r.Roots[n].Axioms...)
	}
	r.Assumptions = append([]string{}, r.Assumptions...)
	r.Guarantees = append([]string{}, r.Guarantees...)
	r.Exclusions = append([]string{}, r.Exclusions...)
	return r
}
func makeImageReceipt(w imageWireRecord, in [4]string, sourceHash string) ImageReceipt {
	name := string(intBytes(w.Declaration.Name))
	return ImageReceipt{Schema: ImageSchema, Profile: ImageProfile, ProofPackage: ImageProofPackage, ProofSourceSHA256: sourceHash, LeanVersion: LeanVersion, LeanCommit: LeanCommit, ArchiveSHA256: ArchiveSHA256,
		Source: identify(in[0]), Wasm: identify(in[1]), ARM64: identify(in[2]), RV64: identify(in[3]),
		Declaration: Declaration{Name: name, Parameters: [2]string{string(intBytes(w.Declaration.First)), string(intBytes(w.Declaration.Second))}, Operation: w.Declaration.Op, InputWidths: [2]int{32, 32}, ResultWidth: 32},
		Targets:     [3]ImageTarget{{Target: "core/wasm32", Container: "Wasm", ABI: "two i32 inputs, one i32 result", Symbol: name}, {Target: "linux/arm64", Container: "ELF64 ET_EXEC", ABI: "low W0/W1 u32 inputs; zero-extended X0 result; X30 return; SP/NZCV and other-register preservation", Symbol: "oak_" + name, SectionIndex: 1, FileOffset: 4108, BodySize: 8, ELFEntry: 65536, FunctionAddress: 65548}, {Target: "linux/riscv64", Container: "ELF64 ET_EXEC", ABI: "LP64D; sign-extended result; clearLow-RA return; restored SP/s1/s2; exact frame memory", Symbol: "oak_" + name, SectionIndex: 1, FileOffset: 4112, BodySize: 36, ELFEntry: 65536, FunctionAddress: 65552}},
		Roots:       [3]Root{w.Roots[0], w.Roots[1], w.Roots[2]},
		Guarantees:  []string{"Exact original canonical source grammar and complete Wasm/ARM64/RV64 image binding, with universal successful full-u32 results under the stated local invocation premises.", "ARM: zero-extended X0 result, all other registers unchanged, return PC equal to caller X30, SP and NZCV unchanged.", "RV: sign-extended result in a0, preservation of all registers except x0/a0 relative to the initialized LP64D entry state, restored SP/s1/s2, clearLow-RA return, exact frameMemory, and unchanged memory outside the sixteen saved frame bytes."},
		Assumptions: []string{"Canonical ASCII single-function source grammar and existing typed-expression interpretation.", "Wasm bounded module loader/interpreter.", "ARM low W0/W1 inputs, arbitrary high halves; modeled local invocation with immutable/separate instructions and no-fault scalar projection.", "RV LP64D entry; SP >= 96 and 16-byte aligned; ordinary coherent readable/writable noninterfering 96-byte stack frame.", "Execution begins at the decoded named-function address with initialized ABI/frame state, immutable/separate instructions and explicit flat MinimalELF model loading."},
		Exclusions:  []string{"Whole-language, package, parser/compiler correctness and external Wasm engine/Core refinement.", "ELF-entry/startup execution, Linux loader/process exit, system linker, physical fetch/mapping/coherence, faults, hardware ISA fidelity and physical return-destination correctness.", "Malicious same-UID processes, unsafe in-process code and compromised host/toolchain."}}
}
