// Package leansources embeds the reviewed checked-bundle proof closure directly
// from its authoritative .lean files. No duplicate proof-source bundle is kept.
package leansources

import (
	"crypto/sha256"
	"embed"
	"encoding/binary"
	"encoding/hex"
	"sort"
)

//go:embed Oak/WasmAssemblerExtracted.lean Oak/WasmAssemblerLaws.lean Oak/WasmLEB.lean Oak/WasmEncoding.lean Oak/WasmAssemblerBytes.lean Oak/WasmInstruction.lean Oak/WasmAssemblerInstruction.lean Oak/WasmAssemblerSequence.lean Oak/WasmAssemblerTotal.lean Oak/WasmNumeric.lean Oak/WasmExecution.lean Oak/BitwiseFunction.lean Oak/BitwiseModule.lean Oak/ByteFields.lean Oak/BitwiseSource.lean Oak/AssemblerSemantics.lean Oak/IntegerDivision.lean Oak/LoweringRefinement.lean Oak/BitwiseSourceLowering.lean Oak/MinimalELF.lean Oak/AArch64Encoding.lean Oak/AArch64ReturnEncoding.lean Oak/AArch64BitwiseFunction.lean Oak/RV64Relocation.lean Oak/RiscV.lean Oak/RiscVMaterialization.lean Oak/RiscVCallExecution.lean Oak/RiscVBranchEncoding.lean Oak/RiscVBitwiseFunction.lean Oak/AArch64CompareBranchEncoding.lean Oak/AArch64ConditionalBranch.lean Oak/ArmASL.lean Oak/AArch64BranchExecution.lean Oak/ObjectRelocation.lean Oak/AArch64DirectBranchEncoding.lean Oak/ControlFlowPlan.lean Oak/AArch64ControlFlow.lean Oak/AArch64SpillMemory.lean Oak/RiscVFramedBitwise.lean Oak/NativeBitwiseObject.lean Oak/BitwiseSourceObjectParity.lean Oak/CheckedBundleAudit.lean
var sourceFiles embed.FS

var buildOrder = [...]string{
	"Oak/WasmAssemblerExtracted.lean",
	"Oak/WasmAssemblerLaws.lean",
	"Oak/WasmLEB.lean",
	"Oak/WasmEncoding.lean",
	"Oak/WasmAssemblerBytes.lean",
	"Oak/WasmInstruction.lean",
	"Oak/WasmAssemblerInstruction.lean",
	"Oak/WasmAssemblerSequence.lean",
	"Oak/WasmAssemblerTotal.lean",
	"Oak/WasmNumeric.lean",
	"Oak/WasmExecution.lean",
	"Oak/BitwiseFunction.lean",
	"Oak/BitwiseModule.lean",
	"Oak/ByteFields.lean",
	"Oak/BitwiseSource.lean",
	"Oak/AssemblerSemantics.lean",
	"Oak/IntegerDivision.lean",
	"Oak/LoweringRefinement.lean",
	"Oak/BitwiseSourceLowering.lean",
	"Oak/MinimalELF.lean",
	"Oak/AArch64Encoding.lean",
	"Oak/AArch64ReturnEncoding.lean",
	"Oak/AArch64BitwiseFunction.lean",
	"Oak/RV64Relocation.lean",
	"Oak/RiscV.lean",
	"Oak/RiscVMaterialization.lean",
	"Oak/RiscVCallExecution.lean",
	"Oak/RiscVBranchEncoding.lean",
	"Oak/RiscVBitwiseFunction.lean",
	"Oak/AArch64CompareBranchEncoding.lean",
	"Oak/AArch64ConditionalBranch.lean",
	"Oak/ArmASL.lean",
	"Oak/AArch64BranchExecution.lean",
	"Oak/ObjectRelocation.lean",
	"Oak/AArch64DirectBranchEncoding.lean",
	"Oak/ControlFlowPlan.lean",
	"Oak/AArch64ControlFlow.lean",
	"Oak/AArch64SpillMemory.lean",
	"Oak/RiscVFramedBitwise.lean",
	"Oak/NativeBitwiseObject.lean",
	"Oak/BitwiseSourceObjectParity.lean",
	"Oak/CheckedBundleAudit.lean",
}

// Source contains a fresh owned copy; callers cannot mutate embedded bytes.
type Source struct {
	Path  string
	Bytes []byte
}

func Sources() []Source {
	out := make([]Source, 0, len(buildOrder))
	for _, path := range buildOrder {
		b, err := sourceFiles.ReadFile(path)
		if err != nil {
			panic(err)
		}
		out = append(out, Source{path, b})
	}
	return out
}

// Identity includes the auditor and semantic sources in a deterministic,
// length-framed digest. It is diagnostic; the compiled-in sources are authority.
func Identity() string {
	names := append([]string(nil), buildOrder[:]...)
	sort.Strings(names)
	h := sha256.New()
	h.Write([]byte("oak.checked-bundle.proof-sources.v1\x00"))
	var length [8]byte
	for _, path := range names {
		b, err := sourceFiles.ReadFile(path)
		if err != nil {
			panic(err)
		}
		binary.BigEndian.PutUint64(length[:], uint64(len(path)))
		h.Write(length[:])
		h.Write([]byte(path))
		binary.BigEndian.PutUint64(length[:], uint64(len(b)))
		h.Write(length[:])
		h.Write(b)
	}
	return hex.EncodeToString(h.Sum(nil))
}
