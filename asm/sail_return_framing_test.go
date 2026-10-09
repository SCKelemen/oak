package asm

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

// Runs without Sail or Lean. The existing formal Sail job also builds the new
// kernel simulation; guarded compiler regeneration is a separate local profile.
func TestSailScalarExecutionReturnFraming(t *testing.T) {
	root := filepath.Join("..", "spec", "sail")
	read := func(name string) []byte {
		t.Helper()
		data, err := os.ReadFile(filepath.Join(root, filepath.FromSlash(name)))
		if err != nil {
			t.Fatal(err)
		}
		return data
	}
	var manifest struct {
		Files map[string]string `json:"files"`
	}
	if err := json.Unmarshal(read("return_execution_manifest.json"), &manifest); err != nil {
		t.Fatal(err)
	}
	if len(manifest.Files) != 9 {
		t.Fatalf("unexpected pin set: %d", len(manifest.Files))
	}
	digest := func(data []byte) string { sum := sha256.Sum256(data); return hex.EncodeToString(sum[:]) }
	for name, want := range manifest.Files {
		data := read(name)
		if digest(data) != want {
			t.Fatalf("guarded return provenance drift: %s", name)
		}
		// Reject actual byte drift, including source/signature and raw artifact edits.
		if len(data) == 0 {
			t.Fatalf("empty artifact: %s", name)
		}
		mutated := append([]byte(nil), data...)
		mutated[len(mutated)/2] ^= 1
		if digest(mutated) == want {
			t.Fatalf("mutation accepted: %s", name)
		}
	}
	compare := func(name, want string) {
		t.Helper()
		if string(read(name)) != want {
			t.Fatalf("body/interface framing drift: %s", name)
		}
	}
	frame := func(raw, namespace, iface, boundary string, names []string) string {
		text := strings.ReplaceAll(raw, "import Out.Defs\nimport Out.Specialization\nimport Out.FakeReal\n", "import ReturnExecution.Defs\nimport ReturnExecution."+iface+"\n")
		text = strings.ReplaceAll(text, "namespace Out.Functions", "namespace "+namespace+"\nopen PreSail")
		text = strings.ReplaceAll(text, "end Out.Functions", "end "+namespace)
		for _, name := range names {
			text = regexp.MustCompile(`\b`+regexp.QuoteMeta(name)+`\b`).ReplaceAllString(text, name+" boundaries")
			text = strings.ReplaceAll(text, "def "+name+" boundaries ", "def "+name+" (boundaries : "+boundary+") ")
		}
		return text
	}
	defs := strings.ReplaceAll(string(read("lean/ReturnExecution/RawDefs.lean")), "import Sail\n", "import Sail\nnamespace ReturnExecution\n") + "\nend ReturnExecution\n"
	compare("lean/ReturnExecution/Defs.lean", defs)
	compare("lean/ReturnExecution/Generated.lean", frame(string(read("lean/ReturnExecution/Raw.lean")), "ReturnExecution.Functions", "Interface", "Boundaries", []string{"aget_SCR_GEN", "IsSecureBelowEL3", "ELUsingAArch32", "S1TranslationRegime__0", "AddrTop", "AArch64_BranchAddr", "BranchTo"}))
	compare("lean/ReturnExecution/ScalarGenerated.lean", frame(string(read("lean/ScalarExecution/Raw.lean")), "ReturnExecution.ScalarFunctions", "ScalarInterface", "ScalarBoundaries", []string{"LSL", "ShiftReg", "__PostDecode", "integer_logical_shiftedreg", "integer_logical_shiftedreg_decode", "branch_unconditional_register", "branch_unconditional_register_decode", "decode64"}))
	iface := strings.ReplaceAll(string(read("lean/ScalarExecution/Interface.lean")), "ScalarExecution", "ReturnExecution")
	compare("lean/ReturnExecution/ScalarInterface.lean", strings.ReplaceAll(iface, "Boundaries", "ScalarBoundaries"))
	bridge := string(read("lean/ScalarExecutionBridge.lean"))
	for _, replacement := range [][2]string{
		{"import ScalarExecution\n", "import ReturnScalar\n"},
		{"namespace Oak.SailBridge.Scalar", "namespace Oak.SailBridge.ExtendedScalar"},
		{"end Oak.SailBridge.Scalar", "end Oak.SailBridge.ExtendedScalar"},
		{"ScalarExecution.Functions", "ReturnExecution.ScalarFunctions"},
		{"ScalarExecution", "ReturnExecution"},
		{"Boundaries", "ScalarBoundaries"},
	} {
		bridge = strings.ReplaceAll(bridge, replacement[0], replacement[1])
	}
	compare("lean/ReturnScalarBridge.lean", bridge)
}
