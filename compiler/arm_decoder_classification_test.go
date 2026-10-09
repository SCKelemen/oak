package compiler

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/target"
)

// This is actual compiler/ELF-extraction correspondence to the byte artifact,
// followed by a kernel-checked classification. It is not a universal compiler,
// loader, Sail-parser, or full generated-decoder execution proof.
func TestArmDecoderClassificationCompilerBytes(t *testing.T) {
	library := os.Getenv("OAK_ARM_CLASSIFICATION_LIB")
	if library == "" {
		if os.Getenv("OAK_REQUIRE_ARM_CLASSIFICATION") == "1" {
			t.Fatal("the bounded classification library is required")
		}
		t.Skip("formal-sail.yml requires the built classification library")
	}
	lean, err := exec.LookPath("lean")
	if err != nil {
		t.Fatal(err)
	}
	core, err := filepath.Abs(filepath.Join("..", "spec", "lean", ".lake", "build", "lib", "lean"))
	if err != nil {
		t.Fatal(err)
	}
	if override := os.Getenv("OAK_ARM_CLASSIFICATION_CORE_LIB"); override != "" {
		core = override // Local cache is separately checked against all 15 source modules.
	}
	var proof strings.Builder
	proof.WriteString("import Oak.ArmDecoderClassification.ByteBinding\nopen Oak.ArmDecoderClassification Oak.AArch64BitwiseFunction\n")
	for _, tc := range []struct{ op, symbol string }{{"and", "&"}, {"or", "|"}, {"xor", "^"}} {
		original := fmt.Sprintf("mix: (a: u32, b: u32): u32 = a %s b\n", tc.symbol)
		code := sourceBitwiseFunctionBytes(t, original, "mix", target.ArchArm64)
		if len(code) != 8 {
			t.Fatalf("unexpected function extent: %x", code)
		}
		var values []string
		for _, b := range code {
			values = append(values, fmt.Sprint(b))
		}
		literal := "[" + strings.Join(values, ",") + "]"
		fmt.Fprintf(&proof, "theorem bytes_%s : functionBytes .%s = %s := by decide +kernel\n", tc.op, tc.op, literal)
		fmt.Fprintf(&proof, "theorem classified_%s : classifyFunction %s = some (logicalIndex .%s,1522) := by rw [← bytes_%s]; exact function_bytes_classified .%s\n", tc.op, literal, tc.op, tc.op, tc.op)
		fmt.Fprintf(&proof, "#print axioms classified_%s\n", tc.op)
		t.Logf("original source %q -> exact ARM bytes %x -> source-clause classification", original, code)
	}
	path := filepath.Join(t.TempDir(), "CompilerDecoderClassification.lean")
	if err := os.WriteFile(path, []byte(proof.String()), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(t.Context(), 2*time.Minute)
	defer cancel()
	cmd := exec.CommandContext(ctx, lean, "-j1", path)
	cmd.Dir = filepath.Join("..", "spec", "lean")
	cmd.Env = append(os.Environ(), "LEAN_PATH="+library+string(os.PathListSeparator)+core)
	if output, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("compiler byte/classification pin: %v\n%s", err, output)
	} else {
		matches := regexp.MustCompile(`'classified_(and|or|xor)' depends on axioms: \[([^]]*)\]`).FindAllStringSubmatch(string(output), -1)
		seen := map[string]bool{}
		for _, match := range matches {
			if seen[match[1]] {
				t.Fatalf("duplicate closure: %s", match[1])
			}
			seen[match[1]] = true
			for _, axiom := range strings.Split(match[2], ",") {
				switch strings.TrimSpace(axiom) {
				case "", "propext", "Classical.choice", "Quot.sound":
				default:
					t.Fatalf("unexpected proof authority: %s", axiom)
				}
			}
		}
		if len(seen) != 3 {
			t.Fatalf("missing compiler-classification closure audit: %s", output)
		}
	}
}
