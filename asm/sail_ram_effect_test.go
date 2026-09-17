package asm

import (
	"crypto/sha256"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// Both the official source and the fragment used for generation must retain
// the exact external binding and forwarding wrapper. A pure no-op, swapped
// arguments, or an inactive declaration cannot satisfy this source seam.
func auditSailRAMWrapper(source string) error {
	for name, want := range map[string]string{
		"___WriteRAM": `val___WriteRAM="write_ram":forall'n'm.(atom('m),atom('n),bits('m),bits('m),bits(8*'n))->uniteffect{wmem}`,
		"__WriteRAM":  "val__WriteRAM:forall'n'm.(atom('m),atom('n),bits('m),bits('m),bits(8*'n))->uniteffect{wmem}",
	} {
		got, err := exactSailValParagraph(source, name)
		if err != nil {
			return err
		}
		if got != want {
			return fmt.Errorf("%s declaration changed: %s", name, got)
		}
	}
	header, err := sailDeclarationThroughOpen(source, "__WriteRAM")
	if err != nil {
		return err
	}
	const wantHeader = "val__WriteRAM:forall'n'm.(atom('m),atom('n),bits('m),bits('m),bits(8*'n))->uniteffect{wmem}function__WriteRAM(addr_length,bytes,hex_ram,addr,data)={"
	if header != wantHeader {
		return fmt.Errorf("__WriteRAM binders changed: %s", header)
	}
	body, err := exactSailFunctionBody(source, "__WriteRAM")
	if err != nil {
		return err
	}
	if compactSail(body) != "___WriteRAM(addr_length,bytes,hex_ram,addr,data)" {
		return fmt.Errorf("__WriteRAM forwarding changed: %s", body)
	}
	return nil
}

func TestSailNoDeviceRAMWrapperExactAndMutated(t *testing.T) {
	for _, fixture := range []struct {
		path     string
		external bool
	}{
		{filepath.Join(filepath.Dir(sailArmModel), "no_devices.sail"), true},
		{filepath.Join("..", "spec", "sail", "arm_primitives.sail"), false},
	} {
		t.Run(filepath.Base(fixture.path), func(t *testing.T) {
			bytes, err := os.ReadFile(fixture.path)
			if err != nil {
				if fixture.external {
					requireOracle(t, "RAM wrapper source unavailable: "+err.Error())
				}
				t.Fatal(err)
			}
			source := string(bytes)
			if err := auditSailRAMWrapper(source); err != nil {
				t.Fatal(err)
			}
			for _, mutation := range []struct{ name, old, replacement string }{
				{"external_target", `"write_ram"`, `"read_ram"`},
				{"drop_effect", "___WriteRAM(addr_length, bytes, hex_ram, addr, data)", "()"},
				{"wrong_address", "___WriteRAM(addr_length, bytes, hex_ram, addr, data)", "___WriteRAM(addr_length, bytes, hex_ram, hex_ram, data)"},
				{"wrong_count", "___WriteRAM(addr_length, bytes, hex_ram, addr, data)", "___WriteRAM(addr_length, addr_length, hex_ram, addr, data)"},
				{"swapped_binders", "function __WriteRAM(addr_length, bytes, hex_ram, addr, data)", "function __WriteRAM(addr_length, bytes, addr, hex_ram, data)"},
			} {
				t.Run(mutation.name, func(t *testing.T) {
					changed := strings.Replace(source, mutation.old, mutation.replacement, 1)
					if changed == source {
						t.Fatal("mutation did not change the source")
					}
					if err := auditSailRAMWrapper(changed); err == nil {
						t.Fatal("changed RAM wrapper was admitted")
					}
				})
			}
			if err := auditSailRAMWrapper("/*\n" + source + "\n*/"); err == nil {
				t.Fatal("a commented copy of the wrapper was admitted")
			}
		})
	}
}

func auditLemPlainRAM(source []byte) error {
	// Pin the whole official file: comments cannot hide or fabricate an
	// active declaration while preserving this exact-source check.
	const pinned = "96751fd026b0a0406d6c6b6fd4f363b3e27ac8fc61895ea229bfe2d833b4b071"
	if got := fmt.Sprintf("%x", sha256.Sum256(source)); got != pinned {
		return fmt.Errorf("official aarch64_extras.lem hash = %s, want %s", got, pinned)
	}
	return nil
}

// The separate Lem backend emits Write_plain requests, not release writes.
// A theorem about Lean's sequential byte map is not a CAT interpretation of
// these requests; this guard pins the distinction, not a backend refinement.
func TestSailLemRAMRequestsRemainPlain(t *testing.T) {
	source, err := os.ReadFile(filepath.Join(filepath.Dir(sailArmModel), "..", "aarch64_extras.lem"))
	if err != nil {
		requireOracle(t, "official Lem external semantics unavailable: "+err.Error())
	}
	if err := auditLemPlainRAM(source); err != nil {
		t.Fatal(err)
	}
	const request = "write_mem_ea Write_plain () address size >>\n  write_mem Write_plain () address size value >>= fun _ ->\n  return ()"
	if strings.Count(string(source), request) != 1 {
		t.Fatal("official plain-write request chain changed")
	}
	for _, change := range []string{"Write_release", "Write_exclusive"} {
		mutant := strings.Replace(string(source), "Write_plain", change, 1)
		if err := auditLemPlainRAM([]byte(mutant)); err == nil {
			t.Fatalf("changed write kind %s was admitted", change)
		}
	}
}
