package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

// This seam retains the register read, both calls in order, and the return.
// It must not turn the lower runtime's ignored selector into permission to
// erase __WriteMemory's actual register-initialization precondition.
func auditSailRegisterMemoryWrapper(source string) error {
	register, err := exactSailRegister(source, "__defaultRAM")
	if err != nil {
		return err
	}
	if register != "register__defaultRAM:bits(56)" {
		return fmt.Errorf("RAM selector declaration changed: %s", register)
	}
	header, err := sailDeclarationThroughOpen(source, "__WriteMemory")
	if err != nil {
		return err
	}
	const wantHeader = "val__WriteMemory:forall('N:Int).(int('N),bits(56),bits(8*'N))->uniteffect{rreg,wmem}function__WriteMemory(N,address,val_name)={"
	if header != wantHeader {
		return fmt.Errorf("register-reading wrapper signature/binders changed: %s", header)
	}
	body, err := exactSailFunctionBody(source, "__WriteMemory")
	if err != nil {
		return err
	}
	const wantBody = "__WriteRAM(56,N,__defaultRAM,address,val_name);__TraceMemoryWrite(N,address,val_name);return()"
	if compactSail(body) != wantBody {
		return fmt.Errorf("register-reading wrapper body changed: %s", body)
	}
	return nil
}

func auditSailNoDeviceWriteTrace(source string) error {
	signature, err := exactSailValParagraph(source, "__TraceMemoryWrite")
	if err != nil {
		return err
	}
	if signature != "val__TraceMemoryWrite:forall'n'm.(atom('n),bits('m),bits(8*'n))->unit" {
		return fmt.Errorf("no-device write trace signature changed: %s", signature)
	}
	active, err := stripSailComments(source)
	if err != nil {
		return err
	}
	start, err := exactSailFunctionStart(active, "__TraceMemoryWrite")
	if err != nil {
		return err
	}
	// Include continuation lines, not just the first expression line. The
	// official trace has no braces, so stop at the next top-level declaration.
	tail := active[start+len("function"):]
	next := regexp.MustCompile(`(?m)^(?:val|function|register|type|enum|struct|overload|let)[ \t]`).FindStringIndex(tail)
	end := len(active)
	if next != nil {
		end = start + len("function") + next[0]
	}
	if got := compactSail(active[start:end]); got != "function__TraceMemoryWrite(bytes,addr,data)=()" {
		return fmt.Errorf("no-device write trace body/binders changed: %s", got)
	}
	return nil
}

type sailMemoryMutation struct{ name, old, replacement string }

func checkSailMemorySourceGate(t *testing.T, official string, audit func(string) error, mutations []sailMemoryMutation) {
	t.Helper()
	for _, fixture := range []struct {
		path     string
		external bool
	}{
		{official, true},
		{filepath.Join("..", "spec", "sail", "arm_primitives.sail"), false},
	} {
		t.Run(filepath.Base(fixture.path), func(t *testing.T) {
			data, err := os.ReadFile(fixture.path)
			if err != nil {
				if fixture.external {
					requireOracle(t, "official memory source unavailable: "+err.Error())
				}
				t.Fatal(err)
			}
			source := string(data)
			if err := audit(source); err != nil {
				t.Fatal(err)
			}
			for _, mutation := range mutations {
				t.Run(mutation.name, func(t *testing.T) {
					mutant := strings.Replace(source, mutation.old, mutation.replacement, 1)
					if mutant == source {
						t.Fatal("mutation did not change source")
					}
					if err := audit(mutant); err == nil {
						t.Fatal("changed memory wrapper was admitted")
					}
				})
			}
			if err := audit("/*\n" + source + "\n*/"); err == nil {
				t.Fatal("commented source was admitted")
			}
		})
	}
}

func TestSailRegisterMemoryWrapperExactAndMutated(t *testing.T) {
	const write = "__WriteRAM(56, N, __defaultRAM, address, val_name);"
	const trace = "__TraceMemoryWrite(N, address, val_name);"
	checkSailMemorySourceGate(t, filepath.Join(filepath.Dir(sailArmModel), "aarch_mem.sail"),
		auditSailRegisterMemoryWrapper, []sailMemoryMutation{
			{"selector_width", "register __defaultRAM : bits(56)", "register __defaultRAM : bits(52)"},
			{"selector_erased", "register __defaultRAM : bits(56)", "/* register __defaultRAM : bits(56) */"},
			{"selector_duplicate", "register __defaultRAM : bits(56)", "register __defaultRAM : bits(56)\nregister __defaultRAM : bits(56)"},
			{"read_bypassed", write, "__WriteRAM(56, N, address, address, val_name);"},
			{"write_erased", write, "();"},
			{"wrong_count", write, "__WriteRAM(56, 1, __defaultRAM, address, val_name);"},
			{"wrong_address", write, "__WriteRAM(56, N, __defaultRAM, __defaultRAM, val_name);"},
			{"wrong_data", write, "__WriteRAM(56, N, __defaultRAM, address, ~val_name);"},
			{"binders_swapped", "function __WriteMemory (N, address, val_name)", "function __WriteMemory (N, val_name, address)"},
			{"trace_erased", trace, "();"},
			{"calls_reordered", write + "\n    " + trace, trace + "\n    " + write},
			{"return_erased", trace + "\n    return()", trace + "\n    ()"},
		})
}

func TestSailNoDeviceWriteTraceExactAndMutated(t *testing.T) {
	const trace = "function __TraceMemoryWrite(bytes, addr, data) = ()"
	checkSailMemorySourceGate(t, filepath.Join(filepath.Dir(sailArmModel), "no_devices.sail"),
		auditSailNoDeviceWriteTrace, []sailMemoryMutation{
			{"binders_swapped", trace, "function __TraceMemoryWrite(bytes, data, addr) = ()"},
			{"body_changed", trace, "function __TraceMemoryWrite(bytes, addr, data) = throw()"},
			{"continued_effect", trace, trace + ";\n  throw()"},
			{"duplicate", trace, trace + "\n" + trace},
			{"commented", trace, "/* " + trace + " */"},
		})
}
