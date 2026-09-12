package compiler

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/serialize"
)

// The corpus-wide differential witness: every executable program in the
// golden corpus and the examples tree — anything declaring `main: (): i32`
// — runs through the compiled C and the interpreter, and the two exit
// codes must agree. Agreement is the oracle; no expected values are kept.
// The skip list names programs whose features exist in one realization by
// design (native-only FFI, asm units, multi-file modules) with the reason.
var corpusSkips = map[string]string{
	"c_ffi":          "extern FFI is native-backend only (docs/spec/92-ffi.md)",
	"c_ffi_spans":    "extern FFI and boundary spans are native-backend only (docs/spec/92-ffi.md section 2.5.4)",
	"tail_recursion": "non-terminating by design: exercises the tail-call lowering shape, never runs to completion",
}

var mainI32 = regexp.MustCompile(`(?m)^main\s*:\s*\(\s*\)\s*(:|->)\s*i32\b`)

func TestDifferentialCorpus(t *testing.T) {
	skipInShort(t)
	type program struct{ name, src string }
	var programs []program
	for _, gc := range serialize.GoldenCases() {
		if gc.Skip || !mainI32.MatchString(gc.SourceCode) {
			continue
		}
		programs = append(programs, program{"golden/" + gc.Name, gc.SourceCode})
	}
	examples, _ := filepath.Glob("../examples/*.oak")
	for _, path := range examples {
		src, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		if !mainI32.Match(src) || strings.Contains(string(src), "\nimport ") {
			continue // multi-file programs need module resolution the harness does not do
		}
		programs = append(programs, program{"examples/" + filepath.Base(path), string(src)})
	}
	if len(programs) < 20 {
		t.Fatalf("corpus too small: %d executable programs", len(programs))
	}
	for _, p := range programs {
		p := p
		t.Run(p.name, func(t *testing.T) {
			base := strings.TrimSuffix(filepath.Base(p.name), ".oak")
			if reason, skip := corpusSkips[base]; skip {
				t.Skip(reason)
			}
			code, abnormal := buildAndRun(t, "corpus_"+base, p.src)
			if abnormal {
				t.Fatalf("compiled program exited abnormally (code %d)", code)
			}
			got := interpretChecked(t, p.src)
			// The process exit status is the low byte of main's result.
			if int(got&0xFF) != code&0xFF {
				t.Fatalf("interpreter %d, compiled exit %d", got, code)
			}
		})
	}
}
