package compiler

import (
	"sort"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/stdlib"
)

// The two realizations of the IO port (docs/spec/120-io.md) export one
// surface: every pub declaration of iosim that is part of the port has the
// same spelling in ionative, and vice versa. Realization-specific hooks are
// prefixed with the package name (iosim_crash, ionative_last_errno) and are
// the only differences allowed.
func portSurface(t *testing.T, name string) map[string]string {
	t.Helper()
	p := parser.New(layout.New(scanner.New(stdlib.Packages[name])))
	program := p.ParseProgram()
	if len(p.Errors()) != 0 {
		t.Fatalf("%s: parse errors: %v", name, p.Errors())
	}
	surface := map[string]string{}
	for _, stmt := range program.Statements {
		switch d := stmt.(type) {
		case *ast.FunctionStatement:
			if d.Name == nil || !d.Exported || strings.HasPrefix(d.Name.Value, name+"_") {
				continue
			}
			params := make([]string, 0, len(d.Parameters))
			for _, parameter := range d.Parameters {
				params = append(params, parameter.Name.Value+": "+parameter.Type.String())
			}
			ret := ""
			if d.ReturnType != nil {
				ret = d.ReturnType.String()
			}
			surface[d.Name.Value] = "(" + strings.Join(params, ", ") + "): " + ret
		case *ast.ADTType:
			if d.Name == nil || !d.Exported {
				continue
			}
			surface[d.Name.Value] = d.String()
		}
	}
	return surface
}

func TestIoPortRealizationsShareOneSurface(t *testing.T) {
	sim := portSurface(t, "iosim")
	native := portSurface(t, "ionative")
	names := map[string]bool{}
	for name := range sim {
		names[name] = true
	}
	for name := range native {
		names[name] = true
	}
	sorted := make([]string, 0, len(names))
	for name := range names {
		sorted = append(sorted, name)
	}
	sort.Strings(sorted)
	for _, name := range sorted {
		if sim[name] != native[name] {
			t.Errorf("%s differs between realizations:\n  iosim:    %s\n  ionative: %s", name, sim[name], native[name])
		}
	}
	for _, want := range []string{"io_attach", "io_open_region", "io_submit", "io_wait", "io_poll", "io_request", "io_buffer", "io_pread_sync", "io_pwrite_sync", "io_fsync_sync", "io_op_fsyncdir", "io_err_canceled", "IoRing", "IoRequest", "IoCompletion"} {
		if _, ok := sim[want]; !ok {
			t.Errorf("port surface lacks %s", want)
		}
	}
}
