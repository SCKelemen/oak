package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"os"
	"strings"

	"github.com/SCKelemen/oak/compiler"
)

// protocolCommand implements `oak protocol -tla Name [-o out.tla] [-cfg out.cfg] file.oak`
// (docs/spec/112-protocols.md): the TLA+ projection of one protocol
// declaration, from the parsed source alone.
func protocolCommand(args []string, stdout, stderr io.Writer) int {
	flags := flag.NewFlagSet("oak protocol", flag.ContinueOnError)
	flags.SetOutput(stderr)
	tla := flags.String("tla", "", "protocol name to render as a TLA+ module")
	output := flags.String("o", "", "write the module here instead of standard output")
	cfgOut := flags.String("cfg", "", "also write a TLC configuration for the module here")
	conform := flags.String("conform", "", "protocol name whose projection a hand-written module must agree with")
	against := flags.String("against", "", "the hand-written TLA+ module to check (with -conform)")
	jsonOut := flags.Bool("json", false, "with -conform, print the report as JSON")
	tlc := flags.Bool("tlc", false, "with -conform, run the TLC refinement check even when the normal form judged")
	againstCfg := flags.String("against-cfg", "", "with -conform, the hand-written module's TLC configuration (its constant values carry into the refinement check)")
	mapping := flags.String("map", "", "with -conform, the refinement mapping of projection variables to the module's: renames (state=st) or TLA+ expressions (count=Cardinality({k \\in 0..1 : acked[k]})), comma-separated at the top level, `<-` accepted for `=`; @file reads the same pairs, one per line, from a file")
	outDir := flags.String("out", "", "with -conform, write the refinement modules here (default: a fresh temporary directory)")
	if err := flags.Parse(args); err != nil {
		return 2
	}
	if *conform != "" {
		if *against == "" || flags.NArg() != 1 {
			fmt.Fprintln(stderr, "usage: oak protocol -conform Name -against module.tla [-against-cfg module.cfg] [-map a=b,...] [-tlc] [-out dir] [-json] file.oak")
			return 2
		}
		renames, err := parseRefinementMapping(*mapping, os.ReadFile)
		if err != nil {
			fmt.Fprintf(stderr, "oak protocol: %v\n", err)
			return 2
		}
		return conformCommand(*conform, *against, flags.Arg(0), conformOptions{json: *jsonOut, tlc: *tlc, againstCfg: *againstCfg, mapping: renames, outDir: *outDir}, stdout, stderr)
	}
	if *tla == "" || flags.NArg() != 1 {
		fmt.Fprintln(stderr, "usage: oak protocol -tla Name [-o out.tla] [-cfg out.cfg] file.oak\n       oak protocol -conform Name -against module.tla [-json] file.oak")
		return 2
	}
	path := flags.Arg(0)
	source, err := os.ReadFile(path)
	if err != nil {
		fmt.Fprintf(stderr, "oak protocol: %v\n", err)
		return 1
	}
	tree, err := compiler.New().WithSource(path, string(source)).Parse().Get()
	if err != nil {
		fmt.Fprintf(stderr, "oak protocol: %v\n", err)
		return 1
	}
	for _, decl := range compiler.Protocols(tree) {
		if decl.Name.Value != *tla {
			continue
		}
		theorems := compiler.InvariantTheorems(tree.Root, decl)
		module, err := compiler.ProtocolTLADeclared(decl, path, compiler.ProtocolDeclarationsOf(tree.Root), theorems)
		if err != nil {
			fmt.Fprintf(stderr, "oak protocol: %v\n", err)
			return 1
		}
		if *cfgOut != "" {
			if err := os.WriteFile(*cfgOut, []byte(compiler.ProtocolTLCConfigDeclared(decl, compiler.ProtocolDeclarationsOf(tree.Root), theorems)), 0o644); err != nil {
				fmt.Fprintf(stderr, "oak protocol: %v\n", err)
				return 1
			}
		}
		if *output == "" {
			fmt.Fprint(stdout, module)
			return 0
		}
		if err := os.WriteFile(*output, []byte(module), 0o644); err != nil {
			fmt.Fprintf(stderr, "oak protocol: %v\n", err)
			return 1
		}
		return 0
	}
	fmt.Fprintf(stderr, "oak protocol: %s declares no protocol %s\n", path, *tla)
	return 1
}

// conformCommand implements `oak protocol -conform Name -against module.tla
// file.oak` (docs/spec/112-protocols.md section 4a): the checker's verdict
// on whether a hand-written module agrees with the projection. Exit 0 when
// it agrees, 1 when it differs or uses an unsupported form, 2 on usage or
// read errors.
type conformOptions struct {
	json       bool
	tlc        bool
	againstCfg string
	mapping    map[string]string
	outDir     string
}

func conformCommand(name, against, path string, opts conformOptions, stdout, stderr io.Writer) int {
	jsonOut := opts.json
	source, err := os.ReadFile(path)
	if err != nil {
		fmt.Fprintf(stderr, "oak protocol: %v\n", err)
		return 2
	}
	module, err := os.ReadFile(against)
	if err != nil {
		fmt.Fprintf(stderr, "oak protocol: %v\n", err)
		return 2
	}
	tree, err := compiler.New().WithSource(path, string(source)).Parse().Get()
	if err != nil {
		fmt.Fprintf(stderr, "oak protocol: %v\n", err)
		return 2
	}
	for _, decl := range compiler.Protocols(tree) {
		if decl.Name.Value != name {
			continue
		}
		report, err := compiler.ProtocolConformanceWith(decl, string(module), compiler.RecordDeclarations(tree.Root), compiler.InvariantTheorems(tree.Root, decl))
		if err != nil {
			fmt.Fprintf(stderr, "oak protocol: %v\n", err)
			return 2
		}
		// The TLC refinement fallback (docs/spec/112-protocols.md section
		// 4a): a module outside the normal form is checked semantically,
		// and any module on request.
		if len(report.Unsupported) > 0 || opts.tlc {
			handCfg := ""
			if opts.againstCfg != "" {
				text, err := os.ReadFile(opts.againstCfg)
				if err != nil {
					fmt.Fprintf(stderr, "oak protocol: %v\n", err)
					return 2
				}
				handCfg = string(text)
			}
			ref, err := compiler.CheckRefinement(nil, decl, string(module), compiler.RecordDeclarations(tree.Root), opts.mapping, handCfg, opts.outDir)
			if err != nil {
				fmt.Fprintf(stderr, "oak protocol: refinement: %v\n", err)
				return 2
			}
			report.Refinement = &ref
		}
		if jsonOut {
			encoded, _ := json.MarshalIndent(report, "", "  ")
			fmt.Fprintln(stdout, string(encoded))
		} else {
			fmt.Fprint(stdout, compiler.FormatTLAConformance(report))
		}
		if ref := report.Refinement; ref != nil {
			// Outside the normal form TLC's verdict is the verdict; on -tlc
			// for a module the normal form read, both must agree.
			switch {
			case !ref.Ran:
				return 2
			case ref.Refines && (len(report.Unsupported) > 0 || len(report.Differences) == 0):
				return 0
			default:
				return 1
			}
		}
		if report.Conforms {
			return 0
		}
		return 1
	}
	fmt.Fprintf(stderr, "oak protocol: %s declares no protocol %s\n", path, name)
	return 2
}

// parseRefinementMapping reads the -map flag of `oak protocol -conform`:
// `proj=hand` or `proj <- hand` pairs separated by top-level commas (a
// comma inside (), [], {} or << >> belongs to the expression), where `hand`
// is a variable of the hand-written module or any TLA+ expression over its
// variables — the refinement mapping of a hand-written MC module,
// `INSTANCE Projection WITH state <- st, count <- Cardinality({k \in 0..1 :
// acked[k]})`. `@path` reads the pairs from a file, one per line (or
// comma-separated), `\*` comments dropped, so a module's mapping lives
// next to it (the dbs pilot's round-five item 9). The value is spliced into
// the generated refinement module verbatim for TLC to parse; nothing here
// evaluates it.
func parseRefinementMapping(spec string, readFile func(string) ([]byte, error)) (map[string]string, error) {
	spec = strings.TrimSpace(spec)
	if strings.HasPrefix(spec, "@") {
		data, err := readFile(strings.TrimPrefix(spec, "@"))
		if err != nil {
			return nil, fmt.Errorf("-map: %v", err)
		}
		var lines []string
		for _, line := range strings.Split(string(data), "\n") {
			if i := strings.Index(line, "\\*"); i >= 0 {
				line = line[:i]
			}
			if line = strings.TrimSpace(line); line != "" {
				lines = append(lines, line)
			}
		}
		spec = strings.Join(lines, ",")
	}
	mapping := map[string]string{}
	for _, pair := range splitTopLevel(spec, ',') {
		if pair = strings.TrimSpace(pair); pair == "" {
			continue
		}
		name, value := "", ""
		if arrow := strings.Index(pair, "<-"); arrow > 0 {
			name, value = pair[:arrow], pair[arrow+2:]
		} else if eq := strings.Index(pair, "="); eq > 0 {
			name, value = pair[:eq], pair[eq+1:]
		}
		name, value = strings.TrimSpace(name), strings.TrimSpace(value)
		if name == "" || value == "" || strings.ContainsAny(name, " \t()[]{}<>.,") {
			return nil, fmt.Errorf("-map takes proj=hand or proj <- expression pairs, got %q", pair)
		}
		if _, dup := mapping[name]; dup {
			return nil, fmt.Errorf("-map names %s twice", name)
		}
		mapping[name] = value
	}
	return mapping, nil
}

// splitTopLevel splits on sep outside every (), [], {} and << >> pair.
func splitTopLevel(s string, sep rune) []string {
	var parts []string
	depth := 0
	start := 0
	runes := []rune(s)
	for i := 0; i < len(runes); i++ {
		switch runes[i] {
		case '(', '[', '{':
			depth++
		case ')', ']', '}':
			depth--
		case '<':
			if i+1 < len(runes) && runes[i+1] == '<' {
				depth++
				i++
			}
		case '>':
			if i+1 < len(runes) && runes[i+1] == '>' {
				depth--
				i++
			}
		case sep:
			if depth == 0 {
				parts = append(parts, string(runes[start:i]))
				start = i + 1
			}
		}
	}
	return append(parts, string(runes[start:]))
}
