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
	mapping := flags.String("map", "", "with -conform, projection-to-module variable renames for the refinement check: state=st,count=n")
	outDir := flags.String("out", "", "with -conform, write the refinement modules here (default: a fresh temporary directory)")
	if err := flags.Parse(args); err != nil {
		return 2
	}
	if *conform != "" {
		if *against == "" || flags.NArg() != 1 {
			fmt.Fprintln(stderr, "usage: oak protocol -conform Name -against module.tla [-against-cfg module.cfg] [-map a=b,...] [-tlc] [-out dir] [-json] file.oak")
			return 2
		}
		renames := map[string]string{}
		for _, pair := range strings.Split(*mapping, ",") {
			if pair = strings.TrimSpace(pair); pair == "" {
				continue
			}
			eq := strings.Index(pair, "=")
			if eq <= 0 || eq == len(pair)-1 {
				fmt.Fprintf(stderr, "oak protocol: -map takes proj=hand pairs, got %q\n", pair)
				return 2
			}
			renames[strings.TrimSpace(pair[:eq])] = strings.TrimSpace(pair[eq+1:])
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
		module, err := compiler.ProtocolTLAWithDeclarations(decl, path, compiler.ProtocolDeclarationsOf(tree.Root))
		if err != nil {
			fmt.Fprintf(stderr, "oak protocol: %v\n", err)
			return 1
		}
		if *cfgOut != "" {
			if err := os.WriteFile(*cfgOut, []byte(compiler.ProtocolTLCConfigWithDeclarations(decl, compiler.ProtocolDeclarationsOf(tree.Root))), 0o644); err != nil {
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
		report, err := compiler.ProtocolConformance(decl, string(module), compiler.RecordDeclarations(tree.Root))
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
