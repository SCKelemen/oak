package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"os"

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
	if err := flags.Parse(args); err != nil {
		return 2
	}
	if *conform != "" {
		if *against == "" || flags.NArg() != 1 {
			fmt.Fprintln(stderr, "usage: oak protocol -conform Name -against module.tla [-json] file.oak")
			return 2
		}
		return conformCommand(*conform, *against, flags.Arg(0), *jsonOut, stdout, stderr)
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
		module, err := compiler.ProtocolTLAWithRecords(decl, path, compiler.RecordDeclarations(tree.Root))
		if err != nil {
			fmt.Fprintf(stderr, "oak protocol: %v\n", err)
			return 1
		}
		if *cfgOut != "" {
			if err := os.WriteFile(*cfgOut, []byte(compiler.ProtocolTLCConfig(decl)), 0o644); err != nil {
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
func conformCommand(name, against, path string, jsonOut bool, stdout, stderr io.Writer) int {
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
		if jsonOut {
			encoded, _ := json.MarshalIndent(report, "", "  ")
			fmt.Fprintln(stdout, string(encoded))
		} else {
			fmt.Fprint(stdout, compiler.FormatTLAConformance(report))
		}
		if report.Conforms {
			return 0
		}
		return 1
	}
	fmt.Fprintf(stderr, "oak protocol: %s declares no protocol %s\n", path, name)
	return 2
}
