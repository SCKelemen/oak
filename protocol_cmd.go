package main

import (
	"flag"
	"fmt"
	"io"
	"os"

	"github.com/SCKelemen/oak/compiler"
)

// protocolCommand implements `oak protocol -tla Name [-o out.tla] file.oak`
// (docs/spec/112-protocols.md): the TLA+ projection of one protocol
// declaration, from the parsed source alone.
func protocolCommand(args []string, stdout, stderr io.Writer) int {
	flags := flag.NewFlagSet("oak protocol", flag.ContinueOnError)
	flags.SetOutput(stderr)
	tla := flags.String("tla", "", "protocol name to render as a TLA+ module")
	output := flags.String("o", "", "write the module here instead of standard output")
	if err := flags.Parse(args); err != nil {
		return 2
	}
	if *tla == "" || flags.NArg() != 1 {
		fmt.Fprintln(stderr, "usage: oak protocol -tla Name [-o out.tla] file.oak")
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
