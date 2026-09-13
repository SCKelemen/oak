package compiler

import (
	"fmt"
	"reflect"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/stdlib"
)

// CodeLiteralsShape reports a literals declaration that does not describe a
// scannable set (docs/spec/113-literals.md section 1): no literal, a
// literal shorter than the three bytes the prefilter classifies, a
// duplicate, or a projected name the program already declares.
const CodeLiteralsShape = "OAK-M0304"

// literalsKernelPrefix prefixes the standard library kernel's functions when
// the projection clones them into a program, so a program with a literals
// declaration is self-contained and the names cannot meet a user's.
const literalsKernelPrefix = "literals_teddy_"

// lowerLiterals replaces every literals declaration with its projection
// (docs/spec/113-literals.md section 2): the literal bytes, their starts,
// and the six nibble tables of the Teddy prefilter computed here from the
// declaration, plus `name_count`, `name_find`, and `name_which` over the
// standard library's kernel (stdlib/literals.oak), whose functions are
// cloned once into the program under literalsKernelPrefix. Oak.Teddy
// proves the tables sound for the kernel's verification.
func lowerLiterals(tree *SyntaxTree) error {
	program := tree.Root
	var diags []*diagnostic.Diagnostic
	report := func(code string, node ast.Node, format string, args ...interface{}) {
		diags = append(diags, diagnostic.NewDiagnosticFromNodeWithCode(node, "compiler", code, modules.DemangleText(fmt.Sprintf(format, args...))))
	}
	declared := map[string]bool{}
	found := false
	for _, stmt := range program.Statements {
		if name := declarationName(stmt); name != "" {
			declared[name] = true
		}
		if _, isLiterals := stmt.(*ast.LiteralsDeclaration); isLiterals {
			found = true
		}
	}
	if !found {
		return nil
	}
	var out []ast.Statement
	var kernelContext string
	for _, stmt := range program.Statements {
		decl, isLiterals := stmt.(*ast.LiteralsDeclaration)
		if !isLiterals {
			out = append(out, stmt)
			continue
		}
		if kernelContext == "" && decl.Name != nil {
			kernelContext = decl.Name.Token.SemanticContext
		}
		projected, ok := projectLiterals(decl, declared, report)
		if ok {
			out = append(out, projected...)
		}
	}
	if len(diags) == 0 {
		kernel, err := literalsKernel(kernelContext)
		if err != nil {
			return err
		}
		for _, stmt := range kernel {
			if name := declarationName(stmt); declared[name] {
				report(CodeLiteralsShape, program, "the literals kernel declares %s, which the program already declares", name)
			}
		}
		out = append(out, kernel...)
	}
	if len(diags) != 0 {
		return &DiagnosticError{Phase: "literals", Diagnostics: diags}
	}
	program.Statements = out
	return nil
}

// literalsTables computes the six nibble tables (stdlib/literals.oak
// `build`) for the literal set: low and high nibble of bytes 0, 1, 2 of
// every literal, bucket j % 8. Every literal has at least three bytes.
func literalsTables(lits []string) [96]byte {
	var tables [96]byte
	for j, lit := range lits {
		bit := byte(1) << uint(j%8)
		for k := 0; k < 3; k++ {
			c := lit[k]
			tables[32*k+int(c&15)] |= bit
			tables[32*k+16+int(c>>4)] |= bit
		}
	}
	return tables
}

// projectLiterals checks one declaration and generates its projection as
// Oak source, parsed and stamped with the declaration's context.
func projectLiterals(decl *ast.LiteralsDeclaration, declared map[string]bool, report func(code string, node ast.Node, format string, args ...interface{})) ([]ast.Statement, bool) {
	if decl.Name == nil {
		return nil, false
	}
	name := decl.Name.Value
	if len(decl.Literals) == 0 {
		report(CodeLiteralsShape, decl.Name, "literals %s declares no literal", name)
		return nil, false
	}
	ok := true
	seen := map[string]bool{}
	var lits []string
	for _, lit := range decl.Literals {
		if len(lit.Value) < 3 {
			report(CodeLiteralsShape, lit, "literals %s: %q is shorter than three bytes, the prefix the scanner classifies", name, lit.Value)
			ok = false
		}
		if seen[lit.Value] {
			report(CodeLiteralsShape, lit, "literals %s: %q is declared twice", name, lit.Value)
			ok = false
		}
		seen[lit.Value] = true
		lits = append(lits, lit.Value)
	}
	if !ok {
		return nil, false
	}
	prefix := snakeCase(name)
	for _, generated := range []string{prefix + "_literal_bytes", prefix + "_literal_starts", prefix + "_literal_tables", prefix + "_count", prefix + "_find", prefix + "_which", prefix + "_match", name + "Match"} {
		if declared[generated] {
			report(CodeLiteralsShape, decl.Name, "literals %s projects %s, which the program already declares", name, generated)
			ok = false
		}
	}
	if !ok {
		return nil, false
	}
	var patterns []byte
	starts := []int{0}
	for _, lit := range lits {
		patterns = append(patterns, lit...)
		starts = append(starts, len(patterns))
	}
	tables := literalsTables(lits)
	var src strings.Builder
	pub := ""
	if decl.Exported {
		pub = "pub "
	}
	write := func(format string, args ...interface{}) { src.WriteString(fmt.Sprintf(format, args...)) }
	write("%s_literal_bytes: [%d]u8 = [", prefix, len(patterns))
	for i, b := range patterns {
		if i > 0 {
			write(", ")
		}
		write("u8(%d)", b)
	}
	write("]\n%s_literal_starts: [%d]u32 = [", prefix, len(starts))
	for i, s := range starts {
		if i > 0 {
			write(", ")
		}
		write("u32(%d)", s)
	}
	write("]\n%s_literal_tables: [96]u8 = [", prefix)
	for i, b := range tables {
		if i > 0 {
			write(", ")
		}
		write("u8(%d)", b)
	}
	write("]\n")
	set := fmt.Sprintf("view(&%s_literal_bytes), view(&%s_literal_starts), u32(%d)", prefix, prefix, len(lits))
	write("%s%s_count: (bytes: []u8): u32 = %scount(bytes, %s, view(&%s_literal_tables))\n", pub, prefix, literalsKernelPrefix, set, prefix)
	write("%s%s_find: (bytes: []u8, start: u32): u32 = %sfind_from(bytes, start, %s, view(&%s_literal_tables))\n", pub, prefix, literalsKernelPrefix, set, prefix)
	write("%s%s_which: (bytes: []u8, pos: u32): u32 = %swhich_at(bytes, pos, %s)\n", pub, prefix, literalsKernelPrefix, set)
	// name_match: the first occurrence at or after start as one record —
	// its position (len(bytes) when none) and the literal's index (the
	// number of literals when none).
	write("%s%sMatch: type = struct {\n  at: u32\n  which: u32\n}\n", pub, name)
	write("%s%s_match: (bytes: []u8, start: u32): %sMatch {\n  at: u32 = %s_find(bytes, start)\n  %sMatch { at: at, which: at < len(bytes) ? %s_which(bytes, at) | u32(%d) }\n}\n", pub, prefix, name, prefix, name, prefix, len(lits))
	statements, err := parseGeneratedOak(src.String(), helperContext(decl.Name.Token.SemanticContext, name+"Literals"))
	if err != nil {
		report(CodeLiteralsShape, decl.Name, "literals %s: %v", name, err)
		return nil, false
	}
	return statements, true
}

// literalsKernel parses the standard library's literals package and returns
// its functions renamed under literalsKernelPrefix, unexported, stamped with
// the given context.
func literalsKernel(context string) ([]ast.Statement, error) {
	source, ok := stdlib.Packages["literals"]
	if !ok {
		return nil, fmt.Errorf("compiler: standard library package literals is missing")
	}
	statements, err := parseGeneratedOak(source, helperContext(context, "LiteralsKernel"))
	if err != nil {
		return nil, fmt.Errorf("compiler: literals kernel: %w", err)
	}
	var functions []ast.Statement
	var names []string
	for _, stmt := range statements {
		fn, isFunction := stmt.(*ast.FunctionStatement)
		if !isFunction || fn.Name == nil {
			continue
		}
		fn.Exported = false
		names = append(names, fn.Name.Value)
		functions = append(functions, fn)
	}
	for _, stmt := range functions {
		for _, name := range names {
			renameIdentifier(stmt, name, literalsKernelPrefix+name)
		}
	}
	return functions, nil
}

// parseGeneratedOak parses compiler-generated Oak source and stamps every
// token with the context, so scoping and diagnostics attribute it to the
// declaration it was generated for.
func parseGeneratedOak(src, context string) ([]ast.Statement, error) {
	p := parser.New(layout.New(scanner.New(src)))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		return nil, fmt.Errorf("generated source does not parse: %v", errs[0])
	}
	stampSemanticContext(reflect.ValueOf(program), context)
	return program.Statements, nil
}
