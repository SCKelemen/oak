package codegen

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/typechecker"
)

// GenerateHeader emits the C header of a program's exported surface
// (docs/spec/92-ffi.md section 2.6, "Exported functions"): the primitive
// typedefs the generated C uses, every declared type in dependency order with
// its cc-ratified layout assertions (records, tagged unions, array wrappers,
// views and spans), and a prototype for each `pub` function. A C consumer
// includes the header and links against the generated C; it never has to
// mirror a struct by hand.
//
// Types are emitted by the same emitters as the C file, so the header and
// the definitions the code was compiled against cannot disagree. Private
// functions, helpers, globals, and bodies are not part of the surface.
func (cg *CodeGenerator) GenerateHeader(program *ast.Program, tc *typechecker.TypeChecker) (string, error) {
	cg.typeChecker = tc
	guard := headerGuard(cg.packageName)
	cg.write(fmt.Sprintf("/* Generated C header from Oak: package %s. Include it from C; link the generated C. */\n", cg.packageName))
	cg.write(fmt.Sprintf("#ifndef %s\n#define %s\n\n", guard, guard))

	cg.emitHeader(program)
	cg.emitBoolADT()
	cg.emitComparisonADT()

	for _, stmt := range program.Statements {
		if adt, ok := stmt.(*ast.ADTType); ok {
			cg.adtTypes[adt.Name.Value] = adt
		}
	}
	cg.emitTypesInDependencyOrder(program, tc)
	cg.preEmitContainerTypes(program)

	// The root package's pub functions are exported implicitly under
	// `oak_<name>`, in declaration order. A dependency's pub functions carry
	// the elaborator's internal names and are not part of the C surface;
	// they reach the header only through an explicit `export("symbol")`
	// marker (docs/spec/92-ffi.md section 2.9), listed after the implicit
	// exports sorted by symbol, each with its package in a comment.
	cg.write("/* exported functions */\n")
	var explicit []*ast.FunctionStatement
	for _, stmt := range program.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil || !fn.Exported || fn.Receiver != nil || fn.ExternSymbol != "" || len(fn.TypeParams) != 0 {
			continue
		}
		if fn.ExportSymbol != "" {
			explicit = append(explicit, fn)
			continue
		}
		if _, _, mangled := modules.Demangle(fn.Name.Value); mangled {
			continue
		}
		cg.write(fmt.Sprintf("%s %s( %s );\n", cg.parseTypeExpression(fn.ReturnType), cg.cFunctionName(fn.Name.Value), cg.cParameterList(fn)))
	}
	sort.SliceStable(explicit, func(i, j int) bool { return explicit[i].ExportSymbol < explicit[j].ExportSymbol })
	if len(explicit) > 0 {
		cg.write("/* explicit C ABI exports (export(\"symbol\") markers) */\n")
	}
	for _, fn := range explicit {
		path, name, mangled := modules.Demangle(fn.Name.Value)
		if !mangled {
			path, name = "the root package", fn.Name.Value
		}
		cg.write(fmt.Sprintf("/* %s: %s */\n", path, name))
		cg.write(fmt.Sprintf("%s %s( %s );\n", cg.parseTypeExpression(fn.ReturnType), fn.ExportSymbol, cg.cParameterList(fn)))
	}
	cg.write(fmt.Sprintf("\n#endif /* %s */\n", guard))
	output := cg.output.String()
	if strings.Contains(output, "OAK_UNSUPPORTED") {
		return output, fmt.Errorf("codegen: the exported surface names a type without a C representation")
	}
	return output, nil
}

// headerGuard is the include guard: OAK_<PACKAGE>_H with every character
// outside the identifier alphabet spelled as an underscore.
func headerGuard(packageName string) string {
	var guard strings.Builder
	guard.WriteString("OAK_")
	for _, r := range strings.ToUpper(packageName) {
		if (r >= 'A' && r <= 'Z') || (r >= '0' && r <= '9') {
			guard.WriteRune(r)
		} else {
			guard.WriteByte('_')
		}
	}
	guard.WriteString("_H")
	return guard.String()
}
