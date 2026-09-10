package codegen

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
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

	cg.write("/* exported functions */\n")
	for _, stmt := range program.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil || !fn.Exported || fn.Receiver != nil || fn.ExternSymbol != "" || len(fn.TypeParams) != 0 {
			continue
		}
		cg.write(fmt.Sprintf("%s %s( ", cg.parseTypeExpression(fn.ReturnType), cg.cFunctionName(fn.Name.Value)))
		if len(fn.Parameters) == 0 {
			cg.write("void")
		}
		for i, param := range fn.Parameters {
			if param.Variadic {
				cg.write(fmt.Sprintf("%s %s", cg.emitViewType(cg.parseTypeExpression(param.Type)), cIdent(param.Name.Value)))
			} else {
				cg.write(cg.cParameter(param.Type, param.Name.Value))
			}
			if i < len(fn.Parameters)-1 {
				cg.write(", ")
			}
		}
		cg.write(" );\n")
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
