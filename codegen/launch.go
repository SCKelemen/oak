package codegen

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
)

// test_launch(kernel, grid, args...) (docs/spec/110-testing.md, "Launch
// targets"): the kernel runs over the grid on the host — the C realization,
// one call per position in order — and the launch is recorded through the
// test host: the kernel's name and grid, every argument's bytes before the
// run (views, spans, scalars; a record parameter's fields as name.field,
// as the launch descriptor spells them), and every span's bytes after. The
// runner replays the record on the GPU and compares.

// launchArg is one recorded buffer: the descriptor's name and kind, the
// element type, and the C expression of the value.
type launchArg struct {
	name, kind, element, expr string
}

func (cg *CodeGenerator) emitTestLaunch(call *ast.InvocationExpression, tc *typechecker.TypeChecker) {
	kernelIdent, ok := call.Function.(*ast.Identifier)
	_ = kernelIdent
	if len(call.Arguments) < 2 {
		cg.write("  OAK_UNSUPPORTED_LAUNCH;\n")
		return
	}
	kernelName, ok := call.Arguments[0].(*ast.Identifier)
	if !ok {
		cg.write("  OAK_UNSUPPORTED_LAUNCH;\n")
		return
	}
	fn := cg.programFunctions[kernelName.Value]
	if fn == nil {
		cg.write("  OAK_UNSUPPORTED_LAUNCH_NOFN;\n")
		return
	}
	if !fn.Kernel && !tc.IsKernel(kernelName.Value) {
		cg.write("  OAK_UNSUPPORTED_LAUNCH_NOTKERNEL;\n")
		return
	}
	if len(fn.Parameters) != len(call.Arguments)-1 {
		cg.write(fmt.Sprintf("  OAK_UNSUPPORTED_LAUNCH_ARITY_%d_%d;\n", len(fn.Parameters), len(call.Arguments)))
		return
	}
	cg.launchCounter++
	prefix := fmt.Sprintf("oak_la%d_", cg.launchCounter)
	cg.write("  {\n")
	cg.write(fmt.Sprintf("    u32 %sgrid = ", prefix))
	cg.emitExpressionFragment(call.Arguments[1], tc)
	cg.output.WriteString(";\n")
	var args []launchArg
	var callArgs []string
	for i, param := range fn.Parameters[1:] {
		temp := fmt.Sprintf("%sa%d", prefix, i)
		cg.write(fmt.Sprintf("    %s %s = ", cg.parseTypeExpression(param.Type), temp))
		cg.emitExpressionFragment(call.Arguments[i+2], tc)
		cg.output.WriteString(";\n")
		callArgs = append(callArgs, temp)
		args = append(args, cg.launchArgs(param.Name.Value, param.Type, temp)...)
	}
	cg.write(fmt.Sprintf("    oak_test_host_launch_begin(%q, %sgrid);\n", kernelName.Value, prefix))
	for _, a := range args {
		cg.write(fmt.Sprintf("    oak_test_host_launch_arg(%q, %q, %q, %s);\n", a.name, a.kind, a.element, a.expr))
	}
	cg.write(fmt.Sprintf("    for (u32 %sg = 0; %sg < %sgrid; %sg++) { %s(%sg", prefix, prefix, prefix, prefix, cg.cFunctionName(kernelName.Value), prefix))
	for _, arg := range callArgs {
		cg.output.WriteString(", " + arg)
	}
	cg.output.WriteString("); }\n")
	for _, a := range args {
		if a.kind == "span" {
			cg.write(fmt.Sprintf("    oak_test_host_launch_out(%q, %s);\n", a.name, a.expr))
		}
	}
	cg.write("    oak_test_host_launch_end();\n")
	cg.write("  }\n")
}

// launchArgs lists the recorded buffers of one parameter: a view or span
// is its base and byte length, a scalar its address and size, and a record
// its fields, each named name.field.
func (cg *CodeGenerator) launchArgs(name string, typeExpr ast.Expression, expr string) []launchArg {
	switch t := typeExpr.(type) {
	case *ast.IndexExpression:
		if !t.Dot {
			element, isIdent := t.Left.(*ast.Identifier)
			marker, isMarker := t.Index.(*ast.Identifier)
			if isIdent && isMarker && (marker.Value == "" || marker.Value == "*") {
				kind := "view"
				if marker.Value == "*" {
					kind = "span"
				}
				bytes := fmt.Sprintf("(const void *)( %s ).base, (u32)(( %s ).len * (u32)sizeof(*( %s ).base))", expr, expr, expr)
				return []launchArg{{name: name, kind: kind, element: element.Value, expr: bytes}}
			}
		}
	case *ast.Identifier:
		if adt, isADT := cg.adtTypes[t.Value]; isADT {
			if record, isRecord := recordDefinitionShape(adt); isRecord {
				var out []launchArg
				for _, field := range record.FieldOrder {
					out = append(out, cg.launchArgs(name+"."+field.Name, field.Value, expr+"."+cIdent(field.Name))...)
				}
				return out
			}
		}
		return []launchArg{{name: name, kind: "scalar", element: t.Value, expr: fmt.Sprintf("(const void *)&%s, (u32)sizeof(%s)", expr, expr)}}
	}
	return nil
}
