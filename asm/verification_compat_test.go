package asm

// Legacy private test entry points deliberately use explicit default options.
// Production uses session receivers, so a missed propagation edge cannot silently
// capture ambient configuration or drop an explicit session.
import (
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/typechecker"
	"os"
)

func verifyChunk(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression, chunk int) (result Verdict) {
	return (&verificationSession{}).verifyChunk(fn, sig, oakBody, chunk)
}

func verifyChunkJoining(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression, chunk int, joins bool) (Verdict, *pathExecutor) {
	return (&verificationSession{}).verifyChunkJoining(fn, sig, oakBody, chunk, joins)
}

func verifyExecution(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression, chunk int, asmTerm *term, exec *pathExecutor, reason string, ok bool) Verdict {
	return (&verificationSession{}).verifyExecution(fn, sig, oakBody, chunk, asmTerm, exec, reason, ok)
}

func verifyExecutionWithApplications(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression, chunk int, asmTerm *term, exec *pathExecutor, reason string, ok, expandCalls bool) Verdict {
	return (&verificationSession{}).verifyExecutionWithApplications(fn, sig, oakBody, chunk, asmTerm, exec, reason, ok, expandCalls)
}

func decideEqual(fn *Function, lowering *oakLowering, asmTerm, oakTerm *term, width int, note string) Verdict {
	return (&verificationSession{}).decideEqual(fn, lowering, asmTerm, oakTerm, width, note)
}

func decideCells(fn *Function, lowering *oakLowering, exec *pathExecutor, result *Verdict) Verdict {
	return (&verificationSession{}).decideCells(fn, lowering, exec, result)
}

func decideEffects(fn *Function, lowering *oakLowering, exec *pathExecutor, result *Verdict) Verdict {
	return (&verificationSession{}).decideEffects(fn, lowering, exec, result)
}

func decideSpans(fn *Function, lowering *oakLowering, exec *pathExecutor, result *Verdict) Verdict {
	return (&verificationSession{}).decideSpans(fn, lowering, exec, result)
}

func verifyTrapDomain(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression, exec *pathExecutor, result Verdict) Verdict {
	return (&verificationSession{}).verifyTrapDomain(fn, sig, oakBody, exec, result)
}

func verifyVectorResult(fn *Function, sig *ast.FunctionStatement, oakBody ast.Expression, shape typechecker.SimdShape) Verdict {
	return (&verificationSession{}).verifyVectorResult(fn, sig, oakBody, shape)
}

// Existing escalation parsing test exercises the public compatibility adapter's
// environment choice without putting another ambient read into production.
func escalatedNodeBudget() int {
	return NewVerificationOptions("", os.Getenv("OAK_VERIFY_BUDGET"), "").escalationBudget()
}
