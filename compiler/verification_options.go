package compiler

import (
	"os"
	"path/filepath"

	"github.com/SCKelemen/oak/asm"
)

// verificationRun is owned by one check invocation, never by the reusable
// Compilation. Both cache operations and every verifier entry consume it.
// Its zero value is an explicit default verifier with caching disabled, useful
// for private helpers; helpers must never acquire ambient options themselves.
type verificationRun struct {
	options  asm.VerificationOptions
	cacheDir string
}

// captureVerificationRun is the only compiler acquisition boundary. Separate
// environment reads are not an atomic transaction with concurrent os.Setenv;
// concurrent callers needing distinct settings must use explicit options.
func (comp Compilation) captureVerificationRun() verificationRun {
	options := comp.verificationOptions
	if !comp.verificationOptionsSupplied {
		options = asm.NewVerificationOptions(os.Getenv("OAK_VERIFY_OFF"), os.Getenv("OAK_VERIFY_BUDGET"), os.Getenv("OAK_VERIFY_ONLY"))
	}
	return newVerificationRun(options, os.Getenv("OAK_VERIFY_CACHE"), comp.options.VerifyFresh)
}

func newVerificationRun(options asm.VerificationOptions, cacheSetting string, fresh bool) verificationRun {
	run := verificationRun{options: options}
	if cacheSetting != "0" && !fresh && !options.SelectionActive() {
		run.cacheDir = filepath.Join(os.TempDir(), "oak-verify-cache")
	}
	return run
}
