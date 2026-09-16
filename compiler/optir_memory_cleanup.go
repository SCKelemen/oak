package compiler

import (
	"fmt"
	"reflect"

	"github.com/SCKelemen/oak/optir"
)

// OptIRMemoryCleanup records one bounded scalar cleanup after memory
// forwarding. SCCP consumes ForwardedLoads, and GVN/DCE consumes SCCPSimplified.
// Projection and MemorySSA belong to CFG, including any removed control paths.
type OptIRMemoryCleanup struct {
	Constants      optir.SCCPResult
	SCCPSimplified optir.CFG
	SCCPRewrite    optir.SCCPRewriteReport
	CFG            optir.CFG
	Simplification optir.GVNDCEReport
	Projection     optir.CheckedMemoryProjection
	MemorySSA      optir.RegionMemorySSA
}

func (cleanup OptIRMemoryCleanup) Changes() int {
	return cleanup.SCCPRewrite.Changes() + cleanup.Simplification.Changes()
}

func cleanupOptIRMemory(cfg optir.CFG, authority optir.CheckedMemoryAuthority) (OptIRMemoryCleanup, error) {
	// Authenticate the input before a rewrite can remove any access or call.
	if _, err := optir.ProjectCheckedMemory(cfg, authority); err != nil {
		return OptIRMemoryCleanup{}, err
	}
	constants, err := optir.AnalyzeSCCP(cfg)
	if err != nil {
		return OptIRMemoryCleanup{}, err
	}
	sccp, rewrite, err := optir.SimplifyWithSCCP(cfg, constants)
	if err != nil {
		return OptIRMemoryCleanup{}, err
	}
	result, simplification, err := optir.SimplifyGVNDCE(sccp)
	if err != nil {
		return OptIRMemoryCleanup{}, err
	}
	projection, err := optir.ProjectCheckedMemory(result, authority)
	if err != nil {
		return OptIRMemoryCleanup{}, err
	}
	if err := optir.VerifyCheckedMemoryProjection(result, authority, projection); err != nil {
		return OptIRMemoryCleanup{}, err
	}
	memorySSA, err := optir.AnalyzeRegionMemorySSA(result, projection.Metadata)
	if err != nil {
		return OptIRMemoryCleanup{}, err
	}
	if err := optir.VerifyRegionMemorySSA(result, projection.Metadata, memorySSA); err != nil {
		return OptIRMemoryCleanup{}, err
	}
	return OptIRMemoryCleanup{
		Constants: constants, SCCPSimplified: sccp, SCCPRewrite: rewrite,
		CFG: result, Simplification: simplification, Projection: projection, MemorySSA: memorySSA,
	}, nil
}

func verifyOptIRMemoryCleanup(cfg optir.CFG, authority optir.CheckedMemoryAuthority, cleanup OptIRMemoryCleanup) error {
	expected, err := cleanupOptIRMemory(cfg, authority)
	if err != nil {
		return err
	}
	if !reflect.DeepEqual(expected, cleanup) {
		return fmt.Errorf("compiler: post-memory cleanup does not match its exact input and checked authority")
	}
	return nil
}
