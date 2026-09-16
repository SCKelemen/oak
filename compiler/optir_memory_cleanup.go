package compiler

import (
	"fmt"
	"reflect"

	"github.com/SCKelemen/oak/optir"
)

// OptIRMemoryCleanup records one bounded cleanup after memory forwarding:
// SCCP -> phi/GVN/DCE -> memory DSE -> pure DCE. Each intermediate CFG belongs
// to the preceding report. Projection and MemorySSA belong to the final CFG.
type OptIRMemoryCleanup struct {
	Constants            optir.SCCPResult
	SCCPSimplified       optir.CFG
	SCCPRewrite          optir.SCCPRewriteReport
	ScalarCFG            optir.CFG
	Simplification       optir.GVNDCEReport
	DeadStores           optir.CFG
	DeadStoreElimination optir.DeadStoreEliminationReport
	CFG                  optir.CFG
	DCE                  optir.DCEReport
	Projection           optir.CheckedMemoryProjection
	MemorySSA            optir.RegionMemorySSA
}

func (cleanup OptIRMemoryCleanup) Changes() int {
	return cleanup.SCCPRewrite.Changes() + cleanup.Simplification.Changes() +
		len(cleanup.DeadStoreElimination.Removed) + cleanup.DCE.EliminatedOperations
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
	scalar, simplification, err := optir.SimplifyGVNDCE(sccp)
	if err != nil {
		return OptIRMemoryCleanup{}, err
	}
	// Removed reads and control paths can make formerly observed stores dead.
	// Rebuild the evidence: pre-forwarding liveness cannot authorize this DSE.
	scalarProjection, scalarSSA, err := checkedOptIRMemoryState(scalar, authority)
	if err != nil {
		return OptIRMemoryCleanup{}, err
	}
	liveness, err := optir.AnalyzeMemoryDefinitionLiveness(scalar, scalarProjection.Metadata, scalarSSA, scalarProjection.Observability)
	if err != nil {
		return OptIRMemoryCleanup{}, err
	}
	deadStores, metadata, stores, err := optir.EliminateDeadRegionStores(scalar, scalarProjection.Metadata, scalarSSA, scalarProjection.Observability, liveness)
	if err != nil {
		return OptIRMemoryCleanup{}, err
	}
	if err := optir.VerifyDeadStoreElimination(scalar, scalarProjection.Metadata, scalarSSA, scalarProjection.Observability, liveness, deadStores, metadata, stores); err != nil {
		return OptIRMemoryCleanup{}, err
	}
	storeProjection, err := optir.ProjectCheckedMemory(deadStores, authority)
	if err != nil {
		return OptIRMemoryCleanup{}, err
	}
	if !reflect.DeepEqual(storeProjection.Metadata, metadata) || !reflect.DeepEqual(storeProjection.Observability, scalarProjection.Observability) {
		return OptIRMemoryCleanup{}, fmt.Errorf("compiler: cleanup DSE changed checked memory metadata or observability")
	}
	// Only the existing closed, total, pure vocabulary may lose its now-unused
	// producers. Calls and other effects remain even when their results are dead.
	result, dce, err := optir.EliminateDeadCode(deadStores)
	if err != nil {
		return OptIRMemoryCleanup{}, err
	}
	projection, memorySSA, err := checkedOptIRMemoryState(result, authority)
	if err != nil {
		return OptIRMemoryCleanup{}, err
	}
	return OptIRMemoryCleanup{
		Constants: constants, SCCPSimplified: sccp, SCCPRewrite: rewrite,
		ScalarCFG: scalar, Simplification: simplification,
		DeadStores: deadStores, DeadStoreElimination: stores,
		CFG: result, DCE: dce, Projection: projection, MemorySSA: memorySSA,
	}, nil
}

func checkedOptIRMemoryState(cfg optir.CFG, authority optir.CheckedMemoryAuthority) (optir.CheckedMemoryProjection, optir.RegionMemorySSA, error) {
	projection, err := optir.ProjectCheckedMemory(cfg, authority)
	if err == nil {
		err = optir.VerifyCheckedMemoryProjection(cfg, authority, projection)
	}
	if err != nil {
		return optir.CheckedMemoryProjection{}, optir.RegionMemorySSA{}, err
	}
	memorySSA, err := optir.AnalyzeRegionMemorySSA(cfg, projection.Metadata)
	if err == nil {
		err = optir.VerifyRegionMemorySSA(cfg, projection.Metadata, memorySSA)
	}
	return projection, memorySSA, err
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
