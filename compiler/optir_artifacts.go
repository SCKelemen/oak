package compiler

import (
	"context"
	"fmt"
	"reflect"

	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/optir"
)

const (
	optIRAnalysisWorkers          = 3
	optIRSCCPRevision             = "oak.optir.sccp.v1"
	optIRSCCPRewriteRevision      = "oak.optir.sccp-rewrite.v1"
	optIRSCCPCFGRevision          = "oak.optir.sccp-cfg.v1"
	optIRLoopStructureRevision    = "oak.optir.loop-structure.v1"
	optIRLoopsRevision            = "oak.optir.loops.v2"
	optIRGVNDCERevision           = "oak.optir.gvn-dce.v3"
	optIRCleanupCFGRevision       = "oak.optir.cleanup-cfg.v4"
	optIRPreservationRevision     = "oak.optir.preservation.v1"
	optIRLICMRevision             = "oak.optir.licm.v1"
	optIRFinalCFGRevision         = "oak.optir.final-cfg.v1"
	optIRMemoryProjectionRevision = "oak.optir.checked-memory-projection.v4"
	optIRMemorySSARevision        = "oak.optir.region-memory-ssa.v5"
	optIRMemoryLivenessRevision   = "oak.optir.memory-liveness.v2"
	optIRMemoryEvidenceRevision   = "oak.optir.memory-evidence.v1"
	optIRDSERevision              = "oak.optir.dead-store-elimination.v4"
	optIRRegionLoadRevision       = "oak.optir.region-load-forwarding.v6"
)

type optIRSCCPRewriteArtifact struct {
	CFG    optir.CFG
	Report optir.SCCPRewriteReport
}

type optIRGVNDCEArtifact struct {
	CFG    optir.CFG
	Report optir.GVNDCEReport
}

type optIRLICMArtifact struct {
	CFG    optir.CFG
	Report optir.LICMReport
}

type optIRMemoryEvidenceArtifact struct {
	SSA      optir.RegionMemorySSA
	Liveness optir.MemoryDefinitionLiveness
}

type optIRDSEArtifact struct {
	CFG      optir.CFG
	Metadata optir.RegionMemoryMetadata
	Report   optir.DeadStoreEliminationReport
}

type optIRRegionLoadArtifact struct {
	InputProjection optir.CheckedMemoryProjection
	InputSSA        optir.RegionMemorySSA
	CFG             optir.CFG
	Metadata        optir.RegionMemoryMetadata
	Projection      optir.CheckedMemoryProjection
	SSA             optir.RegionMemorySSA
	Report          optir.RegionLoadForwardingReport
}

type optIRArtifactKeys struct {
	cfgV0            opt.ArtifactKey
	sccp             opt.ArtifactKey
	sccpRewrite      opt.ArtifactKey
	cfgV1            opt.ArtifactKey
	loopStructureV1  opt.ArtifactKey
	loopsV1          opt.ArtifactKey
	cleanup          opt.ArtifactKey
	cfgV2            opt.ArtifactKey
	preservation     opt.ArtifactKey
	loopsV2          opt.ArtifactKey
	licm             opt.ArtifactKey
	cfgV3            opt.ArtifactKey
	memoryAuthority  opt.ArtifactKey
	memoryProjection opt.ArtifactKey
	memorySSA        opt.ArtifactKey
	memoryLiveness   opt.ArtifactKey
	memoryEvidence   opt.ArtifactKey
	dse              opt.ArtifactKey
	regionLoads      opt.ArtifactKey
}

type optIRArtifactRefs struct {
	hasMemory        bool
	cfgV0            opt.ArtifactRef[optir.CFG]
	sccp             opt.ArtifactRef[optir.SCCPResult]
	sccpRewrite      opt.ArtifactRef[optIRSCCPRewriteArtifact]
	cfgV1            opt.ArtifactRef[optir.CFG]
	loopStructureV1  opt.ArtifactRef[optir.LoopStructure]
	loopsV1          opt.ArtifactRef[optir.LoopAnalysis]
	cleanup          opt.ArtifactRef[optIRGVNDCEArtifact]
	cfgV2            opt.ArtifactRef[optir.CFG]
	preservation     opt.ArtifactRef[optir.PreservationCertificate]
	loopsV2          opt.ArtifactRef[optir.LoopAnalysis]
	licm             opt.ArtifactRef[optIRLICMArtifact]
	cfgV3            opt.ArtifactRef[optir.CFG]
	memoryAuthority  opt.ArtifactRef[optir.CheckedMemoryAuthority]
	memoryProjection opt.ArtifactRef[optir.CheckedMemoryProjection]
	memorySSA        opt.ArtifactRef[optir.RegionMemorySSA]
	memoryLiveness   opt.ArtifactRef[optir.MemoryDefinitionLiveness]
	memoryEvidence   opt.ArtifactRef[optIRMemoryEvidenceArtifact]
	dse              opt.ArtifactRef[optIRDSEArtifact]
	regionLoads      opt.ArtifactRef[optIRRegionLoadArtifact]
}

func (references optIRArtifactRefs) keys() optIRArtifactKeys {
	return optIRArtifactKeys{
		cfgV0:            references.cfgV0.Key(),
		sccp:             references.sccp.Key(),
		sccpRewrite:      references.sccpRewrite.Key(),
		cfgV1:            references.cfgV1.Key(),
		loopStructureV1:  references.loopStructureV1.Key(),
		loopsV1:          references.loopsV1.Key(),
		cleanup:          references.cleanup.Key(),
		cfgV2:            references.cfgV2.Key(),
		preservation:     references.preservation.Key(),
		loopsV2:          references.loopsV2.Key(),
		licm:             references.licm.Key(),
		cfgV3:            references.cfgV3.Key(),
		memoryAuthority:  references.memoryAuthority.Key(),
		memoryProjection: references.memoryProjection.Key(),
		memorySSA:        references.memorySSA.Key(),
		memoryLiveness:   references.memoryLiveness.Key(),
		memoryEvidence:   references.memoryEvidence.Key(),
		dse:              references.dse.Key(),
		regionLoads:      references.regionLoads.Key(),
	}
}

type optIRAnalysisArtifacts struct {
	hasMemory            bool
	constants            optir.SCCPResult
	sccpSimplified       optir.CFG
	sccpSimplification   optir.SCCPRewriteReport
	loops                optir.LoopAnalysis
	simplified           optir.CFG
	simplification       optir.GVNDCEReport
	loopInvariant        optir.CFG
	loopMotion           optir.LICMReport
	memoryProjection     optir.CheckedMemoryProjection
	memorySSA            optir.RegionMemorySSA
	memoryLiveness       optir.MemoryDefinitionLiveness
	deadStores           optir.CFG
	deadStoreMetadata    optir.RegionMemoryMetadata
	deadStoreElimination optir.DeadStoreEliminationReport
	postDSEProjection    optir.CheckedMemoryProjection
	postDSEMemorySSA     optir.RegionMemorySSA
	regionLoads          optir.CFG
	regionLoadMetadata   optir.RegionMemoryMetadata
	regionLoadProjection optir.CheckedMemoryProjection
	regionLoadMemorySSA  optir.RegionMemorySSA
	regionLoadForwarding optir.RegionLoadForwardingReport
	run                  opt.ArtifactRun
	keys                 optIRArtifactKeys
}

func runOptIRAnalysisGraphWithMemory(cfg optir.CFG, memoryAuthority optir.CheckedMemoryAuthority) (optIRAnalysisArtifacts, error) {
	graph, references, err := newOptIRAnalysisGraph(cfg, memoryAuthority)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	targets := []opt.ArtifactKey{references.sccp.Key(), references.sccpRewrite.Key(), references.loopsV1.Key(), references.cleanup.Key(), references.licm.Key()}
	if references.hasMemory {
		targets = append(targets, references.regionLoads.Key())
	}
	run, err := graph.RunParallel(context.Background(), nil, optIRAnalysisWorkers, targets...)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	constants, err := references.sccp.Value(run)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	sccpRewrite, err := references.sccpRewrite.Value(run)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	loops, err := references.loopsV1.Value(run)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	cleanup, err := references.cleanup.Value(run)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	licm, err := references.licm.Value(run)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	artifacts := optIRAnalysisArtifacts{
		hasMemory:          references.hasMemory,
		constants:          constants,
		sccpSimplified:     sccpRewrite.CFG,
		sccpSimplification: sccpRewrite.Report,
		loops:              loops,
		simplified:         cleanup.CFG,
		simplification:     cleanup.Report,
		loopInvariant:      licm.CFG,
		loopMotion:         licm.Report,
		run:                run,
		keys:               references.keys(),
	}
	if !references.hasMemory {
		return artifacts, nil
	}
	memoryProjection, err := references.memoryProjection.Value(run)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	memorySSA, err := references.memorySSA.Value(run)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	memoryLiveness, err := references.memoryLiveness.Value(run)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	dse, err := references.dse.Value(run)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	artifacts.memoryProjection = memoryProjection
	artifacts.memorySSA = memorySSA
	artifacts.memoryLiveness = memoryLiveness
	artifacts.deadStores = dse.CFG
	artifacts.deadStoreMetadata = dse.Metadata
	artifacts.deadStoreElimination = dse.Report
	regionLoads, err := references.regionLoads.Value(run)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	artifacts.postDSEProjection = regionLoads.InputProjection
	artifacts.postDSEMemorySSA = regionLoads.InputSSA
	artifacts.regionLoads = regionLoads.CFG
	artifacts.regionLoadMetadata = regionLoads.Metadata
	artifacts.regionLoadProjection = regionLoads.Projection
	artifacts.regionLoadMemorySSA = regionLoads.SSA
	artifacts.regionLoadForwarding = regionLoads.Report
	return artifacts, nil
}

func newOptIRAnalysisGraph(cfg optir.CFG, memoryAuthority optir.CheckedMemoryAuthority) (*opt.ArtifactGraph, optIRArtifactRefs, error) {
	fingerprint, err := optir.FingerprintCFG(cfg)
	if err != nil {
		return nil, optIRArtifactRefs{}, err
	}
	cfgV0, cfgV0Task := opt.RootArtifact(opt.ArtifactKey{Kind: opt.ArtifactIR, Name: "optir.cfg.v0", Version: fingerprint}, cfg)
	sccp, sccpTask := opt.DerivedArtifact1(opt.ArtifactAnalysis, "optir.sccp", optIRSCCPRevision, cfgV0,
		func(_ context.Context, input optir.CFG) (optir.SCCPResult, error) { return optir.AnalyzeSCCP(input) })
	sccpRewrite, sccpRewriteTask := opt.DerivedArtifact2(opt.ArtifactCandidate, "optir.sccp-rewrite", optIRSCCPRewriteRevision, cfgV0, sccp,
		func(_ context.Context, input optir.CFG, evidence optir.SCCPResult) (optIRSCCPRewriteArtifact, error) {
			result, report, err := optir.SimplifyWithSCCP(input, evidence)
			return optIRSCCPRewriteArtifact{CFG: result, Report: report}, err
		})
	cfgV1, cfgV1Task := opt.DerivedArtifact1(opt.ArtifactIR, "optir.cfg.v1", optIRSCCPCFGRevision, sccpRewrite,
		func(_ context.Context, result optIRSCCPRewriteArtifact) (optir.CFG, error) { return result.CFG, nil })
	loopStructureV1, loopStructureV1Task := opt.DerivedArtifact1(opt.ArtifactAnalysis, "optir.loop-structure.v1", optIRLoopStructureRevision, cfgV1,
		func(_ context.Context, input optir.CFG) (optir.LoopStructure, error) {
			return optir.AnalyzeLoopStructure(input)
		})
	loopsV1, loopsV1Task := opt.DerivedArtifact2(opt.ArtifactAnalysis, "optir.loops.v1", optIRLoopsRevision, cfgV1, loopStructureV1,
		func(_ context.Context, input optir.CFG, structure optir.LoopStructure) (optir.LoopAnalysis, error) {
			return optir.AnalyzeLoopsWithStructure(input, structure)
		})
	cleanup, cleanupTask := opt.DerivedArtifact1(opt.ArtifactCandidate, "optir.gvn-dce", optIRGVNDCERevision, cfgV1,
		func(_ context.Context, input optir.CFG) (optIRGVNDCEArtifact, error) {
			result, report, err := optir.SimplifyGVNDCE(input)
			return optIRGVNDCEArtifact{CFG: result, Report: report}, err
		})
	cfgV2, cfgV2Task := opt.DerivedArtifact1(opt.ArtifactIR, "optir.cfg.v2", optIRCleanupCFGRevision, cleanup,
		func(_ context.Context, result optIRGVNDCEArtifact) (optir.CFG, error) { return result.CFG, nil })
	preservation, preservationTask := opt.DerivedArtifact2(opt.ArtifactAdmission, "optir.gvn-dce.preservation", optIRPreservationRevision, cfgV1, cfgV2,
		func(_ context.Context, before, after optir.CFG) (optir.PreservationCertificate, error) {
			return optir.CheckCFGPreservation(
				cfgV1.Key(),
				before,
				cfgV2.Key(),
				after,
				optir.AspectCFGTopology,
				optir.AspectSSAIdentity,
				optir.AspectOperationSemantics,
				optir.AspectMemoryEffects,
				optir.AspectTypes,
				optir.AspectProofFacts,
				optir.AspectLayout,
			)
		})
	loopsV2, loopsV2Task := opt.DerivedArtifact3(opt.ArtifactAnalysis, "optir.loops.v2", optIRLoopsRevision, cfgV2, loopStructureV1, preservation,
		func(_ context.Context, input optir.CFG, structure optir.LoopStructure, certificate optir.PreservationCertificate) (optir.LoopAnalysis, error) {
			return optir.AnalyzeLoopsWithPreservedStructure(input, structure, certificate)
		})
	licm, licmTask := opt.DerivedArtifact2(opt.ArtifactCandidate, "optir.licm", optIRLICMRevision, cfgV2, loopsV2,
		func(_ context.Context, input optir.CFG, loops optir.LoopAnalysis) (optIRLICMArtifact, error) {
			result, report, err := optir.HoistLoopInvariantsWithAnalysis(input, loops)
			return optIRLICMArtifact{CFG: result, Report: report}, err
		})
	cfgV3, cfgV3Task := opt.DerivedArtifact1(opt.ArtifactIR, "optir.cfg.v3", optIRFinalCFGRevision, licm,
		func(_ context.Context, result optIRLICMArtifact) (optir.CFG, error) { return result.CFG, nil })

	references := optIRArtifactRefs{
		cfgV0:           cfgV0,
		sccp:            sccp,
		sccpRewrite:     sccpRewrite,
		cfgV1:           cfgV1,
		loopStructureV1: loopStructureV1,
		loopsV1:         loopsV1,
		cleanup:         cleanup,
		cfgV2:           cfgV2,
		preservation:    preservation,
		loopsV2:         loopsV2,
		licm:            licm,
		cfgV3:           cfgV3,
	}
	tasks := []opt.ArtifactTask{cfgV0Task, sccpTask, sccpRewriteTask, cfgV1Task, loopStructureV1Task, loopsV1Task, cleanupTask, cfgV2Task, preservationTask, loopsV2Task, licmTask, cfgV3Task}
	if memoryAuthority.HasMemoryEffects() {
		memoryAuthorityRef, memoryAuthorityTask := opt.RootArtifact(opt.ArtifactKey{
			Kind: opt.ArtifactChecked, Name: "optir.checked-memory", Version: memoryAuthority.Fingerprint(),
		}, memoryAuthority)
		memoryProjection, memoryProjectionTask := opt.DerivedArtifact2(opt.ArtifactAnalysis, "optir.checked-memory-projection", optIRMemoryProjectionRevision, cfgV3, memoryAuthorityRef,
			func(_ context.Context, input optir.CFG, authority optir.CheckedMemoryAuthority) (optir.CheckedMemoryProjection, error) {
				return optir.ProjectCheckedMemory(input, authority)
			})
		memorySSA, memorySSATask := opt.DerivedArtifact2(opt.ArtifactAnalysis, "optir.region-memory-ssa", optIRMemorySSARevision, cfgV3, memoryProjection,
			func(_ context.Context, input optir.CFG, projection optir.CheckedMemoryProjection) (optir.RegionMemorySSA, error) {
				return optir.AnalyzeRegionMemorySSA(input, projection.Metadata)
			})
		memoryLiveness, memoryLivenessTask := opt.DerivedArtifact3(opt.ArtifactAnalysis, "optir.memory-liveness", optIRMemoryLivenessRevision, cfgV3, memoryProjection, memorySSA,
			func(_ context.Context, input optir.CFG, projection optir.CheckedMemoryProjection, memory optir.RegionMemorySSA) (optir.MemoryDefinitionLiveness, error) {
				return optir.AnalyzeMemoryDefinitionLiveness(input, projection.Metadata, memory, projection.Observability)
			})
		memoryEvidence, memoryEvidenceTask := opt.DerivedArtifact2(opt.ArtifactAnalysis, "optir.memory-evidence", optIRMemoryEvidenceRevision, memorySSA, memoryLiveness,
			func(_ context.Context, memory optir.RegionMemorySSA, liveness optir.MemoryDefinitionLiveness) (optIRMemoryEvidenceArtifact, error) {
				return optIRMemoryEvidenceArtifact{SSA: memory, Liveness: liveness}, nil
			})
		dse, dseTask := opt.DerivedArtifact3(opt.ArtifactCandidate, "optir.dead-store-elimination", optIRDSERevision, cfgV3, memoryProjection, memoryEvidence,
			func(_ context.Context, input optir.CFG, projection optir.CheckedMemoryProjection, evidence optIRMemoryEvidenceArtifact) (optIRDSEArtifact, error) {
				result, metadata, report, err := optir.EliminateDeadRegionStores(input, projection.Metadata, evidence.SSA, projection.Observability, evidence.Liveness)
				if err == nil {
					err = optir.VerifyDeadStoreElimination(input, projection.Metadata, evidence.SSA, projection.Observability, evidence.Liveness, result, metadata, report)
				}
				return optIRDSEArtifact{CFG: result, Metadata: metadata, Report: report}, err
			})
		regionLoads, regionLoadsTask := opt.DerivedArtifact2(opt.ArtifactCandidate, "optir.region-load-forwarding", optIRRegionLoadRevision, dse, memoryAuthorityRef,
			func(_ context.Context, input optIRDSEArtifact, authority optir.CheckedMemoryAuthority) (optIRRegionLoadArtifact, error) {
				inputProjection, err := optir.ProjectCheckedMemory(input.CFG, authority)
				if err != nil {
					return optIRRegionLoadArtifact{}, err
				}
				if !reflect.DeepEqual(inputProjection.Metadata, input.Metadata) {
					return optIRRegionLoadArtifact{}, fmt.Errorf("compiler: post-DSE checked memory projection disagrees with rewritten metadata")
				}
				if err := optir.VerifyCheckedMemoryProjection(input.CFG, authority, inputProjection); err != nil {
					return optIRRegionLoadArtifact{}, err
				}
				inputSSA, err := optir.AnalyzeRegionMemorySSA(input.CFG, inputProjection.Metadata)
				if err != nil {
					return optIRRegionLoadArtifact{}, err
				}
				if err := optir.VerifyRegionMemorySSA(input.CFG, inputProjection.Metadata, inputSSA); err != nil {
					return optIRRegionLoadArtifact{}, err
				}
				result, metadata, report, err := optir.ForwardRegionLoads(input.CFG, inputProjection.Metadata, inputSSA)
				if err != nil {
					return optIRRegionLoadArtifact{}, err
				}
				if err := optir.VerifyRegionLoadForwarding(input.CFG, inputProjection.Metadata, inputSSA, result, metadata, report); err != nil {
					return optIRRegionLoadArtifact{}, err
				}
				projection, err := optir.ProjectCheckedMemory(result, authority)
				if err != nil {
					return optIRRegionLoadArtifact{}, err
				}
				if !reflect.DeepEqual(projection.Metadata, metadata) {
					return optIRRegionLoadArtifact{}, fmt.Errorf("compiler: post-forwarding checked memory projection disagrees with rewritten metadata")
				}
				if err := optir.VerifyCheckedMemoryProjection(result, authority, projection); err != nil {
					return optIRRegionLoadArtifact{}, err
				}
				memorySSA, err := optir.AnalyzeRegionMemorySSA(result, projection.Metadata)
				if err != nil {
					return optIRRegionLoadArtifact{}, err
				}
				if err := optir.VerifyRegionMemorySSA(result, projection.Metadata, memorySSA); err != nil {
					return optIRRegionLoadArtifact{}, err
				}
				return optIRRegionLoadArtifact{
					InputProjection: inputProjection, InputSSA: inputSSA,
					CFG: result, Metadata: metadata, Projection: projection, SSA: memorySSA, Report: report,
				}, nil
			})
		references.hasMemory = true
		references.memoryAuthority = memoryAuthorityRef
		references.memoryProjection = memoryProjection
		references.memorySSA = memorySSA
		references.memoryLiveness = memoryLiveness
		references.memoryEvidence = memoryEvidence
		references.dse = dse
		references.regionLoads = regionLoads
		tasks = append(tasks, memoryAuthorityTask, memoryProjectionTask, memorySSATask, memoryLivenessTask, memoryEvidenceTask, dseTask, regionLoadsTask)
	}
	graph, err := opt.NewArtifactGraph(tasks...)
	if err != nil {
		return nil, optIRArtifactRefs{}, err
	}
	return graph, references, nil
}
