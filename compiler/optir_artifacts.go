package compiler

import (
	"context"

	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/optir"
)

const (
	optIRAnalysisWorkers       = 3
	optIRSCCPRevision          = "oak.optir.sccp.v1"
	optIRSCCPRewriteRevision   = "oak.optir.sccp-rewrite.v1"
	optIRSCCPCFGRevision       = "oak.optir.sccp-cfg.v1"
	optIRLoopStructureRevision = "oak.optir.loop-structure.v1"
	optIRLoopsRevision         = "oak.optir.loops.v2"
	optIRGVNDCERevision        = "oak.optir.gvn-dce.v2"
	optIRCleanupCFGRevision    = "oak.optir.cleanup-cfg.v3"
	optIRPreservationRevision  = "oak.optir.preservation.v1"
	optIRLICMRevision          = "oak.optir.licm.v1"
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

type optIRArtifactKeys struct {
	cfgV0           opt.ArtifactKey
	sccp            opt.ArtifactKey
	sccpRewrite     opt.ArtifactKey
	cfgV1           opt.ArtifactKey
	loopStructureV1 opt.ArtifactKey
	loopsV1         opt.ArtifactKey
	cleanup         opt.ArtifactKey
	cfgV2           opt.ArtifactKey
	preservation    opt.ArtifactKey
	loopsV2         opt.ArtifactKey
	licm            opt.ArtifactKey
}

type optIRArtifactRefs struct {
	cfgV0           opt.ArtifactRef[optir.CFG]
	sccp            opt.ArtifactRef[optir.SCCPResult]
	sccpRewrite     opt.ArtifactRef[optIRSCCPRewriteArtifact]
	cfgV1           opt.ArtifactRef[optir.CFG]
	loopStructureV1 opt.ArtifactRef[optir.LoopStructure]
	loopsV1         opt.ArtifactRef[optir.LoopAnalysis]
	cleanup         opt.ArtifactRef[optIRGVNDCEArtifact]
	cfgV2           opt.ArtifactRef[optir.CFG]
	preservation    opt.ArtifactRef[optir.PreservationCertificate]
	loopsV2         opt.ArtifactRef[optir.LoopAnalysis]
	licm            opt.ArtifactRef[optIRLICMArtifact]
}

func (references optIRArtifactRefs) keys() optIRArtifactKeys {
	return optIRArtifactKeys{
		cfgV0:           references.cfgV0.Key(),
		sccp:            references.sccp.Key(),
		sccpRewrite:     references.sccpRewrite.Key(),
		cfgV1:           references.cfgV1.Key(),
		loopStructureV1: references.loopStructureV1.Key(),
		loopsV1:         references.loopsV1.Key(),
		cleanup:         references.cleanup.Key(),
		cfgV2:           references.cfgV2.Key(),
		preservation:    references.preservation.Key(),
		loopsV2:         references.loopsV2.Key(),
		licm:            references.licm.Key(),
	}
}

type optIRAnalysisArtifacts struct {
	constants          optir.SCCPResult
	sccpSimplified     optir.CFG
	sccpSimplification optir.SCCPRewriteReport
	loops              optir.LoopAnalysis
	simplified         optir.CFG
	simplification     optir.GVNDCEReport
	loopInvariant      optir.CFG
	loopMotion         optir.LICMReport
	run                opt.ArtifactRun
	keys               optIRArtifactKeys
}

func runOptIRAnalysisGraph(cfg optir.CFG) (optIRAnalysisArtifacts, error) {
	graph, references, err := newOptIRAnalysisGraph(cfg)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	run, err := graph.RunParallel(context.Background(), nil, optIRAnalysisWorkers, references.sccp.Key(), references.sccpRewrite.Key(), references.loopsV1.Key(), references.cleanup.Key(), references.licm.Key())
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
	return optIRAnalysisArtifacts{
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
	}, nil
}

func newOptIRAnalysisGraph(cfg optir.CFG) (*opt.ArtifactGraph, optIRArtifactRefs, error) {
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
	}
	tasks := []opt.ArtifactTask{cfgV0Task, sccpTask, sccpRewriteTask, cfgV1Task, loopStructureV1Task, loopsV1Task, cleanupTask, cfgV2Task, preservationTask, loopsV2Task, licmTask}
	graph, err := opt.NewArtifactGraph(tasks...)
	if err != nil {
		return nil, optIRArtifactRefs{}, err
	}
	return graph, references, nil
}
