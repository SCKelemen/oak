package compiler

import (
	"context"

	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/optir"
)

const (
	optIRAnalysisWorkers       = 3
	optIRSCCPRevision          = "oak.optir.sccp.v1"
	optIRLoopStructureRevision = "oak.optir.loop-structure.v1"
	optIRLoopsRevision         = "oak.optir.loops.v2"
	optIRGVNDCERevision        = "oak.optir.gvn-dce.v1"
	optIRCleanupCFGRevision    = "oak.optir.cleanup-cfg.v1"
	optIRPreservationRevision  = "oak.optir.preservation.v1"
	optIRLICMRevision          = "oak.optir.licm.v1"
)

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
	loopStructureV0 opt.ArtifactKey
	loopsV0         opt.ArtifactKey
	cleanup         opt.ArtifactKey
	cfgV1           opt.ArtifactKey
	preservation    opt.ArtifactKey
	loopsV1         opt.ArtifactKey
	licm            opt.ArtifactKey
}

type optIRArtifactRefs struct {
	cfgV0           opt.ArtifactRef[optir.CFG]
	sccp            opt.ArtifactRef[optir.SCCPResult]
	loopStructureV0 opt.ArtifactRef[optir.LoopStructure]
	loopsV0         opt.ArtifactRef[optir.LoopAnalysis]
	cleanup         opt.ArtifactRef[optIRGVNDCEArtifact]
	cfgV1           opt.ArtifactRef[optir.CFG]
	preservation    opt.ArtifactRef[optir.PreservationCertificate]
	loopsV1         opt.ArtifactRef[optir.LoopAnalysis]
	licm            opt.ArtifactRef[optIRLICMArtifact]
}

func (references optIRArtifactRefs) keys() optIRArtifactKeys {
	return optIRArtifactKeys{
		cfgV0:           references.cfgV0.Key(),
		sccp:            references.sccp.Key(),
		loopStructureV0: references.loopStructureV0.Key(),
		loopsV0:         references.loopsV0.Key(),
		cleanup:         references.cleanup.Key(),
		cfgV1:           references.cfgV1.Key(),
		preservation:    references.preservation.Key(),
		loopsV1:         references.loopsV1.Key(),
		licm:            references.licm.Key(),
	}
}

type optIRAnalysisArtifacts struct {
	constants      optir.SCCPResult
	loops          optir.LoopAnalysis
	simplified     optir.CFG
	simplification optir.GVNDCEReport
	loopInvariant  optir.CFG
	loopMotion     optir.LICMReport
	run            opt.ArtifactRun
	keys           optIRArtifactKeys
}

func runOptIRAnalysisGraph(cfg optir.CFG) (optIRAnalysisArtifacts, error) {
	graph, references, err := newOptIRAnalysisGraph(cfg)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	run, err := graph.RunParallel(context.Background(), nil, optIRAnalysisWorkers, references.sccp.Key(), references.loopsV0.Key(), references.cleanup.Key(), references.licm.Key())
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	constants, err := references.sccp.Value(run)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	loops, err := references.loopsV0.Value(run)
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
		constants:      constants,
		loops:          loops,
		simplified:     cleanup.CFG,
		simplification: cleanup.Report,
		loopInvariant:  licm.CFG,
		loopMotion:     licm.Report,
		run:            run,
		keys:           references.keys(),
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
	loopStructureV0, loopStructureV0Task := opt.DerivedArtifact1(opt.ArtifactAnalysis, "optir.loop-structure.v0", optIRLoopStructureRevision, cfgV0,
		func(_ context.Context, input optir.CFG) (optir.LoopStructure, error) {
			return optir.AnalyzeLoopStructure(input)
		})
	loopsV0, loopsV0Task := opt.DerivedArtifact2(opt.ArtifactAnalysis, "optir.loops.v0", optIRLoopsRevision, cfgV0, loopStructureV0,
		func(_ context.Context, input optir.CFG, structure optir.LoopStructure) (optir.LoopAnalysis, error) {
			return optir.AnalyzeLoopsWithStructure(input, structure)
		})
	cleanup, cleanupTask := opt.DerivedArtifact1(opt.ArtifactCandidate, "optir.gvn-dce", optIRGVNDCERevision, cfgV0,
		func(_ context.Context, input optir.CFG) (optIRGVNDCEArtifact, error) {
			result, report, err := optir.SimplifyGVNDCE(input)
			return optIRGVNDCEArtifact{CFG: result, Report: report}, err
		})
	cfgV1, cfgV1Task := opt.DerivedArtifact1(opt.ArtifactIR, "optir.cfg.v1", optIRCleanupCFGRevision, cleanup,
		func(_ context.Context, result optIRGVNDCEArtifact) (optir.CFG, error) { return result.CFG, nil })
	preservation, preservationTask := opt.DerivedArtifact2(opt.ArtifactAdmission, "optir.gvn-dce.preservation", optIRPreservationRevision, cfgV0, cfgV1,
		func(_ context.Context, before, after optir.CFG) (optir.PreservationCertificate, error) {
			return optir.CheckCFGPreservation(
				cfgV0.Key(),
				before,
				cfgV1.Key(),
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
	loopsV1, loopsV1Task := opt.DerivedArtifact3(opt.ArtifactAnalysis, "optir.loops.v1", optIRLoopsRevision, cfgV1, loopStructureV0, preservation,
		func(_ context.Context, input optir.CFG, structure optir.LoopStructure, certificate optir.PreservationCertificate) (optir.LoopAnalysis, error) {
			return optir.AnalyzeLoopsWithPreservedStructure(input, structure, certificate)
		})
	licm, licmTask := opt.DerivedArtifact2(opt.ArtifactCandidate, "optir.licm", optIRLICMRevision, cfgV1, loopsV1,
		func(_ context.Context, input optir.CFG, loops optir.LoopAnalysis) (optIRLICMArtifact, error) {
			result, report, err := optir.HoistLoopInvariantsWithAnalysis(input, loops)
			return optIRLICMArtifact{CFG: result, Report: report}, err
		})

	references := optIRArtifactRefs{
		cfgV0:           cfgV0,
		sccp:            sccp,
		loopStructureV0: loopStructureV0,
		loopsV0:         loopsV0,
		cleanup:         cleanup,
		cfgV1:           cfgV1,
		preservation:    preservation,
		loopsV1:         loopsV1,
		licm:            licm,
	}
	tasks := []opt.ArtifactTask{cfgV0Task, sccpTask, loopStructureV0Task, loopsV0Task, cleanupTask, cfgV1Task, preservationTask, loopsV1Task, licmTask}
	graph, err := opt.NewArtifactGraph(tasks...)
	if err != nil {
		return nil, optIRArtifactRefs{}, err
	}
	return graph, references, nil
}
