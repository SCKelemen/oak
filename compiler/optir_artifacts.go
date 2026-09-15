package compiler

import (
	"context"
	"fmt"

	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/optir"
)

const (
	optIRSCCPRevision       = "oak.optir.sccp.v1"
	optIRLoopsRevision      = "oak.optir.loops.v1"
	optIRCSEDCERevision     = "oak.optir.cse-dce.v1"
	optIRCleanupCFGRevision = "oak.optir.cleanup-cfg.v1"
	optIRLICMRevision       = "oak.optir.licm.v1"
)

type optIRCSEDCEArtifact struct {
	CFG    optir.CFG
	Report optir.CSEDCEReport
}

type optIRLICMArtifact struct {
	CFG    optir.CFG
	Report optir.LICMReport
}

type optIRArtifactKeys struct {
	cfgV0   opt.ArtifactKey
	sccp    opt.ArtifactKey
	loopsV0 opt.ArtifactKey
	cleanup opt.ArtifactKey
	cfgV1   opt.ArtifactKey
	loopsV1 opt.ArtifactKey
	licm    opt.ArtifactKey
}

type optIRAnalysisArtifacts struct {
	constants      optir.SCCPResult
	loops          optir.LoopAnalysis
	simplified     optir.CFG
	simplification optir.CSEDCEReport
	loopInvariant  optir.CFG
	loopMotion     optir.LICMReport
	run            opt.ArtifactRun
	keys           optIRArtifactKeys
}

func runOptIRAnalysisGraph(cfg optir.CFG) (optIRAnalysisArtifacts, error) {
	graph, keys, err := newOptIRAnalysisGraph(cfg)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	run, err := graph.Run(context.Background(), nil, keys.sccp, keys.loopsV0, keys.cleanup, keys.licm)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	constants, err := optIRRunValue[optir.SCCPResult](run, keys.sccp)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	loops, err := optIRRunValue[optir.LoopAnalysis](run, keys.loopsV0)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	cleanup, err := optIRRunValue[optIRCSEDCEArtifact](run, keys.cleanup)
	if err != nil {
		return optIRAnalysisArtifacts{}, err
	}
	licm, err := optIRRunValue[optIRLICMArtifact](run, keys.licm)
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
		keys:           keys,
	}, nil
}

func newOptIRAnalysisGraph(cfg optir.CFG) (*opt.ArtifactGraph, optIRArtifactKeys, error) {
	fingerprint, err := optir.FingerprintCFG(cfg)
	if err != nil {
		return nil, optIRArtifactKeys{}, err
	}
	keys := optIRArtifactKeys{}
	keys.cfgV0 = opt.ArtifactKey{Kind: opt.ArtifactIR, Name: "optir.cfg.v0", Version: fingerprint}
	keys.sccp = derivedOptIRKey(opt.ArtifactAnalysis, "optir.sccp", optIRSCCPRevision, keys.cfgV0)
	keys.loopsV0 = derivedOptIRKey(opt.ArtifactAnalysis, "optir.loops.v0", optIRLoopsRevision, keys.cfgV0)
	keys.cleanup = derivedOptIRKey(opt.ArtifactCandidate, "optir.cse-dce", optIRCSEDCERevision, keys.cfgV0)
	keys.cfgV1 = derivedOptIRKey(opt.ArtifactIR, "optir.cfg.v1", optIRCleanupCFGRevision, keys.cleanup)
	keys.loopsV1 = derivedOptIRKey(opt.ArtifactAnalysis, "optir.loops.v1", optIRLoopsRevision, keys.cfgV1)
	keys.licm = derivedOptIRKey(opt.ArtifactCandidate, "optir.licm", optIRLICMRevision, keys.cfgV1, keys.loopsV1)

	tasks := []opt.ArtifactTask{
		{
			Key: keys.cfgV0,
			Compute: func(context.Context, []opt.Artifact) (any, error) {
				return cfg, nil
			},
		},
		{
			Key:          keys.sccp,
			Dependencies: []opt.ArtifactKey{keys.cfgV0},
			Compute: func(_ context.Context, dependencies []opt.Artifact) (any, error) {
				input, err := optIRDependencyValue[optir.CFG](dependencies, 0)
				if err != nil {
					return nil, err
				}
				return optir.AnalyzeSCCP(input)
			},
		},
		{
			Key:          keys.loopsV0,
			Dependencies: []opt.ArtifactKey{keys.cfgV0},
			Compute: func(_ context.Context, dependencies []opt.Artifact) (any, error) {
				input, err := optIRDependencyValue[optir.CFG](dependencies, 0)
				if err != nil {
					return nil, err
				}
				return optir.AnalyzeLoops(input)
			},
		},
		{
			Key:          keys.cleanup,
			Dependencies: []opt.ArtifactKey{keys.cfgV0},
			Compute: func(_ context.Context, dependencies []opt.Artifact) (any, error) {
				input, err := optIRDependencyValue[optir.CFG](dependencies, 0)
				if err != nil {
					return nil, err
				}
				result, report, err := optir.SimplifyCSEDCE(input)
				return optIRCSEDCEArtifact{CFG: result, Report: report}, err
			},
		},
		{
			Key:          keys.cfgV1,
			Dependencies: []opt.ArtifactKey{keys.cleanup},
			Compute: func(_ context.Context, dependencies []opt.Artifact) (any, error) {
				cleanup, err := optIRDependencyValue[optIRCSEDCEArtifact](dependencies, 0)
				if err != nil {
					return nil, err
				}
				return cleanup.CFG, nil
			},
		},
		{
			Key:          keys.loopsV1,
			Dependencies: []opt.ArtifactKey{keys.cfgV1},
			Compute: func(_ context.Context, dependencies []opt.Artifact) (any, error) {
				input, err := optIRDependencyValue[optir.CFG](dependencies, 0)
				if err != nil {
					return nil, err
				}
				return optir.AnalyzeLoops(input)
			},
		},
		{
			Key:          keys.licm,
			Dependencies: []opt.ArtifactKey{keys.cfgV1, keys.loopsV1},
			Compute: func(_ context.Context, dependencies []opt.Artifact) (any, error) {
				input, err := optIRDependencyValue[optir.CFG](dependencies, 0)
				if err != nil {
					return nil, err
				}
				loops, err := optIRDependencyValue[optir.LoopAnalysis](dependencies, 1)
				if err != nil {
					return nil, err
				}
				result, report, err := optir.HoistLoopInvariantsWithAnalysis(input, loops)
				return optIRLICMArtifact{CFG: result, Report: report}, err
			},
		},
	}
	graph, err := opt.NewArtifactGraph(tasks...)
	if err != nil {
		return nil, optIRArtifactKeys{}, err
	}
	return graph, keys, nil
}

func derivedOptIRKey(kind opt.ArtifactKind, name, revision string, dependencies ...opt.ArtifactKey) opt.ArtifactKey {
	return opt.ArtifactKey{Kind: kind, Name: name, Version: opt.DeriveArtifactVersion(revision, dependencies...)}
}

func optIRDependencyValue[T any](dependencies []opt.Artifact, index int) (T, error) {
	var zero T
	if index < 0 || index >= len(dependencies) {
		return zero, fmt.Errorf("compiler: OptIR artifact dependency %d is missing", index)
	}
	value, ok := dependencies[index].Value.(T)
	if !ok {
		return zero, fmt.Errorf("compiler: OptIR artifact %s has payload %T, expected %T", dependencies[index].Key, dependencies[index].Value, zero)
	}
	return value, nil
}

func optIRRunValue[T any](run opt.ArtifactRun, key opt.ArtifactKey) (T, error) {
	var zero T
	artifact, exists := run.Artifact(key)
	if !exists {
		return zero, fmt.Errorf("compiler: OptIR artifact run did not produce %s", key)
	}
	value, ok := artifact.Value.(T)
	if !ok {
		return zero, fmt.Errorf("compiler: OptIR artifact %s has payload %T, expected %T", key, artifact.Value, zero)
	}
	return value, nil
}
