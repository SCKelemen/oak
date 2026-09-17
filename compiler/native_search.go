package compiler

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"os"
	"strconv"
	"strings"
	"time"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/typechecker"
)

// The native lane's candidate search (docs/notes/optimizer-search-2026-09.md,
// docs/spec/90-backend.md §16): the compiler lowers each function's
// identity candidate and the candidates the lane's transforms propose
// (nativegen.Transforms), the seam checker and the verifier judge them,
// and the cheapest proven body is kept — else the strongest verdict, the
// plain lowering last. nativeDriver is the search's view of the lane; the
// search itself (opt.Search) decides nothing about admissibility.

// nativeDriver lowers, keys, measures, checks, and verifies one function's
// candidates.
type nativeDriver struct {
	// The allocation proposal cache lives for this function's search only.
	// It neither caches a verdict nor skips candidate admission.
	compileSession nativegen.CompileSession
	source         *ast.FunctionStatement
	functions      map[string]*ast.FunctionStatement
	externs        map[string]*ast.FunctionStatement // the program's extern bindings (asm.Function.Externs)
	records        map[string]*ast.RecordLiteral
	adts           map[string]*ast.ADTType
	constants      map[string]asm.Constant
	tc             *typechecker.TypeChecker
	symbols        map[string]bool
	declarations   string
	// tcFingerprint is tc.NativeLoweringFingerprint(), taken once for the
	// lowering pass: the checker's facts are fixed after checking, and the
	// fingerprint hashes every position-keyed one in the program — taken
	// per candidate it was a twentieth of a native build.
	tcFingerprint string
	// cacheDir is the verdict cache, "" to verify afresh.
	cacheDir string
	// verdicts keeps the verifier's verdict by body for the compiler's
	// report; verified and fromCache tally the cache's use.
	verdicts  map[*asm.Function]asm.Verdict
	verified  *int
	fromCache *int
}

// Materialize lowers the candidate's lane configuration.
func (d *nativeDriver) Materialize(c *opt.Candidate) error {
	lane := c.Config.(nativegen.Lane)
	fn, err := d.compileSession.CompileFor(lane, d.source, d.functions, d.records, d.adts, d.constants, d.tc)
	if err != nil {
		return err
	}
	// The verifier takes calls to program functions at their Oak bodies
	// (asm.Function.Callees, docs/spec/94-assembler.md §8).
	fn.Callees = d.functions
	fn.Externs = d.externs
	c.Body = fn
	if os.Getenv("OAK_NATIVE_DUMP") == "candidates" {
		// A debugging aid: every candidate body as lowered, before the
		// checker and the cost model see it.
		fmt.Fprintf(os.Stderr, "// candidate %s of %s\n%s", c.Name(), fn.Name, nativegen.Describe(fn))
	}
	return nil
}

// Key identifies a body by its spelled assembly and the Oak body the
// verifier judges it against.
func (d *nativeDriver) Key(c *opt.Candidate) string {
	fn := c.Body.(*asm.Function)
	sum := sha256.New()
	sum.Write([]byte(nativegen.Describe(fn)))
	if fn.Body != nil {
		sum.Write([]byte{0})
		sum.Write([]byte(fn.Body.String()))
	}
	return hex.EncodeToString(sum.Sum(nil))
}

// Measure reads the body's structural metrics.
func (d *nativeDriver) Measure(c *opt.Candidate) opt.Metrics {
	return nativegen.Metrics(c.Body.(*asm.Function))
}

// Check runs the seam checker.
func (d *nativeDriver) Check(c *opt.Candidate) []string {
	var facts map[string]typechecker.IndexProof
	if d.tc != nil {
		facts = d.tc.IndexProofs()
	}
	function := c.Body.(*asm.Function)
	findings := asm.CheckWithFacts(function, d.source, d.symbols, facts)
	if lane, ok := c.Config.(nativegen.Lane); ok && lane.UseOptIR {
		if lane.OptIR == nil {
			findings = append(findings, "compiler: OptIR machine-call identity has no CFG authority")
		} else if err := checkOptIRMachineCallIdentity(*lane.OptIR, function); err != nil {
			findings = append(findings, err.Error())
		}
	}
	return findings
}

// Validate runs the verifier, through the verdict cache
// (compiler/verdict_cache.go): a body verified before under the same key —
// the same assembly, Oak body, reachable callees, declarations, and
// compiler — keeps its verdict.
func (d *nativeDriver) Validate(c *opt.Candidate) opt.Verdict {
	fn := c.Body.(*asm.Function)
	start := time.Now()
	key := ""
	if d.cacheDir != "" {
		key = verdictCacheKey(fn, d.source, d.functions, d.declarations)
	}
	verdict, cached := cachedVerdict(d.cacheDir, key, d.functions)
	if !cached {
		verdict = asm.Verify(fn, d.source, verifiedBody(fn, d.source))
		storeVerdict(d.cacheDir, key, verdict)
	} else {
		*d.fromCache++
	}
	*d.verified++
	d.verdicts[fn] = verdict
	if os.Getenv("OAK_NATIVE_TIMING") != "" {
		// A profiling aid: how long each body's verification took.
		note := ""
		if cached {
			note = ", cached"
		}
		fmt.Fprintf(os.Stderr, "timing: %s (%s): %.2fs (%s%s)\n", d.source.Name.Value, c.Name(), time.Since(start).Seconds(), verdict.Kind, note)
	}
	return opt.Verdict{Outcome: outcomeOf(verdict.Kind), Message: verdict.Message, Cached: cached}
}

// outcomeOf maps the verifier's verdict kinds onto the search's outcomes.
func outcomeOf(kind asm.VerdictKind) opt.Outcome {
	switch kind {
	case asm.VerdictProven:
		return opt.Proven
	case asm.VerdictWitnessed:
		return opt.Witnessed
	case asm.VerdictTrusted:
		return opt.Trusted
	}
	return opt.Mismatch
}

// nativeSearch builds the lane's search: its transform registry, the
// lane's static cost model, and the beam (OAK_OPT_BEAM overrides the
// default for experiments; -opt keeps its one meaning, the C compiler's
// level, docs/spec/90-backend.md §16 item 5).
func nativeSearch(arch string, report *opt.Report) *opt.Search {
	registry := nativegen.Registry()
	// Result homes currently trade less result traffic for more frame traffic.
	// Keep them experimental until native timings justify default selection;
	// a lower static cost alone is not evidence of an Apple Silicon speedup.
	skipped := map[string]bool{}
	if os.Getenv("OAK_NATIVE_LOOP_RESULT_HOMES") != "1" {
		skipped[nativegen.TransformLoopResultHomes] = true
	}
	// Small unrolling has promising compressor timings, but not yet a broad
	// quiet-host suite. Keep its bounded expansion and stable array placement
	// independently selectable without changing ordinary builds.
	if os.Getenv("OAK_NATIVE_UNROLL_SMALL") != "1" {
		skipped[nativegen.TransformUnrollSmall] = true
	}
	if skip := os.Getenv("OAK_OPT_SKIP"); skip != "" {
		// For experiments and benchmarks: the named transforms (by their
		// report names, comma-separated) propose nothing; unknown names are
		// ignored. The identity candidate and the verdicts are as always.
		for _, name := range strings.Split(skip, ",") {
			if name = strings.TrimSpace(name); name != "" {
				skipped[name] = true
			}
		}
	}
	if len(skipped) > 0 {
		var kept []opt.Transform
		for _, tr := range registry.Transforms() {
			if !skipped[tr.Name()] {
				kept = append(kept, tr)
			}
		}
		registry = opt.NewRegistry(kept...)
	}
	search := &opt.Search{Registry: registry, Costs: opt.CostsFor(arch), Report: report}
	if beam, err := strconv.Atoi(os.Getenv("OAK_OPT_BEAM")); err == nil && beam > 0 {
		search.Beam = beam
	}
	if os.Getenv("OAK_NATIVE_DUMP") != "" {
		// The refused forms, for reading the checker's gap
		// (docs/spec/94-assembler.md §9.ad).
		search.Refused = func(c *opt.Candidate, round int, findings []string) {
			fn := c.Body.(*asm.Function)
			fmt.Fprintf(os.Stderr, "// refused %s form of %s (round %d): %s\n%s", c.Name(), fn.Name, round, findings[0], nativegen.Describe(fn))
		}
	}
	return search
}

// setAside spells, in the compiler's established phrasing, that a
// transform's form was tried and not kept.
var setAside = map[string]string{
	nativegen.TransformStrength:            "keeps its plain arithmetic",
	nativegen.TransformOptIR:               "keeps its direct lowering",
	nativegen.TransformElide:               "keeps its element guards",
	nativegen.TransformReuseFlags:          "repeats its compares",
	nativegen.TransformHoist:               "keeps its loop invariants in place",
	nativegen.TransformRotate:              "keeps its top-tested loops",
	nativegen.TransformUnroll:              "keeps its plain reduction",
	nativegen.TransformUnrollFills:         "keeps its scalar fill loop",
	nativegen.TransformVectorHomes:         "keeps its vector slots",
	nativegen.TransformLoopArrayHomes:      "keeps its loop array elements in memory",
	nativegen.TransformLoopResultHomes:     "keeps its loop result elements in memory",
	nativegen.TransformCleanup:             "keeps its copies",
	nativegen.TransformPostScheduleCleanup: "keeps its post-schedule copies",
	nativegen.TransformVectorize:           "keeps its scalar reduction",
	nativegen.TransformVectorMaps:          "keeps its scalar map",
	nativegen.TransformUnrollMaps:          "keeps one vector per map trip",
	nativegen.TransformVectorFolds:         "keeps its scalar fold",
	nativegen.TransformUnrollConst:         "keeps its constant-trip loops",
	nativegen.TransformVectorLanes:         "keeps its scalar accumulators",
	nativegen.TransformUnrollSmall:         "keeps its small constant-trip loops",
	nativegen.TransformVecBlocks:           "addresses each vector load",
	nativegen.TransformVectorAddresses:     "keeps separate vector access addresses",
	nativegen.TransformMultiplyAdd:         "keeps its multiply and add apart",
	nativegen.TransformValueSelect:         "branches around its conditional",
	nativegen.TransformReallocate:          "keeps its register assignment",
	nativegen.TransformTrimCalleeSaves:     "keeps its callee-save traffic",
	nativegen.TransformEmptyFrame:          "keeps its empty stack frame",
	nativegen.TransformCarryIndex:          "recomputes its loop index",
	nativegen.TransformRedundantGuards:     "keeps its repeated span guards",
	nativegen.TransformRecordBases:         "recomputes its record-span bases",
	nativegen.TransformRecordBaseCarriers:  "keeps separate record-base destinations",
	nativegen.TransformGlobalAddresses:     "recomputes its scalar-global addresses",
	nativegen.TransformForwardGlobalLoads:  "reloads its scalar globals after stores",
	nativegen.TransformGlobalLoadMasks:     "keeps narrow scalar-global reload masks",
	nativegen.TransformSchedule:            "keeps its instruction order",
	nativegen.TransformFuse:                "keeps its instructions apart",
	nativegen.TransformFuseExits:           "keeps its exit tests apart",
}

// setAsideReasons reads, from the function's remarks, the transforms the
// search tried and set aside — the checker refused their form, or the
// verifier judged it weaker than the selected body — with the reason, in
// the order remarked. A transform that had no site, lacked its fact, or
// changed nothing is not set aside: it never proposed a body.
func setAsideReasons(report *opt.Report, function string, selected *opt.Candidate) []string {
	var out []string
	seen := map[string]bool{}
	for _, remark := range report.For(function) {
		if remark.Kind != opt.Missed {
			continue
		}
		var transforms []string
		switch {
		case setAside[remark.Transform] != "" && isRefusal(remark.Message):
			transforms = []string{remark.Transform}
		case remark.Transform == "verify" && isJudged(remark.Message):
			// "the a+b form was judged ...": every transform of the form
			// the selected body lacks.
			for _, name := range formTransforms(remark.Message) {
				if !selected.Has(name) {
					transforms = append(transforms, name)
				}
			}
		}
		for _, name := range transforms {
			if seen[name] || setAside[name] == "" {
				continue
			}
			seen[name] = true
			out = append(out, fmt.Sprintf("%s %s (%s)", function, setAside[name], remark.Message))
		}
	}
	return out
}

func isRefusal(message string) bool { return strings.HasPrefix(message, "the checker did not admit") }

func isJudged(message string) bool {
	return strings.HasPrefix(message, "the ") && strings.Contains(message, " form was judged ")
}

// formTransforms reads the transform names of "the a+b form ..." messages.
func formTransforms(message string) []string {
	rest := strings.TrimPrefix(message, "the ")
	name, _, _ := strings.Cut(rest, " ")
	var out []string
	for _, part := range strings.Split(name, "+") {
		if part != "" {
			out = append(out, part)
		}
	}
	return out
}
