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
	source       *ast.FunctionStatement
	functions    map[string]*ast.FunctionStatement
	records      map[string]*ast.RecordLiteral
	adts         map[string]*ast.ADTType
	constants    map[string]asm.Constant
	tc           *typechecker.TypeChecker
	symbols      map[string]bool
	declarations string
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
	fn, err := nativegen.CompileFor(lane, d.source, d.functions, d.records, d.adts, d.constants, d.tc)
	if err != nil {
		return err
	}
	// The verifier takes calls to program functions at their Oak bodies
	// (asm.Function.Callees, docs/spec/94-assembler.md §8).
	fn.Callees = d.functions
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
	return asm.Check(c.Body.(*asm.Function), d.source, d.symbols)
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
	verdict, cached := cachedVerdict(d.cacheDir, key)
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
	search := &opt.Search{Registry: nativegen.Registry(), Costs: opt.CostsFor(arch), Report: report}
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
	nativegen.TransformStrength:    "keeps its plain arithmetic",
	nativegen.TransformElide:       "keeps its element guards",
	nativegen.TransformReuseFlags:  "repeats its compares",
	nativegen.TransformHoist:       "keeps its loop invariants in place",
	nativegen.TransformUnroll:      "keeps its plain reduction",
	nativegen.TransformVectorHomes: "keeps its vector slots",
	nativegen.TransformCleanup:     "keeps its copies",
	nativegen.TransformVectorize:   "keeps its scalar reduction",
	nativegen.TransformReallocate:  "keeps its register assignment",
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
