package repl

// `:lean check` (docs/spec/83-modules.md section 10): the REPL elaborates the
// obligations it just stated, so the proof exchange with Lean closes inside
// the session. Lean is the checker; the REPL only runs it. `lake` is invoked
// with a fixed argument list and no shell, from the repository's spec/lean
// directory, on a file the REPL wrote itself.

import (
	"bufio"
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"time"
)

// Verdict describes both elaboration and the theorem's transitive trust base.
type Verdict string

const (
	Proved      Verdict = "proved"      // kernel proof, using only Lean's standard logical axioms
	Open        Verdict = "sorry"       // an admission, or an explicitly unproved proposition
	Failed      Verdict = "error"       // elaboration or trust inspection did not complete
	Native      Verdict = "native"      // depends on native evaluation assumptions
	Conditional Verdict = "conditional" // depends on typed (non-propositional) parameters
	Assumed     Verdict = "assumed"     // depends on other propositional axioms
)

type AxiomDependency struct {
	Name string
	Kind string // logical, admission, native, parameter, or assumption
}

type TheoremVerdict struct {
	Name          string
	QualifiedName string
	Line          int
	Verdict       Verdict
	Axioms        []AxiomDependency
	Messages      []string
}

type CheckReport struct {
	Theorems []TheoremVerdict
	// Auxiliaries are compiler-generated theorems without a source declaration.
	// Their trust bases are inspected, but they do not count as user proofs.
	Auxiliaries []TheoremVerdict
	Other       []string
	// Complete is true only after successful elaboration and complete axiom inspection.
	Complete  bool
	hasErrors bool
}

var ErrNoLean = errors.New("lake is not on PATH; check the file with `lake build` in spec/lean")

// LeanCheck elaborates the exact source, then inspects its compiled declarations
// in a separate Lean process. Importing Lean for inspection cannot change the
// environment in which the user's proof was elaborated. This is a checker for
// REPL-generated/trusted Lean source, not a sandbox for adversarial Lean code
// (Lean commands can execute arbitrary IO). No diagnostic text is proof evidence.
func (s *Session) LeanCheck(text, path string) (*CheckReport, error) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		return nil, ErrNoLean
	}
	leanDir, err := findLeanDir(s.ModuleDir)
	if err != nil {
		return nil, err
	}
	absolute, err := filepath.Abs(path)
	if err != nil {
		return nil, err
	}
	if err := os.WriteFile(absolute, []byte(text), 0o644); err != nil {
		return nil, err
	}
	work, err := os.MkdirTemp("", "oak-lean-trust-")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(work)
	input := filepath.Join(work, "OakTrustInput.lean")
	if err := os.WriteFile(input, []byte(text), 0o600); err != nil {
		return nil, err
	}
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
	defer cancel()
	output, stderr, runErr := runLean(ctx, lake, leanDir, nil, "--json", "--root="+work,
		"-o", filepath.Join(work, "OakTrustInput.olean"), input)
	report := classify(text, output)
	if runErr != nil {
		report.invalidate(fmt.Sprintf("elaboration did not complete: %v %s", runErr, stderr))
		return report, nil
	}
	if report.hasErrors {
		return report, nil
	}
	// A per-run token prevents ordinary user messages from masquerading as an
	// audit result. Only the separate inspector's output is considered.
	token := filepath.Base(work)
	audit := filepath.Join(work, "OakTrustAudit.lean")
	if err := os.WriteFile(audit, []byte(strings.ReplaceAll(leanTrustAudit, "OAK_TRUST_TOKEN", token)), 0o600); err != nil {
		return nil, err
	}
	searchPath := work
	if existing := os.Getenv("LEAN_PATH"); existing != "" {
		searchPath += string(os.PathListSeparator) + existing
	}
	output, stderr, runErr = runLean(ctx, lake, leanDir, []string{"LEAN_PATH=" + searchPath}, "--json", audit)
	if runErr != nil {
		report.invalidate(fmt.Sprintf("axiom inspection did not complete: %v %s", runErr, stderr+"\n"+leanFailureDetails(output)))
		return report, nil
	}
	if err := report.applyAudit(text, output, token); err != nil {
		report.invalidate(err.Error())
	}
	return report, nil
}

func runLean(ctx context.Context, lake, dir string, environment []string, args ...string) ([]byte, string, error) {
	command := exec.CommandContext(ctx, lake, append([]string{"env", "lean"}, args...)...)
	command.Dir = dir
	command.Env = append(os.Environ(), environment...)
	var stdout, stderr bytes.Buffer
	command.Stdout, command.Stderr = &stdout, &stderr
	err := command.Run()
	return stdout.Bytes(), strings.TrimSpace(stderr.String()), err
}

func leanFailureDetails(output []byte) string {
	messages, err := decodeLeanMessages(output)
	if err != nil {
		return err.Error()
	}
	var details []string
	for _, message := range messages {
		details = append(details, message.Data)
	}
	return strings.Join(details, "\n")
}

// findLeanDir locates spec/lean by walking up from dir, or takes
// $OAK_LEAN_DIR.
func findLeanDir(dir string) (string, error) {
	if explicit := os.Getenv("OAK_LEAN_DIR"); explicit != "" {
		if _, err := os.Stat(filepath.Join(explicit, "lakefile.toml")); err == nil {
			return explicit, nil
		}
		return "", fmt.Errorf("OAK_LEAN_DIR=%s has no lakefile.toml", explicit)
	}
	current, err := filepath.Abs(dir)
	if err != nil {
		return "", err
	}
	for {
		candidate := filepath.Join(current, "spec", "lean")
		if _, err := os.Stat(filepath.Join(candidate, "lakefile.toml")); err == nil {
			return candidate, nil
		}
		parent := filepath.Dir(current)
		if parent == current {
			return "", errors.New("no spec/lean directory above the working directory; set OAK_LEAN_DIR")
		}
		current = parent
	}
}

// leanMessage is one line of `lean --json` output.
type leanMessage struct {
	Severity string `json:"severity"`
	Pos      struct {
		Line int `json:"line"`
	} `json:"pos"`
	Data string `json:"data"`
}

var theoremLine = regexp.MustCompile(`^\s*(?:(?:private|protected|noncomputable)\s+)*theorem\s+([A-Za-z0-9_'.]+)`)
var obligationLine = regexp.MustCompile(`^-- OAK-OBLIGATION ([A-Za-z0-9_']+): (open|unsupported)$`)

// Source discovery provides locations for diagnostics when elaboration fails;
// it never establishes a successful verdict. Successful discovery comes from
// Lean's actual compiled declarations, including namespaced/private theorems.
func classify(text string, output []byte) *CheckReport {
	report := &CheckReport{}
	for i, line := range strings.Split(text, "\n") {
		if m := theoremLine.FindStringSubmatch(line); m != nil {
			report.Theorems = append(report.Theorems, TheoremVerdict{Name: m[1], Line: i + 1, Verdict: Failed})
		} else if m := obligationLine.FindStringSubmatch(line); m != nil {
			report.Theorems = append(report.Theorems, TheoremVerdict{Name: m[1], Line: i + 2, Verdict: Failed})
		}
	}
	messages, err := decodeLeanMessages(output)
	if err != nil {
		report.invalidate(err.Error())
		return report
	}
	for _, message := range messages {
		summary := fmt.Sprintf("%s:%d: %s", message.Severity, message.Pos.Line, strings.TrimSpace(message.Data))
		report.Other = append(report.Other, summary)
		if message.Severity == "error" {
			report.hasErrors = true
		}
	}
	if report.hasErrors {
		report.invalidate("source contains elaboration errors; no proof verdict is certified")
	}
	return report
}

func decodeLeanMessages(output []byte) ([]leanMessage, error) {
	var messages []leanMessage
	scanner := bufio.NewScanner(bytes.NewReader(output))
	scanner.Buffer(make([]byte, 64<<10), 16<<20)
	for scanner.Scan() {
		raw := strings.TrimSpace(scanner.Text())
		if raw == "" {
			continue
		}
		var message leanMessage
		if err := json.Unmarshal([]byte(raw), &message); err != nil {
			return nil, fmt.Errorf("invalid Lean diagnostic: %w", err)
		}
		switch message.Severity {
		case "information", "warning", "error":
		default:
			return nil, fmt.Errorf("invalid Lean diagnostic severity %q", message.Severity)
		}
		messages = append(messages, message)
	}
	if err := scanner.Err(); err != nil {
		return nil, fmt.Errorf("incomplete Lean diagnostics: %w", err)
	}
	return messages, nil
}

func (r *CheckReport) invalidate(reason string) {
	r.Complete, r.hasErrors = false, true
	r.Other = append(r.Other, reason)
	for i := range r.Theorems {
		r.Theorems[i].Verdict = Failed
		r.Theorems[i].Messages = append(r.Theorems[i].Messages, reason)
	}
}

type trustDeclaration struct {
	Name   string `json:"name"`
	Line   int    `json:"line"`
	Kind   string `json:"kind"`
	Axioms []struct {
		Name        string `json:"name"`
		Proposition bool   `json:"proposition"`
	} `json:"axioms"`
}

type trustAudit struct {
	Token        string             `json:"oakTrust"`
	Declarations []trustDeclaration `json:"declarations"`
}

func (r *CheckReport) applyAudit(text string, output []byte, token string) error {
	if r.hasErrors {
		return errors.New("cannot certify a file with elaboration errors")
	}
	messages, err := decodeLeanMessages(output)
	if err != nil {
		return err
	}
	var audit *trustAudit
	for _, message := range messages {
		if message.Severity == "error" {
			return fmt.Errorf("axiom inspector error: %s", message.Data)
		}
		var row trustAudit
		if json.Unmarshal([]byte(message.Data), &row) == nil && row.Token == token {
			if audit != nil {
				return errors.New("duplicate axiom inspection result")
			}
			audit = &row
		}
	}
	if audit == nil || audit.Declarations == nil {
		return errors.New("missing complete axiom inspection result")
	}
	lines := strings.Split(text, "\n")
	var verdicts []TheoremVerdict
	seen := map[string]bool{}
	for _, decl := range audit.Declarations {
		if decl.Name == "" || decl.Line < 0 || decl.Line > len(lines) || seen[decl.Name] {
			return errors.New("invalid or duplicate audited declaration")
		}
		seen[decl.Name] = true
		name := decl.Name[strings.LastIndex(decl.Name, ".")+1:]
		v := TheoremVerdict{Name: name, QualifiedName: decl.Name, Line: decl.Line, Verdict: Proved}
		switch decl.Kind {
		case "theorem":
			if decl.Line == 0 {
				v.Messages = append(v.Messages, "compiler-generated theorem (no source range)")
			}
			if decl.Axioms == nil {
				return errors.New("missing axiom list in inspection result")
			}
			for _, ax := range decl.Axioms {
				if ax.Name == "" {
					return errors.New("unnamed axiom in inspection result")
				}
				kind := axiomKind(ax.Name, ax.Proposition)
				v.Axioms = append(v.Axioms, AxiomDependency{Name: ax.Name, Kind: kind})
				switch kind {
				case "admission":
					v.Verdict = Open
				case "assumption":
					if v.Verdict != Open {
						v.Verdict = Assumed
					}
				case "parameter":
					if v.Verdict == Proved || v.Verdict == Native {
						v.Verdict = Conditional
					}
				case "native":
					if v.Verdict == Proved {
						v.Verdict = Native
					}
				}
			}
			sort.Slice(v.Axioms, func(i, j int) bool { return v.Axioms[i].Name < v.Axioms[j].Name })
		case "proposition":
			if decl.Line < 2 {
				continue
			}
			marker := obligationLine.FindStringSubmatch(lines[decl.Line-2])
			if marker == nil || marker[1] != name || marker[2] != "open" {
				continue
			}
			v.Verdict = Open
			v.Messages = []string{"unproved proposition; no theorem has been established"}
		case "other":
			continue
		default:
			return fmt.Errorf("unknown audited declaration kind %q", decl.Kind)
		}
		verdicts = append(verdicts, v)
	}
	// Every source-discovered obligation must have actual inspection evidence.
	for _, expected := range r.Theorems {
		if expected.Line >= 2 {
			marker := obligationLine.FindStringSubmatch(lines[expected.Line-2])
			if marker != nil && marker[2] == "unsupported" {
				expected.Verdict = Open
				expected.Messages = []string{"unsupported obligation; no formal proposition was emitted"}
				verdicts = append(verdicts, expected)
				continue
			}
		}
		found := false
		for _, v := range verdicts {
			if v.Line == expected.Line && (v.Name == expected.Name || v.QualifiedName == expected.Name || strings.HasSuffix(v.QualifiedName, "."+expected.Name)) {
				found = true
				break
			}
		}
		if !found {
			return fmt.Errorf("axiom inspection did not cover %s at line %d", expected.Name, expected.Line)
		}
	}
	sort.SliceStable(verdicts, func(i, j int) bool {
		if verdicts[i].Line == verdicts[j].Line {
			return verdicts[i].QualifiedName < verdicts[j].QualifiedName
		}
		return verdicts[i].Line < verdicts[j].Line
	})
	r.Theorems, r.Auxiliaries = nil, nil
	for _, verdict := range verdicts {
		if verdict.Line == 0 {
			r.Auxiliaries = append(r.Auxiliaries, verdict)
		} else {
			r.Theorems = append(r.Theorems, verdict)
		}
	}
	r.Complete = true
	return nil
}

func axiomKind(name string, proposition bool) string {
	switch name {
	case "propext", "Classical.choice", "Quot.sound":
		return "logical"
	case "sorryAx":
		return "admission"
	}
	if name == "Lean.ofReduceBool" || name == "Lean.ofReduceNat" || strings.Contains(name, "._native.native_decide.") || strings.Contains(name, "._native.bv_decide.") {
		return "native"
	}
	if !proposition {
		return "parameter"
	}
	return "assumption"
}

// String always exposes nonstandard dependencies, even when several categories
// occur together. "proved" is reserved for the standard logical trust base.
func (r *CheckReport) String() string {
	var out strings.Builder
	counts := map[Verdict]int{}
	for _, theorem := range r.Theorems {
		counts[theorem.Verdict]++
		name := theorem.Name
		if theorem.QualifiedName != "" {
			name = theorem.QualifiedName
		}
		fmt.Fprintf(&out, "%-11s %s\n", theorem.Verdict, name)
		for _, axiom := range theorem.Axioms {
			fmt.Fprintf(&out, "            %s: %s\n", axiom.Kind, axiom.Name)
		}
		for _, message := range theorem.Messages {
			fmt.Fprintf(&out, "            %s\n", message)
		}
	}
	for _, theorem := range r.Auxiliaries {
		fmt.Fprintf(&out, "auxiliary   %s (%s; excluded from proof totals)\n", theorem.QualifiedName, theorem.Verdict)
		for _, axiom := range theorem.Axioms {
			fmt.Fprintf(&out, "            %s: %s\n", axiom.Kind, axiom.Name)
		}
	}
	for _, other := range r.Other {
		fmt.Fprintf(&out, "lean: %s\n", other)
	}
	fmt.Fprintf(&out, "%d proved, %d open (sorry/unproved), %d native, %d conditional, %d assumed, %d failed\n", counts[Proved], counts[Open], counts[Native], counts[Conditional], counts[Assumed], counts[Failed])
	if !r.Complete {
		out.WriteString("check incomplete; no proof verdict is certified\n")
	}
	return out.String()
}

// The inspected module was compiled independently, without importing Lean.
// Legacy import mode includes private declarations. Metadata and dependencies come
// from Lean's environment, never source-line guesses or warning messages.
const leanTrustAudit = `
import Lean
import OakTrustInput
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let mut rows : Array Json := #[]
 for (n, ci) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  if env.header.modules[idx]!.module.toString != "OakTrustInput" then continue
  let ranges ← findDeclarationRanges? n
  let line := ranges.map (·.selectionRange.pos.line) |>.getD 0
  let kind ← if ci.isTheorem then pure "theorem" else if ci.isDefinition then do
    let claim ← liftTermElabM <| Meta.forallTelescopeReducing ci.type fun _ body => pure (body == mkSort .zero)
    pure (if claim then "proposition" else "other")
   else pure "other"
  let mut deps : Array Json := #[]
  if ci.isTheorem then
   for a in (← collectAxioms n) do
    let info ← getConstInfo a
    let prop ← liftTermElabM <| Meta.isProp info.type
    deps := deps.push <| Json.mkObj [("name", toJson a.toString), ("proposition", toJson prop)]
  rows := rows.push <| Json.mkObj [("name", toJson n.toString), ("line", toJson line), ("kind", toJson kind), ("axioms", toJson deps)]
 liftIO <| IO.println <| (Json.mkObj [("oakTrust", toJson "OAK_TRUST_TOKEN"), ("declarations", toJson rows)]).compress
`
