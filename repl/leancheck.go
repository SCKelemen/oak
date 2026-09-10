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

// Verdict is Lean's judgment of one emitted theorem.
type Verdict string

const (
	// Proved: the theorem elaborated with no diagnostic.
	Proved Verdict = "proved"
	// Open: the theorem elaborated but uses sorry — the programmer's part.
	Open Verdict = "sorry"
	// Failed: Lean reported an error inside the theorem.
	Failed Verdict = "error"
)

// TheoremVerdict is one theorem's outcome with Lean's messages, if any.
type TheoremVerdict struct {
	Name     string
	Line     int
	Verdict  Verdict
	Messages []string
}

// CheckReport is the outcome of elaborating an obligations file.
type CheckReport struct {
	// Theorems in file order.
	Theorems []TheoremVerdict
	// Other are messages Lean reported outside any theorem.
	Other []string
}

// ErrNoLean reports that the Lean toolchain (lake) is not available.
var ErrNoLean = errors.New("lake is not on PATH; check the file with `lake build` in spec/lean")

// LeanCheck writes text to path (a .lean file) and elaborates it with the
// repository's Lean toolchain: `lake env lean --json <path>` from the
// spec/lean directory found above the session's module directory (or named
// by $OAK_LEAN_DIR). Every `theorem` in text receives a verdict.
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
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
	defer cancel()
	command := exec.CommandContext(ctx, lake, "env", "lean", "--json", absolute)
	command.Dir = leanDir
	var stdout, stderr bytes.Buffer
	command.Stdout, command.Stderr = &stdout, &stderr
	runErr := command.Run()
	report := classify(text, stdout.Bytes())
	if runErr != nil && len(report.Theorems) == 0 && len(report.Other) == 0 {
		return nil, fmt.Errorf("lean: %v\n%s", runErr, strings.TrimSpace(stderr.String()))
	}
	return report, nil
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

var theoremLine = regexp.MustCompile(`^theorem\s+([A-Za-z0-9_']+)`)

// classify attributes Lean's messages to the theorems of text by line
// range: a theorem spans from its `theorem` line to the line before the
// next top-level declaration or comment block.
func classify(text string, output []byte) *CheckReport {
	lines := strings.Split(text, "\n")
	type span struct {
		name        string
		start, stop int // 1-based inclusive
	}
	var spans []span
	for i, line := range lines {
		if m := theoremLine.FindStringSubmatch(line); m != nil {
			if len(spans) != 0 && spans[len(spans)-1].stop == 0 {
				spans[len(spans)-1].stop = i
			}
			spans = append(spans, span{name: m[1], start: i + 1})
			continue
		}
		if len(spans) != 0 && spans[len(spans)-1].stop == 0 && (strings.HasPrefix(line, "def ") || strings.HasPrefix(line, "/--") || strings.HasPrefix(line, "end ")) {
			spans[len(spans)-1].stop = i
		}
	}
	if len(spans) != 0 && spans[len(spans)-1].stop == 0 {
		spans[len(spans)-1].stop = len(lines)
	}
	report := &CheckReport{}
	verdicts := make([]TheoremVerdict, len(spans))
	for i, sp := range spans {
		verdicts[i] = TheoremVerdict{Name: sp.name, Line: sp.start, Verdict: Proved}
	}
	scanner := bufio.NewScanner(bytes.NewReader(output))
	scanner.Buffer(make([]byte, 1<<20), 16<<20)
	for scanner.Scan() {
		raw := strings.TrimSpace(scanner.Text())
		if raw == "" {
			continue
		}
		var message leanMessage
		if err := json.Unmarshal([]byte(raw), &message); err != nil {
			report.Other = append(report.Other, raw)
			continue
		}
		summary := fmt.Sprintf("%s:%d: %s", message.Severity, message.Pos.Line, strings.TrimSpace(message.Data))
		owner := -1
		for i, sp := range spans {
			if message.Pos.Line >= sp.start && message.Pos.Line <= sp.stop {
				owner = i
			}
		}
		if owner < 0 {
			report.Other = append(report.Other, summary)
			continue
		}
		verdicts[owner].Messages = append(verdicts[owner].Messages, summary)
		switch {
		case message.Severity == "error":
			verdicts[owner].Verdict = Failed
		case strings.Contains(message.Data, "sorry") && verdicts[owner].Verdict != Failed:
			verdicts[owner].Verdict = Open
		}
	}
	sort.SliceStable(verdicts, func(i, j int) bool { return verdicts[i].Line < verdicts[j].Line })
	report.Theorems = verdicts
	return report
}

// String renders the report one theorem per line.
func (r *CheckReport) String() string {
	var out strings.Builder
	counts := map[Verdict]int{}
	for _, theorem := range r.Theorems {
		counts[theorem.Verdict]++
		fmt.Fprintf(&out, "%-8s %s\n", theorem.Verdict, theorem.Name)
		if theorem.Verdict == Failed {
			for _, message := range theorem.Messages {
				fmt.Fprintf(&out, "         %s\n", message)
			}
		}
	}
	for _, other := range r.Other {
		fmt.Fprintf(&out, "lean: %s\n", other)
	}
	fmt.Fprintf(&out, "%d proved, %d open (sorry), %d failed\n", counts[Proved], counts[Open], counts[Failed])
	return out.String()
}
