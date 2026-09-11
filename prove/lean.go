package prove

import (
	"bufio"
	"bytes"
	"fmt"
	"os/exec"
	"regexp"
	"sort"
	"strconv"
	"strings"
)

// The `proved` rung (docs/spec/125-verification.md §5). The projection
// states each theorem as `name_holds` after its definition; running Lean on
// the file and reading its diagnostics back says which statements checked.
// Nothing here trusts the compiler's own opinion: a theorem is `proved`
// only when Lean reported no error inside its statement.

// Proved is the status of a theorem whose Lean statement checked.
const Proved Status = "proved"

// statementRanges maps each theorem to the line range of its `_holds`
// statement in the projection: from the `theorem` line to the line before
// the next top-level declaration or the namespace end.
func statementRanges(projection string) map[string][2]int {
	ranges := map[string][2]int{}
	var current string
	start := 0
	line := 0
	close := func() {
		if current != "" {
			ranges[current] = [2]int{start, line - 1}
			current = ""
		}
	}
	scanner := bufio.NewScanner(strings.NewReader(projection))
	for scanner.Scan() {
		line++
		text := scanner.Text()
		switch {
		case strings.HasPrefix(text, "theorem ") && strings.Contains(text, "_holds "):
			close()
			name := strings.TrimPrefix(text, "theorem ")
			name = name[:strings.Index(name, "_holds ")]
			current, start = name, line
		case strings.HasPrefix(text, "def ") || strings.HasPrefix(text, "end ") ||
			strings.HasPrefix(text, "structure ") || strings.HasPrefix(text, "inductive "):
			close()
		}
	}
	close()
	return ranges
}

var leanDiagnostic = regexp.MustCompile(`^(.*?):(\d+):(\d+): (error|warning): (.*)$`)

// leanErrors maps Lean's error lines to the theorems whose statements
// contain them: theorem name -> first error message. An error outside any
// statement (in a definition the theorems depend on) is recorded under "".
func leanErrors(output string, ranges map[string][2]int) map[string]string {
	errors := map[string]string{}
	for _, text := range strings.Split(output, "\n") {
		match := leanDiagnostic.FindStringSubmatch(text)
		if match == nil || match[4] != "error" {
			continue
		}
		line, _ := strconv.Atoi(match[2])
		owner := ""
		for name, r := range ranges {
			if line >= r[0] && line <= r[1] {
				owner = name
				break
			}
		}
		if _, seen := errors[owner]; !seen {
			errors[owner] = match[5]
		}
	}
	return errors
}

// CheckWithLean runs `lean` on a written projection and upgrades the open
// results whose statements checked to `proved`; a statement Lean rejected
// keeps its open status with Lean's first error, and a projection that
// fails outside every statement leaves all of them open with that error.
// leanBinary is the executable to run (`lean` when empty); its stderr and
// stdout are read for diagnostics, never interpreted as anything else.
func CheckWithLean(leanBinary, path, projection string, results []Result) ([]Result, error) {
	if leanBinary == "" {
		leanBinary = "lean"
	}
	if _, err := exec.LookPath(leanBinary); err != nil {
		return results, fmt.Errorf("lean: %w", err)
	}
	cmd := exec.Command(leanBinary, path)
	var output bytes.Buffer
	cmd.Stdout, cmd.Stderr = &output, &output
	runErr := cmd.Run()
	ranges := statementRanges(projection)
	errors := leanErrors(output.String(), ranges)
	if runErr != nil && len(errors) == 0 {
		// Lean failed without a diagnostic we can place: report as is.
		return results, fmt.Errorf("lean: %v\n%s", runErr, strings.TrimSpace(output.String()))
	}
	upgraded := make([]Result, len(results))
	copy(upgraded, results)
	for i, r := range upgraded {
		if r.Status != Open {
			continue
		}
		if _, stated := ranges[r.Name]; !stated {
			continue
		}
		if global, failed := errors[""]; failed {
			upgraded[i].Detail = r.Detail + " (Lean: " + global + ")"
			continue
		}
		if message, failed := errors[r.Name]; failed {
			upgraded[i].Detail = r.Detail + " (Lean: " + message + ")"
			continue
		}
		upgraded[i] = Result{Name: r.Name, Status: Proved, Detail: "by Lean, from the projection"}
	}
	return upgraded, nil
}

// Names of theorems whose statements a projection carries, sorted.
func statedTheorems(projection string) []string {
	var names []string
	for name := range statementRanges(projection) {
		names = append(names, name)
	}
	sort.Strings(names)
	return names
}
