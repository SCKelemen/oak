package main

import (
	"bufio"
	"os"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"
)

// TestSpecTablesAreRectangular checks every Markdown table in docs/spec: each
// body row must have the same number of cells as its header. A `|` inside a
// cell — an error-set union, a `replace a => b|c` spelling, an `offset_of`
// argument — must be written `\|`, or GitHub splits the row into extra
// columns and the STATUS/STABILITY matrices stop lining up. Merge artifacts
// that duplicate or glue rows show up the same way (found 2026-09-12 in
// STATUS.md, after PR #226).
func TestSpecTablesAreRectangular(t *testing.T) {
	files, err := filepath.Glob(filepath.Join("docs", "spec", "*.md"))
	if err != nil {
		t.Fatal(err)
	}
	if len(files) == 0 {
		t.Fatal("no spec chapters found under docs/spec")
	}
	for _, file := range files {
		for _, problem := range tableProblems(t, file) {
			t.Error(problem)
		}
	}
}

// unescapedPipe matches a `|` not preceded by a backslash.
var unescapedPipe = regexp.MustCompile(`(^|[^\\])\|`)

// delimiterRow matches the header/body separator: only pipes, dashes,
// colons and spaces, with at least one dash.
var delimiterRow = regexp.MustCompile(`^\s*\|[\s:|-]+\|\s*$`)

func cellCount(line string) int {
	return len(unescapedPipe.FindAllStringIndex(line, -1)) - 1
}

// tableProblems returns one message per body row whose cell count differs
// from its table's header. Fenced code blocks are skipped: a `|` in an
// example program is not a table.
func tableProblems(t *testing.T, file string) []string {
	t.Helper()
	f, err := os.Open(file)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()

	var problems []string
	var lines []string
	scanner := bufio.NewScanner(f)
	scanner.Buffer(make([]byte, 0, 1<<20), 1<<24)
	for scanner.Scan() {
		lines = append(lines, scanner.Text())
	}
	if err := scanner.Err(); err != nil {
		t.Fatal(err)
	}

	inFence := false
	header := 0 // cell count of the current table's header; 0 outside a table
	for i, line := range lines {
		if strings.HasPrefix(strings.TrimSpace(line), "```") {
			inFence = !inFence
			continue
		}
		if inFence {
			continue
		}
		if !strings.HasPrefix(strings.TrimSpace(line), "|") {
			header = 0
			continue
		}
		if delimiterRow.MatchString(line) && strings.Contains(line, "-") {
			continue
		}
		next := ""
		if i+1 < len(lines) {
			next = lines[i+1]
		}
		if header == 0 || (delimiterRow.MatchString(next) && strings.Contains(next, "-")) {
			header = cellCount(line)
			continue
		}
		if got := cellCount(line); got != header {
			problems = append(problems, file+":"+strconv.Itoa(i+1)+": table row has "+strconv.Itoa(got)+" cells, header has "+strconv.Itoa(header)+" (escape a literal `|` as `\\|`)")
		}
	}
	return problems
}

func TestTableProblemsFlagsStrayPipe(t *testing.T) {
	dir := t.TempDir()
	file := filepath.Join(dir, "x.md")
	text := "# T\n\n| A | B |\n| --- | --- |\n| ok | `a\\|b` |\n| bad | `a|b` |\n\n```\n| not | a | table |\n```\n"
	if err := os.WriteFile(file, []byte(text), 0o644); err != nil {
		t.Fatal(err)
	}
	problems := tableProblems(t, file)
	if len(problems) != 1 || !strings.Contains(problems[0], "x.md:6:") {
		t.Fatalf("problems = %q, want exactly one at line 6", problems)
	}
}
