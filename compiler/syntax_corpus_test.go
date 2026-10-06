package compiler

import (
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"
)

var syntaxExitCase = regexp.MustCompile(`\.exit([0-9]{1,3})\.oak$`)

func TestSyntaxCorpus(t *testing.T) {
	root := filepath.Join("testdata", "syntax")
	seen := 0
	err := filepath.WalkDir(root, func(path string, entry fs.DirEntry, walkErr error) error {
		if walkErr != nil {
			return walkErr
		}
		if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".oak") {
			return nil
		}
		seen++
		rel, err := filepath.Rel(root, path)
		if err != nil {
			return err
		}
		rel = filepath.ToSlash(rel)
		source, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		name := strings.NewReplacer("/", "_", ".", "_").Replace(rel)
		t.Run(name, func(t *testing.T) {
			comp := New().WithSource(filepath.ToSlash(filepath.Join("testdata", "syntax", rel)), string(source)).WithPackageName("syntax")
			switch {
			case strings.HasSuffix(rel, ".parse.oak"):
				if _, err := comp.Parse().Get(); err != nil {
					t.Fatalf("parse contract failed: %v", err)
				}
			case strings.HasSuffix(rel, ".check.oak"):
				if _, err := comp.Check().Get(); err != nil {
					t.Fatalf("semantic contract failed: %v", err)
				}
			case syntaxExitCase.MatchString(rel):
				match := syntaxExitCase.FindStringSubmatch(rel)
				want, err := strconv.Atoi(match[1])
				if err != nil || want < 0 || want > 255 {
					t.Fatalf("invalid exit-code suffix in %q", rel)
				}
				code, abnormal := buildAndRun(t, name, string(source))
				if abnormal || code != want {
					t.Fatalf("native exit = (%d, abnormal=%v), want %d", code, abnormal, want)
				}
			default:
				t.Fatalf("syntax case %q must end in .parse.oak, .check.oak, or .exitN.oak", rel)
			}
		})
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	if seen == 0 {
		t.Fatal("syntax corpus is empty")
	}
}
