package lrat

import (
	"fmt"
	"strings"
	"testing"
)

// token consumes the newline when it reports the end of a line. A blank
// line must not cause Check to discard the command on the following line.
func TestCheckBlankLinesPreserveCommands(t *testing.T) {
	lines := strings.Split(strings.TrimSuffix(testProof, "\n"), "\n")
	for _, blank := range []string{"\n", " \t\r\n", "\n\n", "\r\n\r\n"} {
		for at := 0; at <= len(lines); at++ {
			t.Run(fmt.Sprintf("%q/before-%d", blank, at), func(t *testing.T) {
				parts := append([]string(nil), lines[:at]...)
				parts = append(parts, strings.TrimSuffix(blank, "\n"))
				parts = append(parts, lines[at:]...)
				result, err := Check(testFormula, strings.Join(parts, "\n")+"\n")
				if err != nil || result.Additions != 2 || result.Deletions != 2 {
					t.Fatalf("blank line changed the proof: result=%+v err=%v", result, err)
				}
			})
		}
	}
}

func TestCheckBlankLinesDoNotHideInvalidCommands(t *testing.T) {
	formula := "p cnf 1 2\n1 0\n-1 0\n"
	refutation := "3 0 1 2 0\n"
	for _, blank := range []string{"\n", " \t\r\n", "\n\n"} {
		for _, suffix := range []string{"garbage", "4 0 0", "3 d 99 0", "4 0 1 2 0 trailing"} {
			for _, ending := range []string{"", "\n", "\r\n"} {
				t.Run(fmt.Sprintf("%q/%q/%q", blank, suffix, ending), func(t *testing.T) {
					if _, err := Check(formula, refutation+blank+suffix+ending); err == nil {
						t.Fatal("accepted an invalid suffix after a blank line")
					}
				})
			}
		}
	}
	// Skipping this deletion incorrectly leaves clause 1 available to the
	// otherwise valid refutation. The whole proof stream must be checked.
	if _, err := Check(formula, "\n2 d 1 0\n"+refutation); err == nil {
		t.Fatal("accepted a proof that uses a clause deleted after a blank line")
	}
}

func TestCheckCommentAndBlankLineBoundaries(t *testing.T) {
	for _, prefix := range []string{"c ignored\n", "\nc ignored\n", "c ignored\n\n", " \t c ignored\r\n\r\n"} {
		result, err := Check(testFormula, prefix+testProof+"\nc trailing comment")
		if err != nil || result.Additions != 2 || result.Deletions != 2 {
			t.Errorf("prefix %q: result=%+v err=%v", prefix, result, err)
		}
	}
}
