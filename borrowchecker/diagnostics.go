package borrowchecker

import (
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/diagnostic"
)

const (
	CodeBorrowGeneric          diagnostic.Code = "OAK-B0000"
	CodeBorrowReassign         diagnostic.Code = "OAK-B0101"
	CodeOwnerUsedDuringSpan    diagnostic.Code = "OAK-B0102"
	CodeOwnerWrittenDuringView diagnostic.Code = "OAK-B0103"
	CodeViewConflictsWithSpan  diagnostic.Code = "OAK-B0104"
	CodeSpanConflictsWithView  diagnostic.Code = "OAK-B0105"
	CodeSpanOverlap            diagnostic.Code = "OAK-B0106"
	CodeBorrowSuspended        diagnostic.Code = "OAK-B0107"
	CodeReborrowOverlap        diagnostic.Code = "OAK-B0108"
)

type diagnosticsState struct {
	collector *diagnostic.DiagnosticCollector
}

func newDiagnosticsState() *diagnosticsState {
	return &diagnosticsState{collector: diagnostic.NewDiagnosticCollector()}
}

func (s *diagnosticsState) ensure() {
	if s == nil {
		return
	}
	if s.collector == nil {
		s.collector = diagnostic.NewDiagnosticCollector()
	}
}

func (s *diagnosticsState) clear() {
	if s == nil {
		return
	}
	s.ensure()
	s.collector.Clear()
}

func (s *diagnosticsState) errorStrings() []string {
	if s == nil {
		return nil
	}
	s.ensure()
	out := make([]string, 0, len(s.collector.Errors()))
	for _, d := range s.collector.Errors() {
		out = append(out, d.PlainText())
	}
	return out
}

// Diagnostics returns the semantic borrow diagnostics. Callers should prefer
// this over Errors(); Errors exists only as a compatibility text projection.
func (bc *BorrowChecker) Diagnostics() []*diagnostic.Diagnostic {
	if bc == nil {
		return nil
	}
	if bc.diagnostics == nil {
		bc.diagnostics = newDiagnosticsState()
	}
	return bc.diagnostics.collector.Diagnostics()
}

func (bc *BorrowChecker) reportBorrow(node ast.Node, code diagnostic.Code, title string) *diagnostic.Diagnostic {
	if bc.diagnostics == nil {
		bc.diagnostics = newDiagnosticsState()
	}
	d := diagnostic.NewDiagnosticFromNodeWithCode(node, "borrowchecker", string(code), title)
	bc.diagnostics.collector.AddDiagnostic(d)
	return d
}

// activeBorrowNames returns a deterministic causal ordering. Borrow origins
// with source positions come first in source order; names are only the stable
// fallback when provenance is unavailable or tied.
func (bc *BorrowChecker) activeBorrowNames(owner string, kind borrowKind) []string {
	names := make([]string, 0)
	for name, info := range bc.activeBorrows {
		if info.owner == owner && info.kind == kind {
			names = append(names, name)
		}
	}
	sort.Slice(names, func(i, j int) bool {
		left := bc.activeBorrows[names[i]]
		right := bc.activeBorrows[names[j]]
		if left.origin != nil && right.origin != nil {
			lr := diagnostic.NodeToRange(left.origin).Start
			rr := diagnostic.NodeToRange(right.origin).Start
			if lr.Line != rr.Line {
				return lr.Line < rr.Line
			}
			if lr.Character != rr.Character {
				return lr.Character < rr.Character
			}
		} else if left.origin != nil {
			return true
		} else if right.origin != nil {
			return false
		}
		return names[i] < names[j]
	})
	return names
}

func (bc *BorrowChecker) firstActiveBorrow(owner string, kind borrowKind) (string, borrowInfo, bool) {
	names := bc.activeBorrowNames(owner, kind)
	if len(names) == 0 {
		return "", borrowInfo{}, false
	}
	name := names[0]
	return name, bc.activeBorrows[name], true
}

func (bc *BorrowChecker) addBorrowContext(d *diagnostic.Diagnostic, borrowName string, info borrowInfo, message string) {
	if d == nil {
		return
	}
	if info.origin != nil {
		d.AddSecondary(diagnostic.NodeToRange(info.origin), message)
	} else if message != "" {
		d.AddNote(message)
	}
	if info.region != nil {
		d.AddNote(fmt.Sprintf("%s covers %s of owner %q", borrowName, describeRegion(info.region), info.owner))
	}
}

func describeRegion(region *Region) string {
	if region == nil {
		return "an unknown region"
	}
	end, ok := regionEnd(region)
	if !ok {
		return "an invalid or overflowing region"
	}
	return fmt.Sprintf("[%d..%d)", region.Offset, end)
}
