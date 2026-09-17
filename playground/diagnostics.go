package playground

import (
	"unicode/utf8"

	"github.com/SCKelemen/oak/diagnostic"
)

const MaxDiagnostics = 64
const MaxDiagnosticBytes = 8192

// Diagnostic is the bounded browser projection, not the compiler's open-ended
// diagnostic.Data/related-file payload. Positions are zero-based UTF-16, as in
// LSP. An absent range means no source location is known; never invent one from
// an error string. The browser also checks ranges against its current source.
type Diagnostic struct {
	Severity string           `json:"severity"`
	Code     string           `json:"code"`
	Source   string           `json:"source"`
	Message  string           `json:"message"`
	Range    *DiagnosticRange `json:"range,omitempty"`
}

type DiagnosticPosition struct {
	Line      int `json:"line"`
	Character int `json:"character"`
}

type DiagnosticRange struct {
	Start DiagnosticPosition `json:"start"`
	End   DiagnosticPosition `json:"end"`
}

func boundedText(s string, limit int) string {
	if len(s) <= limit {
		return s
	}
	for limit > 0 && !utf8.RuneStart(s[limit]) {
		limit--
	}
	return s[:limit]
}

func (r *Response) appendDiagnostic(d Diagnostic) {
	if len(r.Diagnostics) == MaxDiagnostics {
		r.DiagnosticsTruncated = true
		return
	}
	r.Diagnostics = append(r.Diagnostics, d)
}

func (r *Response) addDiagnostic(d *diagnostic.Diagnostic) {
	if d == nil {
		return
	}
	out := Diagnostic{
		Severity: d.Severity.String(), Code: boundedText(d.Code, 128),
		Source: boundedText(d.Source, 128), Message: boundedText(d.Message, MaxDiagnosticBytes),
	}
	a, b := d.Range.Start, d.Range.End
	if (d.File == "" || d.File == "playground.oak") && a.Line >= 0 && a.Character >= 0 &&
		b.Line >= a.Line && b.Character >= 0 && (b.Line != a.Line || b.Character >= a.Character) {
		out.Range = &DiagnosticRange{
			Start: DiagnosticPosition{Line: a.Line, Character: a.Character},
			End:   DiagnosticPosition{Line: b.Line, Character: b.Character},
		}
	}
	r.appendDiagnostic(out)
}

func (r *Response) refuse(message string) {
	r.Error = boundedText(message, MaxDiagnosticBytes)
	for _, d := range r.Diagnostics {
		if d.Severity == "error" {
			return
		}
	}
	r.appendDiagnostic(Diagnostic{
		Severity: "error", Code: string(diagnostic.CodeCompilerGeneric),
		Source: "playground", Message: r.Error,
	})
}
