package compiler

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"reflect"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/optir"
)

// StatefulRawExport is a lossless, deterministic custody format. The exact
// raw CFG is the semantic input; metadata is not discarded or replaced by a
// digest. Serialization/frontend correspondence is tested, not kernel-proved.
type StatefulRawExport struct {
	Profile           string
	Root              string
	Functions         []StatefulRawFunctionExport
	Types             []optir.StatefulTypeRecord
	Accesses          []optir.ByteAccessRecord
	Calls             []optir.StatefulCallRecord
	ProjectedAccesses []optir.StatefulProjectedByteAccess
	Sources           []PackageSource
	IndexProofs       []StatefulIndexProof
}
type StatefulRawFunctionExport struct {
	Structured optir.Function
	CFG        optir.CFG
	Facts      []optir.CheckedFactRecord
}

func (a CheckedStatefulOptIR) Export() (StatefulRawExport, error) {
	if err := optir.VerifyStatefulProgram(a.program); err != nil {
		return StatefulRawExport{}, err
	}
	result := StatefulRawExport{Profile: a.program.Profile(), Root: a.program.Root(), Types: a.program.Types(), Accesses: a.program.ByteAccesses(), Calls: a.program.Calls(), ProjectedAccesses: a.program.ProjectedByteAccesses(), Sources: a.Sources(), IndexProofs: a.IndexProofs()}
	for _, f := range a.program.Functions() {
		result.Functions = append(result.Functions, StatefulRawFunctionExport{Structured: f.Structured, CFG: f.CFG, Facts: f.Facts.Records()})
	}
	return result, nil
}

// ValidateExportJSON binds a transported snapshot back to this exact owned
// checked artifact without a hash-only admission rule. Unknown fields and
// trailing values fail closed; meaningful omitted/changed data cannot match.
func (a CheckedStatefulOptIR) ValidateExportJSON(encoded []byte) error {
	want, err := a.Export()
	if err != nil {
		return err
	}
	var got StatefulRawExport
	decoder := json.NewDecoder(bytes.NewReader(encoded))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(&got); err != nil {
		return fmt.Errorf("compiler: invalid stateful raw export: %w", err)
	}
	var trailing any
	if err := decoder.Decode(&trailing); err != io.EOF {
		return fmt.Errorf("compiler: stateful raw export has trailing data")
	}
	if !reflect.DeepEqual(got, want) {
		return fmt.Errorf("compiler: stateful raw export does not exactly match the checked owned snapshot")
	}
	return nil
}

func (a CheckedStatefulOptIR) ExportJSON() ([]byte, error) {
	data, err := a.Export()
	if err != nil {
		return nil, err
	}
	return json.MarshalIndent(data, "", "  ")
}

// ExportLean reifies the actual owned CFG, field for field. The accompanying
// full custody JSON also freezes structured control, checked authorities and
// original parsed Oak dependency files (not oak.mod/module-manifest bytes).
// Neither a digest nor a hard-coded graph is used.
func (a CheckedStatefulOptIR) ExportLean() (string, error) {
	data, err := a.Export()
	if err != nil {
		return "", err
	}
	jsonData, err := json.Marshal(data)
	if err != nil {
		return "", err
	}
	var out strings.Builder
	out.WriteString("-- Generated from Compilation.Check + StatefulCopyOptIR. Do not hand edit.\nimport Oak.OptIRExecution\n\nnamespace Oak.OptIRStatefulCopy.Generated\nopen Oak.OptIRExecution\n\ndef program : Program := [\n")
	for i, f := range data.Functions {
		if i != 0 {
			out.WriteString(",\n")
		}
		out.WriteString(leanCFG(f.CFG))
	}
	out.WriteString("\n]\n\n-- Exact custody data, not a proof callback or acceptance hash.\ndef custodyJSON : String := ")
	out.WriteString(leanString(string(jsonData)))
	out.WriteString("\n\nend Oak.OptIRStatefulCopy.Generated\n")
	return out.String(), nil
}
func leanString(s string) string {
	var out strings.Builder
	out.WriteByte('"')
	for _, r := range s {
		switch r {
		case '\\':
			out.WriteString("\\\\")
		case '"':
			out.WriteString("\\\"")
		case '\n':
			out.WriteString("\\n")
		case '\r':
			out.WriteString("\\r")
		case '\t':
			out.WriteString("\\t")
		default:
			if r < 32 || r == 127 {
				fmt.Fprintf(&out, "\\u{%x}", r)
			} else {
				out.WriteRune(r)
			}
		}
	}
	out.WriteByte('"')
	return out.String()
}
func leanList[T any](items []T, f func(T) string) string {
	parts := make([]string, len(items))
	for i, x := range items {
		parts[i] = f(x)
	}
	return "[" + strings.Join(parts, ", ") + "]"
}
func leanID(id optir.ValueID) string { return strconv.FormatUint(uint64(id), 10) }
func leanType(t optir.Type) string   { return leanString(string(t)) }
func leanSource(s optir.Source) string {
	return fmt.Sprintf("{ context := %s, line := %d, column := %d }", leanString(s.Context), s.Line, s.Column)
}
func leanValue(v optir.Value) string {
	return fmt.Sprintf("{ id := %d, ty := %s, name := %s, source := %s }", v.ID, leanType(v.Type), leanString(v.Name), leanSource(v.Source))
}
func leanAttribute(a optir.Attribute) string {
	return fmt.Sprintf("{ name := %s, value := %s }", leanString(a.Name), leanString(a.Value))
}
func leanFact(f optir.Fact) string {
	return fmt.Sprintf("{ id := %s, name := %s, values := %s, provenance := %s, witness := %s, scope := %s, dependencies := %s }", leanString(f.ID), leanString(f.Name), leanList(f.Values, leanID), leanString(f.Provenance), leanString(f.Witness), leanString(f.Scope), leanList(f.Dependencies, leanString))
}
func leanOperation(o optir.Operation) string {
	return fmt.Sprintf("{ code := %s, results := %s, operands := %s, effects := %s, attributes := %s, facts := %s, source := %s, memoryAccessID := %s, memoryCallID := %s }", leanString(o.Code), leanList(o.Results, leanValue), leanList(o.Operands, leanID), leanList(o.Effects, func(e optir.Effect) string { return leanString(string(e)) }), leanList(o.Attributes, leanAttribute), leanList(o.Facts, leanFact), leanSource(o.Source), leanString(o.MemoryAccessID), leanString(o.MemoryCallID))
}
func leanEdge(e optir.Edge) string {
	return fmt.Sprintf("{ target := %d, arguments := %s }", e.Target, leanList(e.Arguments, leanID))
}
func leanTerminator(t optir.Terminator) string {
	return fmt.Sprintf("{ kind := %s, condition := %d, trueEdge := %s, falseEdge := %s, values := %s }", leanString(string(t.Kind)), t.Condition, leanEdge(t.True), leanEdge(t.False), leanList(t.Values, leanID))
}
func leanBlock(b optir.Block) string {
	return fmt.Sprintf("{ id := %d, parameters := %s, operations := %s, terminator := %s }", b.ID, leanList(b.Parameters, leanValue), leanList(b.Operations, leanOperation), leanTerminator(b.Terminator))
}
func leanCFG(c optir.CFG) string {
	return fmt.Sprintf("{ name := %s, entry := %d, results := %s, blocks := %s, facts := %s }", leanString(c.Name), c.Entry, leanList(c.Results, leanType), leanList(c.Blocks, leanBlock), leanList(c.Facts, leanFact))
}
