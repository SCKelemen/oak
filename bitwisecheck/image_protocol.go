package bitwisecheck

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"strconv"
)

const imageAuditSchema = "oak.source-image-parity.audit.v1"

type imageWireBytes []int
type imageWasmBytes []int

func decodeImageBytes(raw []byte, limit int) ([]int, error) {
	var values []json.RawMessage
	if len(raw) == 0 || raw[0] != '[' || json.Unmarshal(raw, &values) != nil || values == nil || len(values) > limit {
		return nil, ErrProtocol
	}
	out := make([]int, len(values))
	for n, v := range values {
		if len(v) == 0 {
			return nil, ErrProtocol
		}
		for _, c := range v {
			if c < '0' || c > '9' {
				return nil, ErrProtocol
			}
		}
		x, e := strconv.Atoi(string(v))
		if e != nil || x > 255 {
			return nil, ErrProtocol
		}
		out[n] = x
	}
	return out, nil
}
func (b *imageWireBytes) UnmarshalJSON(raw []byte) error {
	out, err := decodeImageBytes(raw, MaxImageBytes)
	if err == nil {
		*b = out
	}
	return err
}
func (b *imageWasmBytes) UnmarshalJSON(raw []byte) error {
	out, err := decodeImageBytes(raw, MaxWasmBytes)
	if err == nil {
		*b = out
	}
	return err
}

type imageWireRecord struct {
	Schema      string          `json:"schema"`
	Profile     string          `json:"profile"`
	LeanVersion string          `json:"lean_version"`
	Source      wireBytes       `json:"source"`
	Wasm        imageWasmBytes  `json:"wasm"`
	ARM         imageWireBytes  `json:"arm"`
	RV          imageWireBytes  `json:"rv"`
	Declaration wireDeclaration `json:"declaration"`
	Roots       []Root          `json:"roots"`
}

var imageRootNames = [3]string{"Oak.SourceImageParityRequest.admitted", "Oak.SourceImageParityRequest.binding", "Oak.SourceImageParityRequest.all_inputs"}

func validateImageProtocol(out []byte, in [4][]byte) (imageWireRecord, error) {
	var w imageWireRecord
	bad := func() (imageWireRecord, error) { return imageWireRecord{}, ErrProtocol }
	if len(out) == 0 || len(out) > MaxOutputBytes {
		return bad()
	}
	line := bytes.TrimSuffix(out, []byte{'\n'})
	if bytes.ContainsAny(line, "\r\n") || len(line) == 0 || line[0] != '{' || line[len(line)-1] != '}' {
		return bad()
	}
	var compact bytes.Buffer
	if json.Compact(&compact, line) != nil || !bytes.Equal(compact.Bytes(), line) {
		return bad()
	}
	if !exactKeys(line, "schema", "profile", "lean_version", "source", "wasm", "arm", "rv", "declaration", "roots") {
		return bad()
	}
	dec := json.NewDecoder(bytes.NewReader(line))
	dec.UseNumber()
	if rejectDuplicateKeys(dec, 0) != nil {
		return bad()
	}
	if _, err := dec.Token(); err != io.EOF {
		return bad()
	}
	dec = json.NewDecoder(bytes.NewReader(line))
	dec.DisallowUnknownFields()
	if err := dec.Decode(&w); err != nil {
		return bad()
	}
	if w.Schema != imageAuditSchema || w.Profile != ImageProfile || w.LeanVersion != LeanVersion {
		return bad()
	}
	for n, b := range [][]int{w.Source, w.Wasm, w.ARM, w.RV} {
		if !exactByteEcho(b, in[n]) {
			return bad()
		}
	}
	var fields map[string]json.RawMessage
	_ = json.Unmarshal(line, &fields)
	if !exactKeys(fields["declaration"], "name", "first", "second", "op") {
		return bad()
	}
	if len(w.Declaration.Name) > 256 || !identifierBytes(w.Declaration.Name) || !identifierBytes(w.Declaration.First) || !identifierBytes(w.Declaration.Second) {
		return bad()
	}
	op := map[string]string{"and": "&", "or": "|", "xor": "^"}[w.Declaration.Op]
	if op == "" {
		return bad()
	}
	name, first, second := string(intBytes(w.Declaration.Name)), string(intBytes(w.Declaration.First)), string(intBytes(w.Declaration.Second))
	// Diagnostic metadata must reconstruct the original owned source exactly.
	if !bytes.Equal([]byte(fmt.Sprintf("%s: (%s: u32, %s: u32): u32 = %s %s %s\n", name, first, second, first, op, second)), in[0]) {
		return bad()
	}
	if len(w.Roots) != 3 {
		return bad()
	}
	var rawRoots []json.RawMessage
	if json.Unmarshal(fields["roots"], &rawRoots) != nil {
		return bad()
	}
	for n, r := range w.Roots {
		if !exactKeys(rawRoots[n], "name", "axioms") || r.Name != imageRootNames[n] || r.Axioms == nil {
			return bad()
		}
		prev := -1
		for _, ax := range r.Axioms {
			if ax != "Classical.choice" && ax != "Quot.sound" && ax != "propext" {
				return bad()
			}
			rank := map[string]int{"propext": 0, "Classical.choice": 1, "Quot.sound": 2}[ax]
			if rank <= prev {
				return bad()
			}
			prev = rank
		}
	}
	return w, nil
}
