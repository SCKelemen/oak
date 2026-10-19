package bitwisecheck

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"strconv"
)

// wireBytes accepts only arrays of decimal integer byte tokens. In particular,
// encoding/json's permissive null-to-zero coercion must never reach an echo.
type wireBytes []int

func (b *wireBytes) UnmarshalJSON(raw []byte) error {
	var values []json.RawMessage
	if len(raw) == 0 || raw[0] != '[' || json.Unmarshal(raw, &values) != nil || values == nil || len(values) > MaxSourceBytes {
		return ErrProtocol
	}
	out := make(wireBytes, len(values))
	for n, v := range values {
		if len(v) == 0 {
			return ErrProtocol
		}
		for _, c := range v {
			if c < '0' || c > '9' {
				return ErrProtocol
			}
		}
		x, err := strconv.Atoi(string(v))
		if err != nil || x > 255 {
			return ErrProtocol
		}
		out[n] = x
	}
	*b = out
	return nil
}

type wireDeclaration struct {
	Name   wireBytes `json:"name"`
	First  wireBytes `json:"first"`
	Second wireBytes `json:"second"`
	Op     string    `json:"op"`
}
type wireRecord struct {
	Schema       string          `json:"schema"`
	Profile      string          `json:"profile"`
	ProofPackage string          `json:"proof_package"`
	LeanVersion  string          `json:"lean_version"`
	Source       wireBytes       `json:"source"`
	Wasm         wireBytes       `json:"wasm"`
	ARM          wireBytes       `json:"arm"`
	RV           wireBytes       `json:"rv"`
	Declaration  wireDeclaration `json:"declaration"`
	Roots        []Root          `json:"roots"`
}

var rootNames = [3]string{"Oak.CheckedBundleRequest.admitted", "Oak.CheckedBundleRequest.binding", "Oak.CheckedBundleRequest.all_inputs"}

// Check duplicate keys before typed decoding: encoding/json's ordinary decoder
// accepts duplicates with last-key-wins, which is unsuitable for this protocol.
func rejectDuplicateKeys(dec *json.Decoder, depth int) error {
	if depth > 8 {
		return ErrProtocol
	}
	tok, err := dec.Token()
	if err != nil {
		return err
	}
	switch tok {
	case json.Delim('{'):
		keys := map[string]bool{}
		for dec.More() {
			tok, err = dec.Token()
			if err != nil {
				return err
			}
			key, ok := tok.(string)
			if !ok || keys[key] {
				return ErrProtocol
			}
			keys[key] = true
			if err = rejectDuplicateKeys(dec, depth+1); err != nil {
				return err
			}
		}
		tok, err = dec.Token()
		if err != nil || tok != json.Delim('}') {
			return ErrProtocol
		}
	case json.Delim('['):
		for dec.More() {
			if err = rejectDuplicateKeys(dec, depth+1); err != nil {
				return err
			}
		}
		tok, err = dec.Token()
		if err != nil || tok != json.Delim(']') {
			return ErrProtocol
		}
	}
	return nil
}
func exactKeys(raw []byte, keys ...string) bool {
	var fields map[string]json.RawMessage
	if json.Unmarshal(raw, &fields) != nil || len(fields) != len(keys) {
		return false
	}
	for _, key := range keys {
		if _, ok := fields[key]; !ok {
			return false
		}
	}
	return true
}
func exactByteEcho(got []int, want []byte) bool {
	if got == nil || len(got) != len(want) {
		return false
	}
	for n, x := range got {
		if x < 0 || x > 255 || byte(x) != want[n] {
			return false
		}
	}
	return true
}
func intBytes(in []int) []byte {
	out := make([]byte, len(in))
	for n, x := range in {
		out[n] = byte(x)
	}
	return out
}
func identifierBytes(in []int) bool {
	if len(in) == 0 || len(in) > MaxSourceBytes {
		return false
	}
	for i, b := range in {
		if !(b >= 'a' && b <= 'z' || b >= 'A' && b <= 'Z' || i > 0 && b >= '0' && b <= '9') {
			return false
		}
	}
	return true
}
func validateProtocol(out []byte, in [4][]byte) (wireRecord, error) {
	var w wireRecord
	bad := func() (wireRecord, error) { return wireRecord{}, ErrProtocol }
	if len(out) == 0 || len(out) > MaxOutputBytes {
		return bad()
	}
	line := bytes.TrimSuffix(out, []byte{'\n'})
	if bytes.ContainsAny(line, "\r\n") || len(line) == 0 || line[0] != '{' || line[len(line)-1] != '}' {
		return bad()
	}
	if !exactKeys(line, "schema", "profile", "proof_package", "lean_version", "source", "wasm", "arm", "rv", "declaration", "roots") {
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
	if w.Schema != Schema || w.Profile != Profile || w.ProofPackage != ProofPackage || w.LeanVersion != LeanVersion {
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
	if !identifierBytes(w.Declaration.Name) || !identifierBytes(w.Declaration.First) || !identifierBytes(w.Declaration.Second) {
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
		if !exactKeys(rawRoots[n], "name", "axioms") || r.Name != rootNames[n] || r.Axioms == nil {
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
func appendByteList(b *bytes.Buffer, input []byte) {
	b.WriteByte('[')
	for n, x := range input {
		if n != 0 {
			b.WriteByte(',')
		}
		b.WriteString(strconv.Itoa(int(x)))
	}
	b.WriteByte(']')
}
