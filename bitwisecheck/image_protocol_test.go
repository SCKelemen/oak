package bitwisecheck

import (
	"bytes"
	"encoding/json"
	"errors"
	"strings"
	"testing"
)

func imageWireFixture(t *testing.T) ([]byte, [4][]byte) {
	t.Helper()
	in := imageFixture(t)
	ints := func(b []byte) wireBytes {
		out := make(wireBytes, len(b))
		for n, v := range b {
			out[n] = int(v)
		}
		return out
	}
	w := imageWireRecord{Schema: imageAuditSchema, Profile: ImageProfile, LeanVersion: LeanVersion, Source: ints(in[0]), Wasm: imageWasmBytes(ints(in[1])), ARM: imageWireBytes(ints(in[2])), RV: imageWireBytes(ints(in[3])), Declaration: wireDeclaration{Name: ints([]byte("mix")), First: ints([]byte("a")), Second: ints([]byte("b")), Op: "and"}}
	for _, n := range imageRootNames {
		w.Roots = append(w.Roots, Root{Name: n, Axioms: []string{"propext", "Classical.choice", "Quot.sound"}})
	}
	out, e := json.Marshal(w)
	if e != nil {
		t.Fatal(e)
	}
	return out, in
}
func TestImageStrictProtocol(t *testing.T) {
	raw, in := imageWireFixture(t)
	// This exercises only parser logic. No synthetic record can mint a bundle.
	if _, e := validateImageProtocol(raw, in); e != nil {
		t.Fatal(e)
	}
	text := string(raw)
	changes := map[string]string{
		"leading log": "success\n" + text, "trailing log": text + "\nsuccess", "two records": text + "\n" + text, "truncated": text[:len(text)-1],
		"unknown field":           strings.Replace(text, `"schema":`, `"extra":0,"schema":`, 1),
		"duplicate field":         strings.Replace(text, `"schema":`, `"schema":"ignored","schema":`, 1),
		"duplicate nested":        strings.Replace(text, `"op":"and"`, `"op":"xor","op":"and"`, 1),
		"missing field":           strings.Replace(text, `"lean_version":"4.33.1",`, "", 1),
		"wrong version":           strings.Replace(text, `"lean_version":"4.33.1"`, `"lean_version":"4.0.0"`, 1),
		"null byte":               strings.Replace(text, `"wasm":[0,`, `"wasm":[null,`, 1),
		"negative byte":           strings.Replace(text, `"wasm":[0,`, `"wasm":[-1,`, 1),
		"float byte":              strings.Replace(text, `"wasm":[0,`, `"wasm":[0.0,`, 1),
		"oversized byte":          strings.Replace(text, `"wasm":[0,`, `"wasm":[256,`, 1),
		"wrong echo":              strings.Replace(text, `"wasm":[0,`, `"wasm":[1,`, 1),
		"axiom null":              strings.Replace(text, `"axioms":["propext","Classical.choice","Quot.sound"]`, `"axioms":null`, 1),
		"forbidden axiom":         strings.Replace(text, `"propext"`, `"sorryAx"`, 1),
		"duplicate axiom":         strings.Replace(text, `"Quot.sound"`, `"Classical.choice"`, 1),
		"unsorted axioms":         strings.Replace(text, `"Classical.choice","Quot.sound"`, `"Quot.sound","Classical.choice"`, 1),
		"wrong root":              strings.Replace(text, `Oak.SourceImageParityRequest.binding`, `Oak.SourceImageParityRequest.admitted`, 1),
		"wrong declaration":       strings.Replace(text, `"op":"and"`, `"op":"or"`, 1),
		"spaced record":           strings.Replace(text, `"schema":`, `"schema": `, 1),
		"wrong schema":            strings.Replace(text, imageAuditSchema, Schema, 1),
		"object proof field":      strings.Replace(text, `"schema":`, `"proof_package":"old","schema":`, 1),
		"string byte":             strings.Replace(text, `"wasm":[0,`, `"wasm":["0",`, 1),
		"exponent byte":           strings.Replace(text, `"wasm":[0,`, `"wasm":[0e0,`, 1),
		"image byte null":         strings.Replace(text, `"arm":[127,`, `"arm":[null,`, 1),
		"wrong profile":           strings.Replace(text, ImageProfile, "anything", 1),
		"extra whitespace record": text + "\n\n",
	}
	for name, changed := range changes {
		t.Run(name, func(t *testing.T) {
			if changed == text {
				t.Fatal("ineffective mutation")
			}
			if _, e := validateImageProtocol([]byte(changed), in); !errors.Is(e, ErrProtocol) {
				t.Fatalf("accepted: %v", e)
			}
		})
	}
	if _, e := validateImageProtocol(bytes.Repeat([]byte{' '}, MaxOutputBytes+1), in); !errors.Is(e, ErrProtocol) {
		t.Fatal("oversize")
	}
}

func TestImageProtocolFieldLimits(t *testing.T) {
	raw, in := imageWireFixture(t)
	var obj map[string]json.RawMessage
	if e := json.Unmarshal(raw, &obj); e != nil {
		t.Fatal(e)
	}
	for field, limit := range map[string]int{"source": MaxSourceBytes, "wasm": MaxWasmBytes, "arm": MaxImageBytes, "rv": MaxImageBytes} {
		t.Run(field, func(t *testing.T) {
			original := obj[field]
			defer func() { obj[field] = original }()
			values := make([]int, limit+1)
			obj[field], _ = json.Marshal(values)
			bad, _ := json.Marshal(obj)
			if _, e := validateImageProtocol(bad, in); !errors.Is(e, ErrProtocol) {
				t.Fatal("oversized field")
			}
		})
	}
	// The old object decoder must never inherit the larger image byte limit.
	var old wireBytes
	if e := json.Unmarshal([]byte("["+strings.Repeat("0,", MaxObjectBytes)+"0]"), &old); e == nil {
		t.Fatal("old object bound widened")
	}
}
func TestImageMaximumProtocolSize(t *testing.T) {
	// Three-digit ASCII bytes maximize decimal rendering at the field bounds.
	name, first, second := strings.Repeat("z", 256), strings.Repeat("x", 441), strings.Repeat("y", 441)
	source := []byte(name + ": (" + first + ": u32, " + second + ": u32): u32 = " + first + " & " + second + "\n")
	if len(source) != MaxSourceBytes {
		t.Fatalf("source length %d", len(source))
	}
	in := [4][]byte{source, bytes.Repeat([]byte{255}, MaxWasmBytes), bytes.Repeat([]byte{255}, MaxImageBytes), bytes.Repeat([]byte{255}, MaxImageBytes)}
	ints := func(b []byte) []int {
		out := make([]int, len(b))
		for n, v := range b {
			out[n] = int(v)
		}
		return out
	}
	w := imageWireRecord{Schema: imageAuditSchema, Profile: ImageProfile, LeanVersion: LeanVersion, Source: ints(in[0]), Wasm: ints(in[1]), ARM: ints(in[2]), RV: ints(in[3]), Declaration: wireDeclaration{Name: ints([]byte(name)), First: ints([]byte(first)), Second: ints([]byte(second)), Op: "and"}}
	for _, n := range imageRootNames {
		w.Roots = append(w.Roots, Root{Name: n, Axioms: []string{"propext", "Classical.choice", "Quot.sound"}})
	}
	raw, e := json.Marshal(w)
	if e != nil {
		t.Fatal(e)
	}
	if len(raw) > MaxOutputBytes {
		t.Fatal("max output bound")
	}
	if _, e = validateImageProtocol(raw, in); e != nil {
		t.Fatal(e)
	}
	// This is parser-only synthetic data. It never constructs a capability.
	t.Logf("maximum field-bound numeric protocol bytes=%d (cap %d)", len(raw), MaxOutputBytes)
	// Actual input compression validates the bytes before rendering them.
	for n := 2; n < 4; n++ {
		copy(in[n][120:4096], make([]byte, 3976))
	}
	d, e := imageDriver(in)
	if e != nil {
		t.Fatal(e)
	}
	t.Logf("maximum field-bound driver bytes=%d (cap %d)", len(d), MaxDriverBytes)
}
