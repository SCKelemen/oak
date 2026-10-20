package bitwisecheck

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"strings"
	"testing"
	"time"
)

func wireFixture(t *testing.T) ([]byte, [4][]byte) {
	t.Helper()
	in := fixture(t)
	ints := func(b []byte) wireBytes {
		out := make(wireBytes, len(b))
		for n, v := range b {
			out[n] = int(v)
		}
		return out
	}
	w := wireRecord{Schema: Schema, Profile: Profile, ProofPackage: ProofPackage, LeanVersion: LeanVersion, Source: ints(in[0]), Wasm: ints(in[1]), ARM: ints(in[2]), RV: ints(in[3]), Declaration: wireDeclaration{Name: ints([]byte("bitwise")), First: ints([]byte("x")), Second: ints([]byte("y")), Op: "and"}}
	for _, n := range rootNames {
		w.Roots = append(w.Roots, Root{Name: n, Axioms: []string{"propext", "Classical.choice", "Quot.sound"}})
	}
	out, e := json.Marshal(w)
	if e != nil {
		t.Fatal(e)
	}
	return out, in
}
func TestStrictProtocol(t *testing.T) {
	raw, in := wireFixture(t)
	// This exercises only parser logic. No synthetic record can mint a bundle.
	if _, e := validateProtocol(raw, in); e != nil {
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
		"wrong root":              strings.Replace(text, `Oak.CheckedBundleRequest.binding`, `Oak.CheckedBundleRequest.admitted`, 1),
		"wrong declaration":       strings.Replace(text, `"op":"and"`, `"op":"or"`, 1),
		"wrong profile":           strings.Replace(text, Profile, "anything", 1),
		"extra whitespace record": text + "\n\n",
	}
	for name, changed := range changes {
		t.Run(name, func(t *testing.T) {
			if changed == text {
				t.Fatal("ineffective mutation")
			}
			if _, e := validateProtocol([]byte(changed), in); !errors.Is(e, ErrProtocol) {
				t.Fatalf("accepted: %v", e)
			}
		})
	}
	if _, e := validateProtocol(bytes.Repeat([]byte{' '}, MaxOutputBytes+1), in); !errors.Is(e, ErrProtocol) {
		t.Fatal("oversize")
	}
}
func TestProcessRefusal(t *testing.T) {
	env := []string{"PATH=/nonexistent", "LANG=C"}
	dir := t.TempDir()
	for _, script := range []string{`printf '{"schema":"oak.checked-bundle.v1"}'; exit 1`, `printf success; printf diagnostic >&2`, `/usr/bin/head -c 65537 /dev/zero`, `/usr/bin/head -c 65537 /dev/zero >&2`} {
		if out, e := runProcess(context.Background(), dir, env, "/bin/sh", "-c", script); e == nil || out != nil {
			t.Fatal("process refusal failed")
		}
	}
	if _, e := runProcess(context.Background(), dir, env, "/definitely/missing/checker"); e == nil {
		t.Fatal("missing checker accepted")
	}
	ctx, cancel := context.WithTimeout(context.Background(), 25*time.Millisecond)
	defer cancel()
	if _, e := runProcess(ctx, dir, env, "/bin/sh", "-c", "/bin/sleep 30 & wait"); !errors.Is(e, context.DeadlineExceeded) {
		t.Fatalf("timeout: %v", e)
	}
}
