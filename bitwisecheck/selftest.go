package bitwisecheck

import (
	"bytes"
	"context"
	"embed"
	"errors"
)

// These small complete production artifacts are controls, not proof source and
// not a success cache. Every installation proves and audits them from scratch.
//
//go:embed testdata/source.fixture testdata/wasm.fixture testdata/arm.fixture testdata/rv.fixture
var selfTestFiles embed.FS

func (i *Installation) selfTest(ctx context.Context) error {
	var in [4][]byte
	for n, name := range []string{"source.fixture", "wasm.fixture", "arm.fixture", "rv.fixture"} {
		b, err := selfTestFiles.ReadFile("testdata/" + name)
		if err != nil {
			return err
		}
		in[n] = b
	}
	if _, err := i.CheckBundle(ctx, in[0], in[1], in[2], in[3]); err != nil {
		return err
	}
	// Prove actual refusal, rather than treating a timeout/OOM/process failure as
	// a successful negative control. Only a silent successful kernel run passes.
	in[0] = bytes.Replace(in[0], []byte(" & "), []byte(" | "), 1)
	return i.state.proveRefusal(ctx, in)
}

// proveRefusal is a control only: it never constructs admission authority.
func (s *installationState) proveRefusal(ctx context.Context, in [4][]byte) error {
	generated, err := driver(in)
	if err != nil {
		return err
	}
	prefix, _, ok := bytes.Cut(generated, []byte("theorem admitted :"))
	if !ok {
		return errors.New("missing self-test template boundary")
	}
	negative := append(prefix, []byte("theorem refused : Oak.BitwiseSourceObjectParity.check source wasm arm rv = none := by decide +kernel\nend Oak.CheckedBundleRequest\n")...)
	ctx, cancel := context.WithTimeout(ctx, RequestTimeout)
	defer cancel()
	out, err := s.runRequest(ctx, negative)
	if err != nil {
		return err
	}
	if len(out) != 0 {
		return errors.New("unexpected refusal-control output")
	}
	return nil
}
