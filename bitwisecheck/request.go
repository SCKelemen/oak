package bitwisecheck

import (
	"bytes"
	"context"
	"errors"
	"os"
	"path/filepath"
)

func (i *Installation) Valid() bool {
	if i == nil || i.state == nil || i.state.authority != installationSeal {
		return false
	}
	i.state.mu.Lock()
	defer i.state.mu.Unlock()
	return !i.state.closed
}
func requestInput(source, wasm, arm, rv []byte) ([4][]byte, error) {
	var in [4][]byte
	for n, b := range [][]byte{source, wasm, arm, rv} {
		max := MaxObjectBytes
		if n == 0 {
			max = MaxSourceBytes
		}
		if n == 1 {
			max = MaxWasmBytes
		}
		if len(b) == 0 || len(b) > max {
			return in, ErrBounds
		}
	}
	// Callers must not write concurrently during this synchronous snapshot, just
	// as for other Go slice APIs. Mutations after the snapshot cannot affect it.
	for n, b := range [][]byte{source, wasm, arm, rv} {
		in[n] = append([]byte(nil), b...)
	}
	return in, nil
}
func driver(in [4][]byte) ([]byte, error) {
	var b bytes.Buffer
	b.WriteString("import Oak.CheckedBundleAudit\nset_option autoImplicit false\nset_option maxRecDepth 8192\nset_option maxHeartbeats 1600000\nnamespace Oak.CheckedBundleRequest\n")
	for n, name := range []string{"source", "wasm", "arm", "rv"} {
		typ := "List UInt8"
		if n > 1 {
			typ = "Oak.MinimalELF.Bytes"
		}
		b.WriteString("def " + name + " : " + typ + " := ")
		appendByteList(&b, in[n])
		b.WriteByte('\n')
	}
	b.WriteString("def declaration : Oak.BitwiseSource.Decl := (Oak.BitwiseSource.parse source).getD ⟨[], [], [], .and⟩\ntheorem admitted : Oak.BitwiseSourceObjectParity.check source wasm arm rv = some declaration := by decide +kernel\ntheorem binding : type_of% (Oak.BitwiseSourceObjectParity.accepted_source_object_binding admitted) := Oak.BitwiseSourceObjectParity.accepted_source_object_binding admitted\ntheorem all_inputs : type_of% (Oak.BitwiseSourceObjectParity.accepted_all_input_success admitted) := Oak.BitwiseSourceObjectParity.accepted_all_input_success admitted\nend Oak.CheckedBundleRequest\n#oak_checked_bundle_audit\n")
	if b.Len() > MaxDriverBytes {
		return nil, ErrBounds
	}
	return b.Bytes(), nil
}

// CheckBundle independently checks all four exact owned byte snapshots together.
// Requests are serialized per installation. Context cancellation, Close, output
// overflow, proof failure, malformed output, or unsuccessful process exit return
// no bundle. Lean receives a 4096 MiB allocator budget and one worker; this is
// not a promise of a 4 GiB total host RSS/virtual-memory sandbox.
func (i *Installation) CheckBundle(ctx context.Context, source, wasm, arm, rv []byte) (*CheckedBundle, error) {
	if ctx == nil {
		return nil, errors.New("bitwisecheck: nil context")
	}
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	if !i.Valid() {
		return nil, ErrInvalidInstallation
	}
	in, err := requestInput(source, wasm, arm, rv)
	if err != nil {
		return nil, err
	}
	generated, err := driver(in)
	if err != nil {
		return nil, err
	}
	s := i.state
	ctx, cancel := context.WithTimeout(ctx, RequestTimeout)
	defer cancel()
	stop := context.AfterFunc(s.ctx, cancel)
	defer stop()
	select {
	case s.gate <- struct{}{}:
		defer func() { <-s.gate }()
	case <-ctx.Done():
		return nil, ctx.Err()
	}
	if !i.Valid() {
		return nil, ErrInvalidInstallation
	}
	if err = ctx.Err(); err != nil {
		return nil, err
	}
	out, err := s.runRequest(ctx, generated)
	if err != nil {
		return nil, err
	}

	record, err := validateProtocol(out, in)
	if err != nil {
		return nil, err
	}
	// This lock is the admission/Close linearization point. Cancellation after a
	// completed success does not retroactively change that historical result.
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.closed {
		return nil, ErrInvalidInstallation
	}
	if err = ctx.Err(); err != nil {
		return nil, err
	}
	sealed := [4]string{string(in[0]), string(in[1]), string(in[2]), string(in[3])}
	return &CheckedBundle{authority: bundleSeal, source: sealed[0], wasm: sealed[1], arm: sealed[2], rv: sealed[3], receipt: makeReceipt(record, sealed, s.sourceHash)}, nil
}

func (s *installationState) runRequest(ctx context.Context, generated []byte) ([]byte, error) {
	request, err := os.MkdirTemp(s.root, "request-")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(request)
	file := filepath.Join(request, "Request.lean")
	if err = os.WriteFile(file, generated, 0600); err != nil {
		return nil, err
	}
	return runLeanProcess(ctx, request, s.environment(), s.lean, "-j1", "-M4096", "--trust=0", file)
}
