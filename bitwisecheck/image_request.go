package bitwisecheck

import (
	"context"
	"errors"
)

func imageRequestInput(source, wasm, arm, rv []byte) ([4][]byte, error) {
	var owned [4][]byte
	inputs := [4][]byte{source, wasm, arm, rv}
	limits := [4]int{MaxSourceBytes, MaxWasmBytes, MaxImageBytes, MaxImageBytes}
	for n, b := range inputs {
		if len(b) == 0 || len(b) > limits[n] {
			return owned, ErrBounds
		}
	}
	// The caller must not concurrently mutate slices during this synchronous copy.
	for n, b := range inputs {
		owned[n] = append([]byte(nil), b...)
	}
	return owned, nil
}

// CheckImageBundle checks the exact original source, complete Wasm module and
// complete ARM64/RV64 executable images together under the pinned Lean kernel.
// This proves bounded named-function local invocation under explicit model and
// ABI/frame premises. It makes no OS startup, hardware or whole-language claim.
// Requests use one Lean worker and -M4096; this is not a host RSS sandbox.
func (i *ImageInstallation) CheckImageBundle(ctx context.Context, source, wasm, armImage, rvImage []byte) (*CheckedImageBundle, error) {
	if ctx == nil {
		return nil, errors.New("bitwisecheck: nil context")
	}
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	if !i.Valid() {
		return nil, ErrInvalidInstallation
	}
	in, err := imageRequestInput(source, wasm, armImage, rvImage)
	if err != nil {
		return nil, err
	}
	generated, err := imageDriver(in)
	if err != nil {
		return nil, err
	}
	s := i.state
	ctx, release, err := s.beginRequest(ctx)
	if err != nil {
		return nil, err
	}
	defer release()
	out, err := s.runRequest(ctx, generated)
	if err != nil {
		return nil, err
	}
	record, err := validateImageProtocol(out, in)
	if err != nil {
		return nil, err
	}
	// No stdout can seal authority before successful process exit. This lock is
	// the admission/Close linearization point, as with completed object admission.
	s.mu.Lock()
	defer s.mu.Unlock()
	if s.closed {
		return nil, ErrInvalidInstallation
	}
	if err = ctx.Err(); err != nil {
		return nil, err
	}
	sealed := [4]string{string(in[0]), string(in[1]), string(in[2]), string(in[3])}
	return &CheckedImageBundle{authority: imageBundleSeal, source: sealed[0], wasm: sealed[1], arm: sealed[2], rv: sealed[3], receipt: makeImageReceipt(record, sealed, s.sourceHash)}, nil
}
