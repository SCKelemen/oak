package bitwisecheck

import (
	"bytes"
	"context"
	"embed"
	"errors"
)

// Complete actual production images. These are controls only; each fresh
// installation proves and audits the actual four bytestrings again.
//
//go:embed testdata/image-source.fixture testdata/image-wasm.fixture testdata/image-arm.fixture testdata/image-rv.fixture
var imageSelfTestFiles embed.FS

func imageSelfTestInput() ([4][]byte, error) {
	var in [4][]byte
	for n, name := range []string{"image-source.fixture", "image-wasm.fixture", "image-arm.fixture", "image-rv.fixture"} {
		b, err := imageSelfTestFiles.ReadFile("testdata/" + name)
		if err != nil {
			return in, err
		}
		in[n] = b
	}
	return in, nil
}
func (i *ImageInstallation) selfTest(ctx context.Context) error {
	in, err := imageSelfTestInput()
	if err != nil {
		return err
	}
	if _, err = i.CheckImageBundle(ctx, in[0], in[1], in[2], in[3]); err != nil {
		return err
	}
	// Actual Wasm trailing-byte refusal must compile silently and successfully;
	// timeout, OOM, process error or mere failure to admit never passes a control.
	in[1] = append(in[1], 0)
	generated, err := imageRefusalDriver(in)
	if err != nil {
		return err
	}
	ctx, release, err := i.state.beginRequest(ctx)
	if err != nil {
		return err
	}
	defer release()
	out, err := i.state.runRequest(ctx, generated)
	if err != nil {
		return err
	}
	if len(out) != 0 {
		return errors.New("bitwisecheck: unexpected image refusal-control output")
	}
	return nil
}

// A fixed negative control, never a source of successful capability authority.
func imageRefusalDriver(in [4][]byte) ([]byte, error) {
	var b bytes.Buffer
	b.WriteString("import Oak.BitwiseSourceImageParityAudit\nset_option autoImplicit false\nset_option maxRecDepth 16384\nset_option maxHeartbeats 3200000\nnamespace Oak.SourceImageParityRequest\n")
	for n, name := range []string{"source", "wasm", "arm", "rv"} {
		typ := "List UInt8"
		if n > 1 {
			typ = "Oak.MinimalELF.Bytes"
		}
		b.WriteString("def " + name + " : " + typ + " := ")
		if n < 2 {
			appendByteList(&b, in[n])
		} else {
			header, suffix, err := imageParts(in[n])
			if err != nil {
				return nil, err
			}
			b.WriteByte('(')
			appendByteList(&b, header)
			b.WriteString(" ++ (List.replicate 3976 0 ++ ")
			appendByteList(&b, suffix)
			b.WriteString("))")
		}
		b.WriteByte('\n')
	}
	b.WriteString("def declaration : Oak.BitwiseSource.Decl := (Oak.BitwiseSource.parse source).getD ⟨[], [], [], .and⟩\ntheorem refused : Oak.BitwiseSourceImageParity.check source wasm arm rv = none := by\n  exact Oak.BitwiseSourceImageParity.refuses_failed_artifact (d := declaration) (by decide +kernel) (Or.inl (by decide +kernel))\nend Oak.SourceImageParityRequest\n")
	if b.Len() > MaxDriverBytes {
		return nil, ErrBounds
	}
	return b.Bytes(), nil
}
