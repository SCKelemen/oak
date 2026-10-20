package bitwisecheck

import (
	"bytes"
	"encoding/binary"
	"errors"
	"fmt"
	"regexp"
	"strconv"
	"strings"
	"sync"
)

// The only input interpolation is unsigned numeric bytes, checked lengths and
// one of three fixed operation tokens. Source names are never Lean identifiers.
var imageSourceOnce sync.Once
var imageSourcePattern *regexp.Regexp

func imageSourceProposal(source []byte) (name, first, second []byte, op string, err error) {
	imageSourceOnce.Do(func() {
		imageSourcePattern = regexp.MustCompile(`^([A-Za-z][A-Za-z0-9]*): \(([A-Za-z][A-Za-z0-9]*): u32, ([A-Za-z][A-Za-z0-9]*): u32\): u32 = ([A-Za-z][A-Za-z0-9]*) ([&|^]) ([A-Za-z][A-Za-z0-9]*)\n$`)
	})
	m := imageSourcePattern.FindSubmatch(source)
	if m == nil || !bytes.Equal(m[2], m[4]) || !bytes.Equal(m[3], m[6]) {
		err = errors.New("bitwisecheck: unsupported original image source")
		return
	}
	if len(m[1]) > 256 {
		err = ErrBounds
		return
	}
	return m[1], m[2], m[3], map[string]string{"&": "and", "|": "or", "^": "xor"}[string(m[5])], nil
}

// Only the actual all-zero 120:4096 interval is compressed. A nonzero gap is
// refused, never rewritten. Header and suffix contain every actual input byte.
func imageParts(image []byte) ([]byte, []byte, error) {
	if len(image) < 4096 || len(image) > MaxImageBytes {
		return nil, nil, ErrBounds
	}
	for _, b := range image[120:4096] {
		if b != 0 {
			return nil, nil, errors.New("bitwisecheck: nonzero image header gap")
		}
	}
	return image[:120], image[4096:], nil
}
func imageDriver(in [4][]byte) ([]byte, error) {
	name, first, second, op, err := imageSourceProposal(in[0])
	if err != nil {
		return nil, err
	}
	for _, image := range in[2:] {
		if _, _, err = imageParts(image); err != nil {
			return nil, err
		}
	}
	var b bytes.Buffer
	b.WriteString("import Oak.BitwiseSourceImageParityAudit\nset_option autoImplicit false\nset_option linter.unusedSimpArgs false\nset_option maxRecDepth 16384\nset_option maxHeartbeats 3200000\nnamespace Oak.SourceImageParityRequest\nopen Oak.BitwiseSourceImageParity Oak.NativeBitwiseImage\nopen Oak.NativeBitwiseObject (fromUInt8)\nopen Oak.MinimalELF (Bytes readLE slice)\n")
	b.WriteString(imageDriverSupport)
	for n, key := range []string{"source", "wasm"} {
		b.WriteString("def " + key + " : List UInt8 := ")
		appendByteList(&b, in[n])
		b.WriteByte('\n')
	}
	for n, key := range []string{"armData", "rvData"} {
		renderImageProof(&b, key, []string{"arm64", "rv64"}[n], op, name, in[n+2])
	}
	b.WriteString("def arm : Bytes := armData.image\ndef rv : Bytes := rvData.image\ndef declaration : Oak.BitwiseSource.Decl := (Oak.BitwiseSource.parse source).getD ⟨[], [], [], .and⟩\n")
	var d bytes.Buffer
	d.WriteString("(⟨")
	for n, part := range [][]byte{name, first, second} {
		if n != 0 {
			d.WriteByte(',')
		}
		appendByteList(&d, part)
	}
	d.WriteString(",." + op + "⟩ : Oak.BitwiseSource.Decl)")
	b.WriteString("private theorem parsed : Oak.BitwiseSource.parse source = some " + d.String() + " := by decide +kernel\n")
	b.WriteString("private theorem wasm_good : Oak.BitwiseModule.acceptsModule .wasm .wasmLocals [32,32] 32 ." + op + " ")
	appendByteList(&b, name)
	b.WriteString(" wasm = true := by decide +kernel\n")
	b.WriteString("theorem admitted : Oak.BitwiseSourceImageParity.check source wasm arm rv = some declaration := by\n  have declared : declaration = " + d.String() + " := by\n    unfold declaration\n    rw [parsed]\n    rfl\n  rw [declared]\n  exact check_of_artifacts parsed wasm_good armData.accepted rvData.accepted\n")
	b.WriteString("theorem binding : type_of% (accepted_source_image_binding admitted) := accepted_source_image_binding admitted\ntheorem all_inputs : type_of% (accepted_all_input_success admitted) := accepted_all_input_success admitted\nend Oak.SourceImageParityRequest\n#oak_source_image_parity_audit\n")
	if b.Len() > MaxDriverBytes {
		return nil, ErrBounds
	}
	return b.Bytes(), nil
}
func renderImageProof(b *bytes.Buffer, namespace, machine, op string, name, image []byte) {
	header, suffix, _ := imageParts(image) // checked before writing any request
	b.WriteString("namespace " + namespace + "\ndef nameBytes : Bytes := ")
	appendByteList(b, name)
	b.WriteString("\ndef header : Bytes := ")
	appendByteList(b, header)
	b.WriteString("\ndef suffix : Bytes := ")
	appendByteList(b, suffix)
	b.WriteString("\ndef image : Bytes := header ++ (List.replicate 3976 0 ++ suffix)\nprivate theorem header_length : header.length = 120 := by decide +kernel\n")
	fmt.Fprintf(b, "private theorem image_length : image.length = %d := by\n  change (header ++ (List.replicate 3976 0 ++ suffix)).length = %d\n  rw [List.length_append, List.length_append, List.length_replicate, header_length]\n  decide +kernel\n", len(image), len(image))
	b.WriteString("private theorem h40 : readLE image 40 8 = " + strconv.FormatUint(binary.LittleEndian.Uint64(header[40:48]), 10) + " := by decide +kernel\nprivate theorem h58 : readLE image 58 2 = 64 := by decide +kernel\nprivate theorem h60 : readLE image 60 2 = 6 := by decide +kernel\n")
	b.WriteString("private theorem read_tail (offset count : Nat) (bound : 4096 ≤ offset) : readLE image offset count = readLE suffix (offset-4096) count := padded_tail_read header suffix header_length offset count bound\nprivate theorem slice_tail (offset count : Nat) (bound : 4096 ≤ offset) : slice image offset count = slice suffix (offset-4096) count := padded_tail_slice header suffix header_length offset count bound\n")
	expected := "(fromUInt8 (Oak.AArch64BitwiseFunction.functionBytes ." + op + "))"
	if machine == "rv64" {
		expected = "(Oak.RiscVFramedBitwise.functionBytes ." + op + ")"
	}
	atoms := func(n int) []string {
		out := make([]string, n)
		for i := range out {
			out[i] = "?_"
		}
		return out
	}
	pair := func(parts []string) string { return "⟨" + strings.Join(parts, ",") + "⟩" }
	headerAtoms := append([]string{pair(atoms(11))}, atoms(5)...)
	layout := atoms(12)
	layout[5] = "(zero_gap header suffix header_length)"
	profile := pair([]string{pair(headerAtoms), pair(atoms(2)), pair(atoms(6)), pair(atoms(6)), pair(layout)})
	b.WriteString("theorem accepted : Oak.NativeBitwiseImage.accepts ." + machine + " nameBytes image " + expected + " = true := by\n  refine accepts_of_profile " + profile + " ?_\n")
	b.WriteString("  all_goals (try simp only [Oak.NativeBitwiseObject.readSection, Oak.NativeBitwiseObject.readSymbol, Oak.NativeBitwiseObject.symbolName, Oak.MinimalELF.segment, textSection, dataSection, symSection, strSection, shstrSection, functionSymbol, startSymbol, nullSection, nullSymbol, image_length, h40, h58, h60]); (try simp (disch := decide) only [read_tail, slice_tail]); all_goals decide +kernel\nend " + namespace + "\n")
}

const imageDriverSupport = `
private theorem slice_after (pre suffix : Bytes) (offset count : Nat)
    (bound : pre.length ≤ offset) :
    slice (pre ++ suffix) offset count = slice suffix (offset-pre.length) count := by
  unfold slice
  rw [List.drop_append, List.drop_eq_nil_of_le bound, List.nil_append]

private theorem padded_tail_slice (header suffix : Bytes) (hlen : header.length = 120)
    (offset count : Nat) (bound : 4096 ≤ offset) :
    slice (header ++ (List.replicate 3976 0 ++ suffix)) offset count =
      slice suffix (offset-4096) count := by
  have plen : (header ++ List.replicate 3976 (0 : BitVec 8)).length = 4096 := by
    rw [List.length_append, hlen, List.length_replicate]
  rw [← List.append_assoc]
  have hbound : (header ++ List.replicate 3976 (0 : BitVec 8)).length ≤ offset := by
    rw [plen]
    exact bound
  simpa only [plen] using slice_after (header ++ List.replicate 3976 0) suffix offset count hbound

private theorem padded_tail_read (header suffix : Bytes) (hlen : header.length = 120)
    (offset count : Nat) (bound : 4096 ≤ offset) :
    readLE (header ++ (List.replicate 3976 0 ++ suffix)) offset count =
      readLE suffix (offset-4096) count := by
  unfold readLE
  rw [padded_tail_slice header suffix hlen offset count bound]
private theorem zero_gap (header tail : Bytes) (length : header.length = 120) :
    Oak.MinimalELF.slice (header ++ (List.replicate 3976 0 ++ tail)) 120 3976 = List.replicate 3976 0 := by
  unfold Oak.MinimalELF.slice
  rw [List.drop_left' length]
  exact List.take_left' List.length_replicate

private theorem accepts_of_profile {m : Oak.MinimalELF.Machine} {name image expectedBody : Bytes}
    (profile : StrictProfile m name image)
    (body : Oak.MinimalELF.slice image (bodyOffset m) (bodySize m) = expectedBody) :
    Oak.NativeBitwiseImage.accepts m name image expectedBody = true := by
  simp only [Oak.NativeBitwiseImage.accepts,Oak.NativeBitwiseImage.extract,if_pos profile,Oak.NativeBitwiseImage.profile_decodes profile,Oak.NativeBitwiseImage.candidate,decide_eq_true_eq]
  exact body

`
