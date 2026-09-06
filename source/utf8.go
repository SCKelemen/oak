package source

// ValidateUTF8 reports whether text is valid UTF-8 per the well-formed byte
// sequences of the Unicode standard (Table 3-7). On failure it returns the
// byte offset of the first invalid sequence. It is maintained as a
// line-for-line transliteration of the sequence brackets proven in
// spec/lean/Oak/Utf8Validity.lean (Oak.Utf8Validity.Seq): truncated
// sequences, stray continuations, overlong encodings, surrogates, and values
// above U+10FFFF are all rejected — validation fails closed.
//
// This is the source-decoder validation of docs/spec/70-strings.md section 8:
// string literals inherit their validity from the file having been validated
// here, so no safe construction path can carry invalid bytes into `string`.
func ValidateUTF8(text string) (int, bool) {
	i := 0
	n := len(text)
	for i < n {
		b0 := text[i]
		switch {
		case b0 <= 0x7F:
			i++
		case 0xC2 <= b0 && b0 <= 0xDF:
			if i+1 >= n || !isContinuation(text[i+1]) {
				return i, false
			}
			i += 2
		case b0 == 0xE0:
			// 0xA0 lower bound excludes overlong encodings.
			if i+2 >= n || text[i+1] < 0xA0 || text[i+1] > 0xBF || !isContinuation(text[i+2]) {
				return i, false
			}
			i += 3
		case 0xE1 <= b0 && b0 <= 0xEC:
			if i+2 >= n || !isContinuation(text[i+1]) || !isContinuation(text[i+2]) {
				return i, false
			}
			i += 3
		case b0 == 0xED:
			// 0x9F upper bound excludes surrogates U+D800..U+DFFF.
			if i+2 >= n || text[i+1] < 0x80 || text[i+1] > 0x9F || !isContinuation(text[i+2]) {
				return i, false
			}
			i += 3
		case 0xEE <= b0 && b0 <= 0xEF:
			if i+2 >= n || !isContinuation(text[i+1]) || !isContinuation(text[i+2]) {
				return i, false
			}
			i += 3
		case b0 == 0xF0:
			// 0x90 lower bound excludes overlong encodings.
			if i+3 >= n || text[i+1] < 0x90 || text[i+1] > 0xBF ||
				!isContinuation(text[i+2]) || !isContinuation(text[i+3]) {
				return i, false
			}
			i += 4
		case 0xF1 <= b0 && b0 <= 0xF3:
			if i+3 >= n || !isContinuation(text[i+1]) ||
				!isContinuation(text[i+2]) || !isContinuation(text[i+3]) {
				return i, false
			}
			i += 4
		case b0 == 0xF4:
			// 0x8F upper bound excludes values above U+10FFFF.
			if i+3 >= n || text[i+1] < 0x80 || text[i+1] > 0x8F ||
				!isContinuation(text[i+2]) || !isContinuation(text[i+3]) {
				return i, false
			}
			i += 4
		default:
			// 0x80..0xC1 (stray continuations, overlong leads) and
			// 0xF5..0xFF (beyond U+10FFFF) have no well-formed sequence.
			return i, false
		}
	}
	return -1, true
}

func isContinuation(b byte) bool { return 0x80 <= b && b <= 0xBF }
