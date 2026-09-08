package compiler

import (
	"fmt"
	"strconv"
	"strings"
)

func codecU64Literal(value uint64) string {
	if value <= 9223372036854775807 {
		return fmt.Sprintf("u64(%d)", value)
	}
	return fmt.Sprintf("(u64(%d) * u64(4294967296) + u64(%d))", value>>32, value&4294967295)
}

// Decoder helpers return concrete values plus offsets, not a token tree or
// borrowed aggregate. Recursive calls follow the statically bounded schema.
func (d *codecDeriver) deriveDecoder(typ string) error {
	if d.decodeGenerated == nil {
		d.decodeGenerated = map[string]bool{}
		d.decodeActive = map[string]bool{}
	}
	if d.decodeGenerated[typ] {
		return nil
	}
	if d.decodeActive[typ] {
		return fmt.Errorf("codec: recursive decoder type %s is unsupported", typ)
	}
	d.decodeActive[typ] = true
	defer delete(d.decodeActive, typ)
	if typ == "string" {
		return fmt.Errorf("codec: borrowed string decoding requires storage and lifetime contracts; use json_string_decode with caller storage")
	}
	for _, operation := range []string{"read", "decode"} {
		if d.names[codecName(operation, typ)] {
			return fmt.Errorf("codec: generated name %s conflicts with a declaration", codecName(operation, typ))
		}
	}
	var body strings.Builder
	primitive, _ := codecPrimitive(typ)
	switch primitive {
	case "u64", "i64":
		bits, _ := strconv.Atoi(typ[1:])
		body.WriteString("raw: JsonIntegerScan = json_scan_integer(src, offset)\nnegative: Bool = raw.status == u32(1)\nraw.status > u32(1) ? { .Err(json_decode_error(raw.status - u32(1))) } | {\n")
		if primitive == "u64" {
			maximum := ^uint64(0)
			if bits < 64 {
				maximum = (uint64(1) << bits) - 1
			}
			fmt.Fprintf(&body, "negative ? { .Err(.TypeMismatch) } | raw.magnitude > %s ? { .Err(.NumericOverflow) } | {\n", codecU64Literal(maximum))
			conversion := "raw.magnitude"
			if bits < 64 {
				conversion = typ + "_trunc_u64(raw.magnitude)"
			}
			fmt.Fprintf(&body, "item: JsonDecoded[%s]\nitem.value = %s\nitem.next = raw.next\n.Ok(item)\n}\n", typ, conversion)
		} else {
			negativeMax := uint64(1) << (bits - 1)
			fmt.Fprintf(&body, "limit: u64 = negative ? %s | %s\nraw.magnitude > limit ? { .Err(.NumericOverflow) } | {\n", codecU64Literal(negativeMax), codecU64Literal(negativeMax-1))
			body.WriteString("number: i64 = i64(0)\nnegative && raw.magnitude > u64(0) ? { number = i64(0) - i64_bits_u64(raw.magnitude - u64(1)) - i64(1) } | { number = i64_bits_u64(raw.magnitude) }\n")
			conversion := "number"
			if bits < 64 {
				conversion = typ + "_trunc_i64(number)"
			}
			fmt.Fprintf(&body, "item: JsonDecoded[%s]\nitem.value = %s\nitem.next = raw.next\n.Ok(item)\n}\n", typ, conversion)
		}
		body.WriteString("}\n")
	case "bool":
		body.WriteString("part: JsonToken = json_token(src, offset)\npart.kind <= u32(1) ? { .Err(.InvalidSyntax) } | part.kind != u32(8) && part.kind != u32(9) ? { .Err(.TypeMismatch) } | {\nitem: JsonDecoded[Bool]\nitem.value = part.kind == u32(8)\nitem.next = part.end\n.Ok(item)\n}\n")
	default:
		fields, err := d.fields(typ)
		if err != nil {
			return err
		}
		for _, field := range fields {
			if err := d.deriveDecoder(field.typ); err != nil {
				return fmt.Errorf("codec field %s.%s: %w", typ, field.name, err)
			}
		}
		body.WriteString("opening: JsonToken = json_token(src, offset)\nopening.kind <= u32(1) ? { .Err(.InvalidSyntax) } | opening.kind != u32(2) ? { .Err(.TypeMismatch) } | {\n")
		fmt.Fprintf(&body, "value: %s\nat: u32 = opening.end\nstatus: u32 = 0\ndone: Bool = false\n", typ)
		for i, field := range fields {
			// Key bytes live in fixed local arrays. Their views never escape;
			// callers cannot mutate a generated global and change the schema.
			fmt.Fprintf(&body, "seen%d: Bool = false\nkey%d_data: [%d]u8\n", i, i, len(field.wire))
			for j, b := range []byte(field.wire) {
				fmt.Fprintf(&body, "key%d_data[%d] = u8(%d)\n", i, j, b)
			}
			fmt.Fprintf(&body, "key%d: []u8 = view(&key%d_data)\n", i, i)
		}
		body.WriteString("first: u32 = json_skip_space(src, at)\nfirst < len(src) && src[first] == u8(125) ? { done = true\nat = first + u32(1)\n}\nwhile !done && status == u32(0) {\nat = json_skip_space(src, at)\nkey: JsonToken\nfield_index: u32 = 0\n")
		// Match bounded literal spellings directly. Escaped and unusual keys
		// retain the full tokenizer and Unicode comparison path.
		for i, field := range fields {
			literal := []byte("\"" + field.wire + "\"")
			plain := len(literal) <= 34
			for _, b := range []byte(field.wire) {
				plain = plain && b >= 32 && b < 127 && b != '\\' && b != '"'
			}
			if !plain {
				continue
			}
			fmt.Fprintf(&body, "len(src) - at >= u32(%d)", len(literal))
			for j, b := range literal {
				fmt.Fprintf(&body, " && src[at + u32(%d)] == u8(%d)", j, b)
			}
			fmt.Fprintf(&body, " ? { field_index = u32(%d)\nkey = JsonToken { kind: u32(6), start: at, end: at + u32(%d) }\n} | ", i+1, len(literal))
		}
		body.WriteString("true ? {\nkey = json_token(src, at)\n")
		for i := range fields {
			fmt.Fprintf(&body, "json_key_equal(src, key, key%d) ? { field_index = u32(%d) } | ", i, i+1)
		}
		body.WriteString("{}\n}\nkey.kind != u32(6) ? { status = u32(2) } | {\ncolon_at: u32 = json_skip_space(src, key.end)\ncolon: JsonToken = JsonToken { kind: u32(4), start: colon_at, end: colon_at }\ncolon_at >= len(src) || src[colon_at] != u8(58) ? { status = u32(2) } | {\ncolon.end = colon_at + u32(1)\n")
		for i, field := range fields {
			fmt.Fprintf(&body, "field_index == u32(%d) ? {\nseen%d ? { status = u32(6) } | {\n", i+1, i)
			if field.nullable {
				fmt.Fprintf(&body, "token: JsonToken = json_token(src, colon.end)\ntoken.kind == u32(10) ? {\nabsent: Option[%s] = .None\nvalue.%s = absent\nat = token.end\nseen%d = true\n} | {\npart%d: Result[JsonDecoded[%s], JsonDecodeError] = %s(src, colon.end)\npart%d ?\n | .Err(reason) => { status = json_decode_error_code(reason) }\n | .Ok(decoded) => {\npresent: Option[%s] = .Some(decoded.value)\nvalue.%s = present\nat = decoded.next\nseen%d = true\n}\n}\n", field.typ, field.name, i, i, field.typ, codecName("read", field.typ), i, field.typ, field.name, i)
			} else if field.length == 0 {
				fmt.Fprintf(&body, "part%d: Result[JsonDecoded[%s], JsonDecodeError] = %s(src, colon.end)\npart%d ?\n | .Err(reason) => { status = json_decode_error_code(reason) }\n | .Ok(decoded) => { value.%s = decoded.value\nat = decoded.next\nseen%d = true\n}\n", i, field.typ, codecName("read", field.typ), i, field.name, i)
			} else {
				body.WriteString("array_start: JsonToken = json_token(src, colon.end)\narray_start.kind <= u32(1) ? { status = u32(2) } | array_start.kind != u32(11) ? { status = u32(3) } | {\nat = array_start.end\nindex: u32 = 0\n")
				fmt.Fprintf(&body, "while index < u32(%d) && status == u32(0) {\nlookahead: u32 = json_skip_space(src, at)\nlookahead < len(src) && src[lookahead] == u8(93) ? { status = u32(8) } | {\npart: Result[JsonDecoded[%s], JsonDecodeError] = %s(src, at)\npart ?\n | .Err(reason) => { status = json_decode_error_code(reason) }\n | .Ok(decoded) => { value.%s[index] = decoded.value\nat = decoded.next\nindex = index + u32(1)\n}\n}\n", field.length, field.typ, codecName("read", field.typ), field.name)
				fmt.Fprintf(&body, "status == u32(0) ? {\nseparator_at: u32 = json_skip_space(src, at)\nseparator: JsonToken = JsonToken { kind: u32(1), start: separator_at, end: separator_at }\nseparator_at < len(src) ? {\nunit: u8 = src[separator_at]\nseparator.kind = unit == u8(44) ? u32(5) | unit == u8(93) ? u32(12) | unit == u8(125) ? u32(3) | u32(1)\nseparator.end = separator_at + u32(1)\n}\nindex == u32(%d) ? {\nseparator.kind == u32(12) ? { at = separator.end } | separator.kind == u32(5) ? {\nextra: JsonToken = json_token(src, separator.end)\nextra.kind <= u32(1) || extra.kind == u32(12) ? { status = u32(2) } | { status = u32(8) }\n} | { status = u32(2) }\n} | separator.kind == u32(12) ? { status = u32(8) } | separator.kind == u32(5) ? {\nat = separator.end\nfollowing: u32 = json_skip_space(src, at)\nfollowing < len(src) && src[following] == u8(93) ? { status = u32(2) }\n} | { status = u32(2) }\n}\n}\nseen%d = status == u32(0)\n}\n", field.length, i)
			}
			body.WriteString("}\n} | ")
		}
		body.WriteString("{ status = u32(7) }\n}\n}\nstatus == u32(0) ? {\nseparator_at: u32 = json_skip_space(src, at)\nseparator: JsonToken = JsonToken { kind: u32(1), start: separator_at, end: separator_at }\nseparator_at < len(src) ? {\nunit: u8 = src[separator_at]\nseparator.kind = unit == u8(44) ? u32(5) | unit == u8(93) ? u32(12) | unit == u8(125) ? u32(3) | u32(1)\nseparator.end = separator_at + u32(1)\n}\nseparator.kind == u32(3) ? { done = true\nat = separator.end\n} | separator.kind == u32(5) ? { at = separator.end } | { status = u32(2) }\n}\n}\n")
		required := []string{"true"}
		for i := range fields {
			required = append(required, fmt.Sprintf("seen%d", i))
		}
		fmt.Fprintf(&body, "status != u32(0) ? { .Err(json_decode_error(status)) } | !(%s) ? { .Err(.MissingField) } | {\nitem: JsonDecoded[%s]\nitem.value = value\nitem.next = at\n.Ok(item)\n}\n}\n", strings.Join(required, " && "), typ)
	}
	source := fmt.Sprintf("%s: (src: []u8, offset: u32): Result[JsonDecoded[%s], JsonDecodeError] {\n%s}\n", codecName("read", typ), typ, body.String())
	source += fmt.Sprintf("%s: (src: []u8): Result[%s, JsonDecodeError] {\n!json_valid_utf8(src) ? { .Err(.InvalidEncoding) } | {\nresult: Result[JsonDecoded[%s], JsonDecodeError] = %s(src, u32(0))\nresult ?\n | .Err(reason) => { .Err(reason) }\n | .Ok(item) => { json_skip_space(src, item.next) != len(src) ? { .Err(.InvalidSyntax) } | { .Ok(item.value) }\n}\n}\n", codecName("decode", typ), typ, typ, codecName("read", typ))
	if err := d.appendCodecSource(typ, source); err != nil {
		return err
	}
	d.decodeGenerated[typ] = true
	return nil
}
