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
	return fmt.Sprintf("(u64(9223372036854775807) + u64(%d))", value-9223372036854775807)
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
		body.WriteString("parsed: Result[JsonInteger, JsonDecodeError] = json_read_integer(src, offset)\nparsed ?\n | .Err(reason) => { .Err(reason) }\n | .Ok(raw) => {\n")
		if primitive == "u64" {
			maximum := ^uint64(0)
			if bits < 64 {
				maximum = (uint64(1) << bits) - 1
			}
			fmt.Fprintf(&body, "raw.negative ? { .Err(.TypeMismatch) } | raw.magnitude > %s ? { .Err(.NumericOverflow) } | {\n", codecU64Literal(maximum))
			conversion := "raw.magnitude"
			if bits < 64 {
				conversion = typ + "_trunc_u64(raw.magnitude)"
			}
			fmt.Fprintf(&body, "item: JsonDecoded[%s]\nitem.value = %s\nitem.next = raw.next\n.Ok(item)\n}\n", typ, conversion)
		} else {
			negativeMax := uint64(1) << (bits - 1)
			fmt.Fprintf(&body, "limit: u64 = raw.negative ? %s | %s\nraw.magnitude > limit ? { .Err(.NumericOverflow) } | {\n", codecU64Literal(negativeMax), codecU64Literal(negativeMax-1))
			body.WriteString("number: i64 = i64(0)\nraw.negative && raw.magnitude > u64(0) ? { number = i64(0) - i64_bits_u64(raw.magnitude - u64(1)) - i64(1) } | { number = i64_bits_u64(raw.magnitude) }\n")
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
		body.WriteString("first: JsonToken = json_token(src, at)\nfirst.kind == u32(3) ? { done = true\nat = first.end\n}\nwhile !done && status == u32(0) {\nkey: JsonToken = json_token(src, at)\nkey.kind != u32(6) ? { status = u32(2) } | {\ncolon: JsonToken = json_token(src, key.end)\ncolon.kind != u32(4) ? { status = u32(2) } | {\n")
		for i, field := range fields {
			fmt.Fprintf(&body, "json_key_equal(src, key, key%d) ? {\nseen%d ? { status = u32(6) } | {\npart%d: Result[JsonDecoded[%s], JsonDecodeError] = %s(src, colon.end)\npart%d ?\n | .Err(reason) => { status = json_decode_error_code(reason) }\n | .Ok(decoded) => { value.%s = decoded.value\nat = decoded.next\nseen%d = true\n}\n}\n} | ", i, i, i, field.typ, codecName("read", field.typ), i, field.name, i)
		}
		body.WriteString("{ status = u32(7) }\n}\n}\nstatus == u32(0) ? {\nseparator: JsonToken = json_token(src, at)\nseparator.kind == u32(3) ? { done = true\nat = separator.end\n} | separator.kind == u32(5) ? { at = separator.end } | { status = u32(2) }\n}\n}\n")
		required := []string{"true"}
		for i := range fields {
			required = append(required, fmt.Sprintf("seen%d", i))
		}
		fmt.Fprintf(&body, "status != u32(0) ? { .Err(json_decode_error(status)) } | !(%s) ? { .Err(.MissingField) } | {\nitem: JsonDecoded[%s]\nitem.value = value\nitem.next = at\n.Ok(item)\n}\n}\n", strings.Join(required, " && "), typ)
	}
	source := fmt.Sprintf("%s: (src: []u8, offset: u32): Result[JsonDecoded[%s], JsonDecodeError] {\n%s}\n", codecName("read", typ), typ, body.String())
	source += fmt.Sprintf("%s: (src: []u8): Result[%s, JsonDecodeError] {\n!is_valid_utf8(src) ? { .Err(.InvalidEncoding) } | {\nresult: Result[JsonDecoded[%s], JsonDecodeError] = %s(src, u32(0))\nresult ?\n | .Err(reason) => { .Err(reason) }\n | .Ok(item) => { json_skip_space(src, item.next) != len(src) ? { .Err(.InvalidSyntax) } | { .Ok(item.value) }\n}\n}\n", codecName("decode", typ), typ, typ, codecName("read", typ))
	if err := d.appendCodecSource(typ, source); err != nil {
		return err
	}
	d.decodeGenerated[typ] = true
	return nil
}
