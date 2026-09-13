package compiler

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/modules"
)

// The derived binary codec (docs/spec/71-codecs.md section 22, dbs ask 9):
// a closed record of fixed-width integers, Bool, nested records, and fixed
// arrays is a fixed layout — fields packed in declaration order, each
// integer at its width in its own endianness (a `bin` tag; little-endian
// by default), Bool one byte. The size is a compile-time constant, so an
// encoder checks its destination once and a decoder its input once; every
// byte is then a plain checked store or load, with no helper call. The
// functions are ordinary Oak built as typed syntax (compiler/synth.go):
// __oak_bin_encoded_size_T, __oak_bin_write_unchecked_T, __oak_bin_write_T,
// __oak_bin_encode_T, __oak_bin_valid_T, __oak_bin_read_unchecked_T, and
// __oak_bin_decode_T (Oak.BinaryCodec states the byte laws).

func binaryCodecName(operation, typ string) string { return "__oak_bin_" + operation + "_" + typ }

// binaryField is one field of a fixed layout: a scalar or a fixed array of
// scalars or records, with the endianness its integers use.
type binaryField struct {
	name, typ string
	length    int64 // 0 for a scalar
	bigEndian bool
}

// binaryWidth is the byte width of a scalar codec type, 0 for a record.
func binaryWidth(typ string) int64 {
	switch typ {
	case "u8", "i8", "Bool":
		return 1
	case "u16", "i16":
		return 2
	case "u32", "i32":
		return 4
	case "u64", "i64":
		return 8
	}
	return 0
}

func isBinaryTag(name string) bool {
	if name == "bin" {
		return true
	}
	return strings.HasSuffix(modules.DemangleText(name), ".bin")
}

// binaryFields reads a record's fields for the binary layout: the JSON
// deriver's shape rules (closed record, fixed arrays) plus the `bin` tag's
// endianness, and without the JSON-only shapes (nullable, views, strings).
func (d *codecDeriver) binaryFields(typ string) ([]binaryField, error) {
	fields, err := d.fields(typ)
	if err != nil {
		return nil, err
	}
	record := d.records[typ].Variants[0].Literal.(*ast.RecordLiteral)
	tags := map[string]bool{}
	for _, field := range record.OrderedFields() {
		for _, tag := range field.Tags {
			if !isBinaryTag(tag.Name) {
				continue
			}
			schema := d.schemas[tag.Name]
			if schema == nil || len(schema.Schema.OrderedFields()) == 0 || schema.Schema.OrderedFields()[0].Name != "endian" {
				return nil, fmt.Errorf("codec: bin field tags require a declared `bin: tag = { endian: string }` schema")
			}
			value := tag.Value
			if entries, ok := value.(*ast.RecordLiteral); ok {
				for _, entry := range entries.OrderedFields() {
					if entry.Name != "endian" {
						return nil, fmt.Errorf("codec: bin tag property %s is not implemented; only endian is supported", entry.Name)
					}
				}
				value = entries.Fields["endian"]
				if value == nil {
					continue
				}
			}
			literal, ok := value.(*ast.StringLiteral)
			if !ok || (literal.Value != "le" && literal.Value != "be") {
				return nil, fmt.Errorf("codec: %s.%s: the bin endian is the string literal \"le\" or \"be\"", typ, field.Name)
			}
			tags[field.Name] = literal.Value == "be"
		}
	}
	out := make([]binaryField, 0, len(fields))
	for _, field := range fields {
		switch {
		case field.view:
			return nil, fmt.Errorf("codec: %s.%s: borrowed fields have no fixed binary layout", typ, field.name)
		case field.nullable:
			return nil, fmt.Errorf("codec: %s.%s: Option fields have no fixed binary layout; encode presence as a field of its own", typ, field.name)
		case field.typ == "string":
			return nil, fmt.Errorf("codec: %s.%s: strings have no fixed binary layout", typ, field.name)
		}
		big, tagged := tags[field.name]
		if tagged && binaryWidth(field.typ) == 0 {
			return nil, fmt.Errorf("codec: %s.%s: endianness applies to integer fields; a record's fields carry their own", typ, field.name)
		}
		if tagged && binaryWidth(field.typ) == 1 {
			return nil, fmt.Errorf("codec: %s.%s: a one-byte field has no endianness", typ, field.name)
		}
		out = append(out, binaryField{name: field.name, typ: field.typ, length: field.length, bigEndian: big})
	}
	return out, nil
}

// binarySize is the constant byte size of a codec type.
func (d *codecDeriver) binarySize(typ string, active map[string]bool) (int64, error) {
	if width := binaryWidth(typ); width != 0 {
		return width, nil
	}
	if active[typ] {
		return 0, fmt.Errorf("codec: recursive record %s has no fixed binary layout", typ)
	}
	active[typ] = true
	defer delete(active, typ)
	fields, err := d.binaryFields(typ)
	if err != nil {
		return 0, err
	}
	total := int64(0)
	for _, field := range fields {
		size, err := d.binarySize(field.typ, active)
		if err != nil {
			return 0, fmt.Errorf("codec field %s.%s: %w", typ, field.name, err)
		}
		if field.length > 0 {
			size *= field.length
		}
		total += size
		if total > 4294967295 {
			return 0, fmt.Errorf("codec: %s exceeds the u32 layout size", typ)
		}
	}
	return total, nil
}

// unsignedOf is the same-width unsigned type of an integer codec type.
func unsignedOf(typ string) string {
	if strings.HasPrefix(typ, "i") {
		return "u" + typ[1:]
	}
	return typ
}

// binaryStores emits the stores of one scalar `value` (an expression of
// type typ) at dst[out..out+w) and advances out.
func binaryStores(s *synth, typ string, big bool, value ast.Expression, raw string) []ast.Statement {
	width := binaryWidth(typ)
	at := func(k int64) ast.Expression {
		if k == 0 {
			return s.id("out")
		}
		return s.add(s.id("out"), s.u32(k))
	}
	var body []ast.Statement
	switch {
	case typ == "Bool":
		body = append(body, s.store(s.index(s.id("dst"), at(0)), s.cond(value, s.u8(1), s.u8(0))))
	case width == 1:
		if typ == "i8" {
			value = s.call("u8_bits_i8", value)
		}
		body = append(body, s.store(s.index(s.id("dst"), at(0)), value))
	default:
		unsigned := unsignedOf(typ)
		body = append(body, s.decl(raw, s.id(unsigned), value))
		if unsigned != typ {
			body[len(body)-1] = s.decl(raw, s.id(unsigned), s.call(unsigned+"_bits_"+typ, value))
		}
		for k := int64(0); k < width; k++ {
			shift := k
			if big {
				shift = width - 1 - k
			}
			byteOf := ast.Expression(s.id(raw))
			if shift != 0 {
				byteOf = s.infix(s.id(raw), ">>", s.conv(unsigned, s.intLit(8*shift)))
			}
			body = append(body, s.store(s.index(s.id("dst"), at(k)), s.call("u8_trunc_"+unsigned, byteOf)))
		}
	}
	return append(body, s.assign("out", s.add(s.id("out"), s.u32(width))))
}

// binaryLoad is the expression reading one scalar of type typ at src[at..).
func binaryLoad(s *synth, typ string, big bool) ast.Expression {
	width := binaryWidth(typ)
	at := func(k int64) ast.Expression {
		if k == 0 {
			return s.id("at")
		}
		return s.add(s.id("at"), s.u32(k))
	}
	switch {
	case typ == "Bool":
		return s.ne(s.index(s.id("src"), at(0)), s.u8(0))
	case width == 1:
		if typ == "i8" {
			return s.call("i8_bits_u8", s.index(s.id("src"), at(0)))
		}
		return s.index(s.id("src"), at(0))
	}
	unsigned := unsignedOf(typ)
	var value ast.Expression
	for k := int64(0); k < width; k++ {
		shift := k
		if big {
			shift = width - 1 - k
		}
		byteOf := ast.Expression(s.conv(unsigned, s.index(s.id("src"), at(k))))
		if shift != 0 {
			byteOf = s.infix(byteOf, "<<", s.conv(unsigned, s.intLit(8*shift)))
		}
		if value == nil {
			value = byteOf
		} else {
			value = s.infix(value, "|", byteOf)
		}
	}
	if unsigned != typ {
		return s.call(typ+"_bits_"+unsigned, value)
	}
	return value
}

// deriveBinary builds the encoder side of one type.
func (d *codecDeriver) deriveBinary(typ string) error {
	if d.binaryGenerated == nil {
		d.binaryGenerated = map[string]bool{}
	}
	if d.binaryGenerated[typ] {
		return nil
	}
	size, err := d.binarySize(typ, map[string]bool{})
	if err != nil {
		return err
	}
	for _, operation := range []string{"encoded_size", "write_unchecked", "write", "encode", "valid", "read_unchecked", "decode"} {
		if d.names[binaryCodecName(operation, typ)] {
			return fmt.Errorf("codec: generated name %s conflicts with a declaration", binaryCodecName(operation, typ))
		}
	}
	d.binaryGenerated[typ] = true
	sizeName, uncheckedName, writeName, encodeName := binaryCodecName("encoded_size", typ), binaryCodecName("write_unchecked", typ), binaryCodecName("write", typ), binaryCodecName("encode", typ)
	validName, readName, decodeName := binaryCodecName("valid", typ), binaryCodecName("read_unchecked", typ), binaryCodecName("decode", typ)
	result := func(s *synth) ast.Expression { return s.app("Result", s.id("u32"), s.id("BinaryError")) }

	write := newSynth("codec:" + uncheckedName)
	valid := newSynth("codec:" + validName)
	read := newSynth("codec:" + readName)
	writeBody := []ast.Statement{write.decl("out", write.id("u32"), write.id("offset"))}
	validBody := []ast.Statement{valid.decl("at", valid.id("u32"), valid.id("offset")), valid.decl("ok", valid.id("Bool"), valid.boolean(true))}
	readBody := []ast.Statement{read.decl("value", read.id(typ), nil), read.decl("at", read.id("u32"), read.id("offset"))}
	if binaryWidth(typ) != 0 {
		writeBody = append(writeBody, binaryStores(write, typ, false, write.id("value"), "raw")...)
		if typ == "Bool" {
			validBody = append(validBody, valid.assign("ok", valid.le(valid.index(valid.id("src"), valid.id("at")), valid.u8(1))))
		}
		readBody = append(readBody, read.assign("value", binaryLoad(read, typ, false)))
	} else {
		fields, err := d.binaryFields(typ)
		if err != nil {
			return err
		}
		for _, field := range fields {
			if binaryWidth(field.typ) == 0 {
				if err := d.deriveBinary(field.typ); err != nil {
					return fmt.Errorf("codec field %s.%s: %w", typ, field.name, err)
				}
			}
			elemSize, _ := d.binarySize(field.typ, map[string]bool{})
			// One element, at `out`/`at`, of the field or of an array element.
			storeElem := func(s *synth, value ast.Expression) []ast.Statement {
				if binaryWidth(field.typ) != 0 {
					// One temporary per field: names are function-scoped.
					return binaryStores(s, field.typ, field.bigEndian, value, "raw_"+field.name)
				}
				return []ast.Statement{s.assign("out", s.add(s.id("out"), s.call(binaryCodecName("write_unchecked", field.typ), value, s.id("dst"), s.id("out"))))}
			}
			validElem := func(s *synth) []ast.Statement {
				switch {
				case field.typ == "Bool":
					return []ast.Statement{s.assign("ok", s.and(s.id("ok"), s.le(s.index(s.id("src"), s.id("at")), s.u8(1)))), s.assign("at", s.add(s.id("at"), s.u32(1)))}
				case binaryWidth(field.typ) != 0:
					return []ast.Statement{s.assign("at", s.add(s.id("at"), s.u32(elemSize)))}
				}
				return []ast.Statement{s.assign("ok", s.and(s.id("ok"), s.call(binaryCodecName("valid", field.typ), s.id("src"), s.id("at")))), s.assign("at", s.add(s.id("at"), s.u32(elemSize)))}
			}
			loadElem := func(s *synth, target *ast.IndexExpression) []ast.Statement {
				if binaryWidth(field.typ) != 0 {
					return []ast.Statement{s.store(target, binaryLoad(s, field.typ, field.bigEndian)), s.assign("at", s.add(s.id("at"), s.u32(elemSize)))}
				}
				return []ast.Statement{s.store(target, s.call(binaryCodecName("read_unchecked", field.typ), s.id("src"), s.id("at"))), s.assign("at", s.add(s.id("at"), s.u32(elemSize)))}
			}
			if field.length == 0 {
				writeBody = append(writeBody, storeElem(write, write.field(write.id("value"), field.name))...)
				validBody = append(validBody, validElem(valid)...)
				readBody = append(readBody, loadElem(read, read.field(read.id("value"), field.name))...)
				continue
			}
			// Fixed arrays: a bounded loop whose code size is independent of N.
			index := "index_" + field.name
			writeBody = append(writeBody, write.decl(index, write.id("u32"), write.intLit(0)),
				write.loop(write.lt(write.id(index), write.u32(field.length)),
					append(storeElem(write, write.index(write.field(write.id("value"), field.name), write.id(index))), write.assign(index, write.add(write.id(index), write.u32(1))))...))
			validBody = append(validBody, valid.decl(index, valid.id("u32"), valid.intLit(0)),
				valid.loop(valid.lt(valid.id(index), valid.u32(field.length)),
					append(validElem(valid), valid.assign(index, valid.add(valid.id(index), valid.u32(1))))...))
			readBody = append(readBody, read.decl(index, read.id("u32"), read.intLit(0)),
				read.loop(read.lt(read.id(index), read.u32(field.length)),
					append(loadElem(read, read.index(read.field(read.id("value"), field.name), read.id(index))), read.assign(index, read.add(read.id(index), read.u32(1))))...))
		}
	}
	writeBody = append(writeBody, write.expr(write.sub(write.id("out"), write.id("offset"))))
	validBody = append(validBody, valid.expr(valid.id("ok")))
	readBody = append(readBody, read.expr(read.id("value")))

	sizeS := newSynth("codec:" + sizeName)
	sizeFn := sizeS.fn(sizeName, []*ast.FunctionParameter{sizeS.param("value", sizeS.id(typ))}, result(sizeS),
		sizeS.expr(sizeS.variant("Ok", sizeS.u32(size))))
	uncheckedFn := write.fn(uncheckedName,
		[]*ast.FunctionParameter{write.param("value", write.id(typ)), write.param("dst", write.span(write.id("u8"))), write.param("offset", write.id("u32"))},
		write.id("u32"), writeBody...)
	checked := newSynth("codec:" + writeName)
	writeFn := checked.fn(writeName,
		[]*ast.FunctionParameter{checked.param("value", checked.id(typ)), checked.param("dst", checked.span(checked.id("u8"))), checked.param("offset", checked.id("u32"))},
		result(checked),
		checked.expr(checked.cond(
			checked.call("bytes_range_fits", checked.call("len", checked.id("dst")), checked.id("offset"), checked.u32(size)),
			checked.block(checked.expr(checked.variant("Ok", checked.call(uncheckedName, checked.id("value"), checked.id("dst"), checked.id("offset"))))),
			checked.block(checked.expr(errVariant(checked, "DestinationTooSmall"))))))
	encode := newSynth("codec:" + encodeName)
	encodeFn := encode.fn(encodeName,
		[]*ast.FunctionParameter{encode.param("value", encode.id(typ)), encode.param("dst", encode.span(encode.id("u8")))},
		result(encode),
		encode.expr(encode.call(writeName, encode.id("value"), encode.id("dst"), encode.u32(0))))
	validFn := valid.fn(validName,
		[]*ast.FunctionParameter{valid.param("src", valid.view(valid.id("u8"))), valid.param("offset", valid.id("u32"))},
		valid.id("Bool"), validBody...)
	readFn := read.fn(readName,
		[]*ast.FunctionParameter{read.param("src", read.view(read.id("u8"))), read.param("offset", read.id("u32"))},
		read.id(typ), readBody...)
	decode := newSynth("codec:" + decodeName)
	decodeFn := decode.fn(decodeName,
		[]*ast.FunctionParameter{decode.param("src", decode.view(decode.id("u8")))},
		decode.app("Result", decode.id(typ), decode.id("BinaryDecodeError")),
		decode.expr(decode.cond(
			decode.call("bytes_range_fits", decode.call("len", decode.id("src")), decode.u32(0), decode.u32(size)),
			decode.block(decode.expr(decode.cond(
				decode.call(validName, decode.id("src"), decode.u32(0)),
				decode.block(decode.expr(decode.variant("Ok", decode.call(readName, decode.id("src"), decode.u32(0))))),
				decode.block(decode.expr(errVariant(decode, "InvalidBool")))))),
			decode.block(decode.expr(errVariant(decode, "InputTooShort"))))))
	d.output = append(d.output, sizeFn, uncheckedFn, writeFn, encodeFn, validFn, readFn, decodeFn)
	return nil
}
