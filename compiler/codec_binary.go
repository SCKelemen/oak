package compiler

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/modules"
)

// The derived binary codec (docs/spec/71-codecs.md section 22, dbs ask 9):
// a closed record of fixed-width integers (u8 to u128, i8 to i64), Bool,
// nested records, and fixed arrays is a fixed layout — fields packed in
// declaration order, each integer at its width in its own endianness (a
// `bin` tag; little-endian by default), Bool one byte. The size is a
// compile-time constant, so the encoder tests its destination's length
// once, as the literal comparison `len(dst) >= SIZE`, and then stores
// every byte at a constant offset — `i * stride + K` inside an array's
// loop — under that fact; the extents prover discharges each store
// (Oak.Extents.constant_under_min_length, scaled_under_bound), so the
// emitted C carries no per-byte check. The decoder reads the same way.
// Nested records are inlined, so the whole record is one straight-line
// body. The functions are ordinary Oak built as typed syntax
// (compiler/synth.go): __oak_bin_encoded_size_T, __oak_bin_encode_T, and
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
	case "u128":
		return 16
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

// binaryOffset spells a byte's index: the constant `off` plus one term
// `index * stride` per enclosing array loop. With one term the shape is
// the prover's scaled index; with none, a constant.
type binaryOffset struct {
	terms []binaryTerm
}

type binaryTerm struct {
	index  string
	stride int64
}

func (o binaryOffset) at(s *synth, off int64) ast.Expression {
	expr := ast.Expression(s.u32(off))
	for k := len(o.terms) - 1; k >= 0; k-- {
		term := o.terms[k]
		expr = s.add(s.infix(s.id(term.index), "*", s.u32(term.stride)), expr)
	}
	return expr
}

func (o binaryOffset) inside(index string, stride int64) binaryOffset {
	terms := append(append([]binaryTerm{}, o.terms...), binaryTerm{index: index, stride: stride})
	return binaryOffset{terms: terms}
}

// binaryStores emits the stores of one scalar at dst[off..off+w).
func binaryStores(s *synth, typ string, big bool, value func() ast.Expression, at binaryOffset, off int64) []ast.Statement {
	width := binaryWidth(typ)
	switch {
	case typ == "Bool":
		return []ast.Statement{s.store(s.index(s.id("dst"), at.at(s, off)), s.cond(value(), s.u8(1), s.u8(0)))}
	case width == 1:
		v := value()
		if typ == "i8" {
			v = s.call("u8_bits_i8", v)
		}
		return []ast.Statement{s.store(s.index(s.id("dst"), at.at(s, off)), v)}
	}
	unsigned := unsignedOf(typ)
	raw := func() ast.Expression {
		v := value()
		if unsigned != typ {
			return s.call(unsigned+"_bits_"+typ, v)
		}
		return v
	}
	out := make([]ast.Statement, 0, width)
	for k := int64(0); k < width; k++ {
		shift := k
		if big {
			shift = width - 1 - k
		}
		byteOf := raw()
		if shift != 0 {
			byteOf = s.infix(byteOf, ">>", s.conv(unsigned, s.intLit(8*shift)))
		}
		out = append(out, s.store(s.index(s.id("dst"), at.at(s, off+k)), s.call("u8_trunc_"+unsigned, byteOf)))
	}
	return out
}

// binaryLoad is the expression reading one scalar of type typ at src[off..).
func binaryLoad(s *synth, typ string, big bool, at binaryOffset, off int64) ast.Expression {
	width := binaryWidth(typ)
	byteAt := func(k int64) ast.Expression { return s.index(s.id("src"), at.at(s, off+k)) }
	switch {
	case typ == "Bool":
		return s.ne(byteAt(0), s.u8(0))
	case width == 1:
		if typ == "i8" {
			return s.call("i8_bits_u8", byteAt(0))
		}
		return byteAt(0)
	}
	unsigned := unsignedOf(typ)
	var value ast.Expression
	for k := int64(0); k < width; k++ {
		shift := k
		if big {
			shift = width - 1 - k
		}
		byteOf := ast.Expression(s.conv(unsigned, byteAt(k)))
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

// binaryEncodeRecord emits the stores of a record whose bytes start at
// `base`, its fields read through `path`.
func (d *codecDeriver) binaryEncodeRecord(s *synth, typ string, path func() ast.Expression, at binaryOffset, base int64) ([]ast.Statement, error) {
	fields, err := d.binaryFields(typ)
	if err != nil {
		return nil, err
	}
	out := []ast.Statement{}
	off := base
	for _, field := range fields {
		fieldPath := func() ast.Expression { return s.field(path(), field.name) }
		elemSize, err := d.binarySize(field.typ, map[string]bool{})
		if err != nil {
			return nil, fmt.Errorf("codec field %s.%s: %w", typ, field.name, err)
		}
		element := func(value func() ast.Expression, at binaryOffset, off int64) ([]ast.Statement, error) {
			if binaryWidth(field.typ) != 0 {
				return binaryStores(s, field.typ, field.bigEndian, value, at, off), nil
			}
			return d.binaryEncodeRecord(s, field.typ, value, at, off)
		}
		if field.length == 0 {
			stmts, err := element(fieldPath, at, off)
			if err != nil {
				return nil, err
			}
			out = append(out, stmts...)
			off += elemSize
			continue
		}
		// A fixed array: one bounded loop whose code size is independent of
		// N; each byte at index * stride + constant.
		index := fmt.Sprintf("index_%s_%d", field.name, s.next)
		body, err := element(func() ast.Expression { return s.index(fieldPath(), s.id(index)) }, at.inside(index, elemSize), off)
		if err != nil {
			return nil, err
		}
		body = append(body, s.assign(index, s.add(s.id(index), s.u32(1))))
		out = append(out, s.decl(index, s.id("u32"), s.intLit(0)), s.loop(s.lt(s.id(index), s.u32(field.length)), body...))
		off += elemSize * field.length
	}
	return out, nil
}

// binaryDecodeRecord emits the loads of a record into the fields of `path`
// (rooted at the decoded local), and folds each Bool byte's validity into
// `valid`.
func (d *codecDeriver) binaryDecodeRecord(s *synth, typ string, path func() ast.Expression, at binaryOffset, base int64) ([]ast.Statement, error) {
	fields, err := d.binaryFields(typ)
	if err != nil {
		return nil, err
	}
	out := []ast.Statement{}
	off := base
	for _, field := range fields {
		into := func() *ast.IndexExpression { return s.field(path(), field.name) }
		elemSize, err := d.binarySize(field.typ, map[string]bool{})
		if err != nil {
			return nil, fmt.Errorf("codec field %s.%s: %w", typ, field.name, err)
		}
		element := func(target func() *ast.IndexExpression, at binaryOffset, off int64) ([]ast.Statement, error) {
			if binaryWidth(field.typ) == 0 {
				return d.binaryDecodeRecord(s, field.typ, func() ast.Expression { return target() }, at, off)
			}
			stmts := []ast.Statement{s.store(target(), binaryLoad(s, field.typ, field.bigEndian, at, off))}
			if field.typ == "Bool" {
				stmts = append(stmts, s.assign("valid", s.and(s.id("valid"), s.le(s.index(s.id("src"), at.at(s, off)), s.u8(1)))))
			}
			return stmts, nil
		}
		if field.length == 0 {
			stmts, err := element(into, at, off)
			if err != nil {
				return nil, err
			}
			out = append(out, stmts...)
			off += elemSize
			continue
		}
		index := fmt.Sprintf("index_%s_%d", field.name, s.next)
		body, err := element(func() *ast.IndexExpression { return s.index(into(), s.id(index)) }, at.inside(index, elemSize), off)
		if err != nil {
			return nil, err
		}
		body = append(body, s.assign(index, s.add(s.id(index), s.u32(1))))
		out = append(out, s.decl(index, s.id("u32"), s.intLit(0)), s.loop(s.lt(s.id(index), s.u32(field.length)), body...))
		off += elemSize * field.length
	}
	return out, nil
}

// deriveBinary builds the three functions of one type: the constant size,
// the encoder (one length check, then the stores), the decoder (one length
// check, then the loads and the Bool validation).
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
	for _, operation := range []string{"encoded_size", "encode", "decode"} {
		if d.names[binaryCodecName(operation, typ)] {
			return fmt.Errorf("codec: generated name %s conflicts with a declaration", binaryCodecName(operation, typ))
		}
	}
	d.binaryGenerated[typ] = true
	sizeName, encodeName, decodeName := binaryCodecName("encoded_size", typ), binaryCodecName("encode", typ), binaryCodecName("decode", typ)
	result := func(s *synth) ast.Expression { return s.app("Result", s.id("u32"), s.id("BinaryError")) }

	sizeS := newSynth("codec:" + sizeName)
	sizeFn := sizeS.fn(sizeName, []*ast.FunctionParameter{sizeS.param("value", sizeS.id(typ))}, result(sizeS),
		sizeS.expr(sizeS.variant("Ok", sizeS.u32(size))))

	encode := newSynth("codec:" + encodeName)
	var stores []ast.Statement
	if binaryWidth(typ) != 0 {
		stores = binaryStores(encode, typ, false, func() ast.Expression { return encode.id("value") }, binaryOffset{}, 0)
	} else if stores, err = d.binaryEncodeRecord(encode, typ, func() ast.Expression { return encode.id("value") }, binaryOffset{}, 0); err != nil {
		return err
	}
	stores = append(stores, encode.expr(encode.variant("Ok", encode.u32(size))))
	encodeFn := encode.fn(encodeName,
		[]*ast.FunctionParameter{encode.param("value", encode.id(typ)), encode.param("dst", encode.span(encode.id("u8")))},
		result(encode),
		encode.expr(encode.cond(
			encode.ge(encode.call("len", encode.id("dst")), encode.u32(size)),
			encode.block(stores...),
			encode.block(encode.expr(errVariant(encode, "DestinationTooSmall"))))))

	decode := newSynth("codec:" + decodeName)
	body := []ast.Statement{decode.decl("value", decode.id(typ), nil), decode.decl("valid", decode.id("Bool"), decode.boolean(true))}
	if binaryWidth(typ) != 0 {
		body = append(body, decode.assign("value", binaryLoad(decode, typ, false, binaryOffset{}, 0)))
		if typ == "Bool" {
			body = append(body, decode.assign("valid", decode.le(decode.index(decode.id("src"), decode.u32(0)), decode.u8(1))))
		}
	} else {
		loads, err := d.binaryDecodeRecord(decode, typ, func() ast.Expression { return decode.id("value") }, binaryOffset{}, 0)
		if err != nil {
			return err
		}
		body = append(body, loads...)
	}
	body = append(body, decode.expr(decode.cond(decode.id("valid"),
		decode.block(decode.expr(decode.variant("Ok", decode.id("value")))),
		decode.block(decode.expr(errVariant(decode, "InvalidBool"))))))
	decodeFn := decode.fn(decodeName,
		[]*ast.FunctionParameter{decode.param("src", decode.view(decode.id("u8")))},
		decode.app("Result", decode.id(typ), decode.id("BinaryDecodeError")),
		decode.expr(decode.cond(
			decode.ge(decode.call("len", decode.id("src")), decode.u32(size)),
			decode.block(body...),
			decode.block(decode.expr(errVariant(decode, "InputTooShort"))))))
	d.output = append(d.output, sizeFn, encodeFn, decodeFn)
	return nil
}
