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
	// optional marks an Option[T] field: a presence byte, then T's bytes
	// (zeros when absent), so the layout stays fixed.
	optional bool
	// viewBytes is the byte count of a View[u8, R] field: decoded as a
	// subslice of the input, encoded by copying exactly that many bytes.
	viewBytes int64
	region    string
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
	byteCounts := map[string]int64{}
	for _, field := range record.OrderedFields() {
		for _, tag := range field.Tags {
			if !isBinaryTag(tag.Name) {
				continue
			}
			schema := d.schemas[tag.Name]
			if schema == nil || len(schema.Schema.OrderedFields()) == 0 || schema.Schema.OrderedFields()[0].Name != "endian" {
				return nil, fmt.Errorf("codec: bin field tags require a declared `bin: tag = { endian: string }` schema (with `bytes: u32` for view fields)")
			}
			value := tag.Value
			if entries, ok := value.(*ast.RecordLiteral); ok {
				for _, entry := range entries.OrderedFields() {
					switch entry.Name {
					case "endian":
					case "bytes":
						count, isInt := entry.Value.(*ast.IntegerLiteral)
						if !isInt || count.Value <= 0 || count.Value > 4294967295 {
							return nil, fmt.Errorf("codec: %s.%s: the bin bytes count is an integer literal in 1..4294967295", typ, field.Name)
						}
						byteCounts[field.Name] = count.Value
					default:
						return nil, fmt.Errorf("codec: bin tag property %s is not implemented; endian and bytes are supported", entry.Name)
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
		if field.view {
			count, counted := byteCounts[field.name]
			if !counted {
				return nil, fmt.Errorf("codec: %s.%s: a View[u8, R] field needs its byte count in the layout (`%s(bin: { bytes: N }): View[u8, R]`)", typ, field.name, field.name)
			}
			if _, tagged := tags[field.name]; tagged {
				return nil, fmt.Errorf("codec: %s.%s: a byte run has no endianness", typ, field.name)
			}
			out = append(out, binaryField{name: field.name, typ: "view", viewBytes: count, region: field.region})
			continue
		}
		if field.typ == "string" {
			return nil, fmt.Errorf("codec: %s.%s: strings have no fixed binary layout; a View[u8, R] field with a bytes count is the borrowed form", typ, field.name)
		}
		if _, counted := byteCounts[field.name]; counted {
			return nil, fmt.Errorf("codec: %s.%s: the bytes count applies to View[u8, R] fields", typ, field.name)
		}
		big, tagged := tags[field.name]
		if tagged && binaryWidth(field.typ) == 0 {
			return nil, fmt.Errorf("codec: %s.%s: endianness applies to integer fields; a record's fields carry their own", typ, field.name)
		}
		if tagged && binaryWidth(field.typ) == 1 {
			return nil, fmt.Errorf("codec: %s.%s: a one-byte field has no endianness", typ, field.name)
		}
		if field.nullable && field.length > 0 {
			return nil, fmt.Errorf("codec: %s.%s: an array of Option has no derived layout; wrap the element in a record", typ, field.name)
		}
		out = append(out, binaryField{name: field.name, typ: field.typ, length: field.length, bigEndian: big, optional: field.nullable})
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
		size := field.viewBytes
		if field.typ != "view" {
			var err error
			size, err = d.binarySize(field.typ, active)
			if err != nil {
				return 0, fmt.Errorf("codec field %s.%s: %w", typ, field.name, err)
			}
			if field.optional {
				size++ // the presence byte
			}
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
	for _, operation := range []string{"encoded_size", "write_unchecked", "check", "write", "encode", "valid", "read_unchecked", "decode"} {
		if d.names[binaryCodecName(operation, typ)] {
			return fmt.Errorf("codec: generated name %s conflicts with a declaration", binaryCodecName(operation, typ))
		}
	}
	d.binaryGenerated[typ] = true
	sizeName, uncheckedName, writeName, encodeName := binaryCodecName("encoded_size", typ), binaryCodecName("write_unchecked", typ), binaryCodecName("write", typ), binaryCodecName("encode", typ)
	validName, readName, decodeName, checkName := binaryCodecName("valid", typ), binaryCodecName("read_unchecked", typ), binaryCodecName("decode", typ), binaryCodecName("check", typ)
	result := func(s *synth) ast.Expression { return s.app("Result", s.id("u32"), s.id("BinaryError")) }

	// A record with View[u8, R] fields carries its region through every
	// generated function (docs/spec/50-borrowing.md section 8c): the value
	// type is T[R], the input View[u8, R], so the decoded record borrows the
	// input it views.
	region := ""
	var fields []binaryField
	if binaryWidth(typ) == 0 {
		var err error
		if fields, err = d.binaryFields(typ); err != nil {
			return err
		}
		for _, field := range fields {
			if field.typ == "view" {
				if region != "" && region != field.region {
					return fmt.Errorf("codec: %s carries views in two regions; one region per record is derived", typ)
				}
				region = field.region
			}
		}
	}
	regions := []string{}
	if region != "" {
		regions = []string{region}
	}
	valueType := func(s *synth) ast.Expression {
		if region != "" {
			return s.app(typ, s.id(region))
		}
		return s.id(typ)
	}
	srcType := func(s *synth) ast.Expression {
		if region != "" {
			return s.app("View", s.id("u8"), s.id(region))
		}
		return s.view(s.id("u8"))
	}

	write := newSynth("codec:" + uncheckedName)
	valid := newSynth("codec:" + validName)
	read := newSynth("codec:" + readName)
	check := newSynth("codec:" + checkName)
	writeBody := []ast.Statement{write.decl("out", write.id("u32"), write.id("offset"))}
	// The validity code: 0 valid, 1 a Bool byte above one, 2 a presence
	// byte above one; the first fault wins, nested records pass theirs up.
	validBody := []ast.Statement{valid.decl("at", valid.id("u32"), valid.id("offset")), valid.decl("code", valid.id("u32"), valid.intLit(0))}
	// The reader collects every field in a local and builds the record once
	// at the end: no zero record holding views ever exists.
	readBody := []ast.Statement{read.decl("at", read.id("u32"), read.id("offset"))}
	checkBody := []ast.Statement{check.decl("fits", check.id("Bool"), check.boolean(true))}
	var readInits []recordInit
	if binaryWidth(typ) != 0 {
		writeBody = append(writeBody, binaryStores(write, typ, false, write.id("value"), "raw")...)
		if typ == "Bool" {
			validBody = append(validBody, valid.assign("code", valid.cond(valid.gt(valid.index(valid.id("src"), valid.id("at")), valid.u8(1)), valid.u32(1), valid.u32(0))))
		}
		readBody = append(readBody, read.decl("value", read.id(typ), binaryLoad(read, typ, false)))
	} else {
		for _, field := range fields {
			local := "field_" + field.name
			readInits = append(readInits, read.set(field.name, read.id(local)))
			if field.typ == "view" {
				// The byte run: copied out on encode (its length checked by
				// the checked entry), a subslice of the input on decode.
				n := field.viewBytes
				checkBody = append(checkBody, check.assign("fits", check.and(check.id("fits"), check.eq(check.call("len", check.field(check.id("value"), field.name)), check.u32(n)))))
				copyIndex := "copy_" + field.name
				writeBody = append(writeBody,
					write.decl(copyIndex, write.id("u32"), write.intLit(0)),
					write.loop(write.lt(write.id(copyIndex), write.u32(n)),
						write.store(write.index(write.id("dst"), write.add(write.id("out"), write.id(copyIndex))), write.index(write.field(write.id("value"), field.name), write.id(copyIndex))),
						write.assign(copyIndex, write.add(write.id(copyIndex), write.u32(1)))),
					write.assign("out", write.add(write.id("out"), write.u32(n))))
				validBody = append(validBody, valid.assign("at", valid.add(valid.id("at"), valid.u32(n))))
				readBody = append(readBody,
					read.decl(local, read.view(read.id("u8")), read.call("subslice", read.id("src"), read.id("at"), read.u32(n))),
					read.assign("at", read.add(read.id("at"), read.u32(n))))
				continue
			}
			if binaryWidth(field.typ) == 0 {
				if err := d.deriveBinary(field.typ); err != nil {
					return fmt.Errorf("codec field %s.%s: %w", typ, field.name, err)
				}
				if d.binaryRegions[field.typ] {
					return fmt.Errorf("codec: %s.%s: a nested record with view fields is not derived; borrow at the top level", typ, field.name)
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
			// faultAt is the validity code of one element at `at` plus delta.
			faultAt := func(s *synth, delta int64) ast.Expression {
				position := ast.Expression(s.id("at"))
				if delta != 0 {
					position = s.add(s.id("at"), s.u32(delta))
				}
				switch {
				case field.typ == "Bool":
					return s.cond(s.gt(s.index(s.id("src"), position), s.u8(1)), s.u32(1), s.u32(0))
				case binaryWidth(field.typ) != 0:
					return s.u32(0)
				}
				return s.call(binaryCodecName("valid", field.typ), s.id("src"), position)
			}
			// keepFirst records a fault only when none is recorded yet.
			keepFirst := func(s *synth, fault ast.Expression) ast.Statement {
				return s.assign("code", s.cond(s.eq(s.id("code"), s.u32(0)), fault, s.id("code")))
			}
			validElem := func(s *synth) []ast.Statement {
				if binaryWidth(field.typ) != 0 && field.typ != "Bool" {
					return []ast.Statement{s.assign("at", s.add(s.id("at"), s.u32(elemSize)))}
				}
				return []ast.Statement{keepFirst(s, faultAt(s, 0)), s.assign("at", s.add(s.id("at"), s.u32(elemSize)))}
			}
			loadElem := func(s *synth, target *ast.IndexExpression) []ast.Statement {
				if binaryWidth(field.typ) != 0 {
					return []ast.Statement{s.store(target, binaryLoad(s, field.typ, field.bigEndian)), s.assign("at", s.add(s.id("at"), s.u32(elemSize)))}
				}
				return []ast.Statement{s.store(target, s.call(binaryCodecName("read_unchecked", field.typ), s.id("src"), s.id("at"))), s.assign("at", s.add(s.id("at"), s.u32(elemSize)))}
			}
			// loadValue is the element's value expression at `at`; the caller
			// advances `at`.
			loadValue := func(s *synth) ast.Expression {
				if binaryWidth(field.typ) != 0 {
					return binaryLoad(s, field.typ, field.bigEndian)
				}
				return s.call(binaryCodecName("read_unchecked", field.typ), s.id("src"), s.id("at"))
			}
			if field.optional {
				// Presence byte, then the payload's bytes: zeros when absent.
				optionType := func(s *synth) ast.Expression { return s.app("Option", s.id(field.typ)) }
				zeroIndex := "zero_" + field.name
				writeBody = append(writeBody,
					write.decl("opt_"+field.name, optionType(write), write.field(write.id("value"), field.name)),
					write.expr(write.match(write.id("opt_"+field.name),
						write.arm("None", "", write.block(append([]ast.Statement{
							write.store(write.index(write.id("dst"), write.id("out")), write.u8(0)),
							write.assign("out", write.add(write.id("out"), write.u32(1))),
							write.decl(zeroIndex, write.id("u32"), write.intLit(0)),
							write.loop(write.lt(write.id(zeroIndex), write.u32(elemSize)),
								write.store(write.index(write.id("dst"), write.add(write.id("out"), write.id(zeroIndex))), write.u8(0)),
								write.assign(zeroIndex, write.add(write.id(zeroIndex), write.u32(1)))),
							write.assign("out", write.add(write.id("out"), write.u32(elemSize)))})...)),
						write.arm("Some", "present_"+field.name, write.block(append([]ast.Statement{
							write.store(write.index(write.id("dst"), write.id("out")), write.u8(1)),
							write.assign("out", write.add(write.id("out"), write.u32(1)))},
							storeElem(write, write.id("present_"+field.name))...)...)))))
				// The presence byte is 0 or 1; a present payload is validated,
				// an absent one's zeros are not inspected.
				validBody = append(validBody,
					keepFirst(valid, valid.cond(valid.gt(valid.index(valid.id("src"), valid.id("at")), valid.u8(1)), valid.u32(2), valid.u32(0))),
					keepFirst(valid, valid.cond(valid.eq(valid.index(valid.id("src"), valid.id("at")), valid.u8(1)), faultAt(valid, 1), valid.u32(0))),
					valid.assign("at", valid.add(valid.id("at"), valid.u32(1+elemSize))))
				readBody = append(readBody,
					read.decl("present_"+field.name, read.id("Bool"), read.ne(read.index(read.id("src"), read.id("at")), read.u8(0))),
					read.assign("at", read.add(read.id("at"), read.u32(1))),
					read.decl(local, optionType(read), read.cond(read.id("present_"+field.name), read.variant("Some", loadValue(read)), read.variant("None", nil))),
					read.assign("at", read.add(read.id("at"), read.u32(elemSize))))
				continue
			}
			if field.length == 0 {
				writeBody = append(writeBody, storeElem(write, write.field(write.id("value"), field.name))...)
				validBody = append(validBody, validElem(valid)...)
				readBody = append(readBody,
					read.decl(local, read.id(field.typ), loadValue(read)),
					read.assign("at", read.add(read.id("at"), read.u32(elemSize))))
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
			readBody = append(readBody,
				read.decl(local, read.array(field.length, read.id(field.typ)), nil),
				read.decl(index, read.id("u32"), read.intLit(0)),
				read.loop(read.lt(read.id(index), read.u32(field.length)),
					append(loadElem(read, read.index(read.id(local), read.id(index))), read.assign(index, read.add(read.id(index), read.u32(1))))...))
		}
		readBody = append(readBody, read.decl("value", valueType(read), read.record(typ, readInits...)))
	}
	if d.binaryRegions == nil {
		d.binaryRegions = map[string]bool{}
	}
	d.binaryRegions[typ] = region != ""
	writeBody = append(writeBody, write.expr(write.sub(write.id("out"), write.id("offset"))))
	validBody = append(validBody, valid.expr(valid.id("code")))
	readBody = append(readBody, read.expr(read.id("value")))
	checkBody = append(checkBody, check.expr(check.id("fits")))

	sizeS := newSynth("codec:" + sizeName)
	sizeFn := sizeS.fnRegions(sizeName, regions, []*ast.FunctionParameter{sizeS.param("value", valueType(sizeS))}, result(sizeS),
		sizeS.expr(sizeS.variant("Ok", sizeS.u32(size))))
	uncheckedFn := write.fnRegions(uncheckedName, regions,
		[]*ast.FunctionParameter{write.param("value", valueType(write)), write.param("dst", write.span(write.id("u8"))), write.param("offset", write.id("u32"))},
		write.id("u32"), writeBody...)
	checkFn := check.fnRegions(checkName, regions, []*ast.FunctionParameter{check.param("value", valueType(check))}, check.id("Bool"), checkBody...)
	// The checked entry: the view lengths first (LengthMismatch names the
	// value's fault), then the destination once.
	checked := newSynth("codec:" + writeName)
	writeFn := checked.fnRegions(writeName, regions,
		[]*ast.FunctionParameter{checked.param("value", valueType(checked)), checked.param("dst", checked.span(checked.id("u8"))), checked.param("offset", checked.id("u32"))},
		result(checked),
		checked.expr(checked.cond(
			checked.not(checked.call(checkName, checked.id("value"))),
			checked.block(checked.expr(errVariant(checked, "LengthMismatch"))),
			checked.cond(
				checked.call("bytes_range_fits", checked.call("len", checked.id("dst")), checked.id("offset"), checked.u32(size)),
				checked.block(checked.expr(checked.variant("Ok", checked.call(uncheckedName, checked.id("value"), checked.id("dst"), checked.id("offset"))))),
				checked.block(checked.expr(errVariant(checked, "DestinationTooSmall")))))))
	encode := newSynth("codec:" + encodeName)
	encodeFn := encode.fnRegions(encodeName, regions,
		[]*ast.FunctionParameter{encode.param("value", valueType(encode)), encode.param("dst", encode.span(encode.id("u8")))},
		result(encode),
		encode.expr(encode.call(writeName, encode.id("value"), encode.id("dst"), encode.u32(0))))
	validFn := valid.fn(validName,
		[]*ast.FunctionParameter{valid.param("src", valid.view(valid.id("u8"))), valid.param("offset", valid.id("u32"))},
		valid.id("u32"), validBody...)
	readFn := read.fnRegions(readName, regions,
		[]*ast.FunctionParameter{read.param("src", srcType(read)), read.param("offset", read.id("u32"))},
		valueType(read), readBody...)
	decode := newSynth("codec:" + decodeName)
	decodeFn := decode.fnRegions(decodeName, regions,
		[]*ast.FunctionParameter{decode.param("src", srcType(decode))},
		decode.app("Result", valueType(decode), decode.id("BinaryDecodeError")),
		decode.expr(decode.cond(
			decode.call("bytes_range_fits", decode.call("len", decode.id("src")), decode.u32(0), decode.u32(size)),
			decode.block(
				decode.decl("fault", decode.id("u32"), decode.call(validName, decode.id("src"), decode.u32(0))),
				decode.expr(decode.cond(
					decode.eq(decode.id("fault"), decode.u32(0)),
					decode.block(decode.expr(decode.variant("Ok", decode.call(readName, decode.id("src"), decode.u32(0))))),
					decode.cond(
						decode.eq(decode.id("fault"), decode.u32(1)),
						decode.block(decode.expr(errVariant(decode, "InvalidBool"))),
						decode.block(decode.expr(errVariant(decode, "InvalidPresence"))))))),
			decode.block(decode.expr(errVariant(decode, "InputTooShort"))))))
	d.output = append(d.output, sizeFn, uncheckedFn, checkFn, writeFn, encodeFn, validFn, readFn, decodeFn)
	return nil
}
