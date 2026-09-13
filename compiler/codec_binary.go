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
	// optional marks an Option[T] field: a presence byte, then T's bytes
	// (zeros when absent), so the layout stays fixed.
	optional bool
	// viewBytes is the byte count of a View[u8, R] field (typ "view"):
	// decoded as a subslice of the input, encoded by copying that many bytes.
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
		size, err := d.binaryFieldSize(field, active)
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

// binaryFieldSize is one element's size: the view's count, or the type's
// size plus the presence byte of an Option.
func (d *codecDeriver) binaryFieldSize(field binaryField, active map[string]bool) (int64, error) {
	if field.typ == "view" {
		return field.viewBytes, nil
	}
	size, err := d.binarySize(field.typ, active)
	if err != nil {
		return 0, err
	}
	if field.optional {
		size++
	}
	return size, nil
}

// binaryRegion is the single region a record's view fields share, or "".
func binaryRegion(typ string, fields []binaryField) (string, error) {
	region := ""
	for _, field := range fields {
		if field.typ != "view" {
			continue
		}
		if region != "" && region != field.region {
			return "", fmt.Errorf("codec: %s carries views in two regions; one region per record is derived", typ)
		}
		region = field.region
	}
	return region, nil
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
		if field.typ == "view" {
			// The byte run: its length was checked at the entry, so the copy
			// reads within the view and stores at k * 1 + off.
			n := field.viewBytes
			k := fmt.Sprintf("copy_%s_%d", field.name, s.next)
			s.next++
			out = append(out,
				s.decl(k, s.id("u32"), s.intLit(0)),
				s.loop(s.lt(s.id(k), s.u32(n)),
					s.store(s.index(s.id("dst"), at.inside(k, 1).at(s, off)), s.index(fieldPath(), s.id(k))),
					s.assign(k, s.add(s.id(k), s.u32(1)))))
			off += n
			continue
		}
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
		if field.optional {
			// The presence byte, then the payload — the bound value when
			// present, zeros when absent (nothing of a value leaks).
			present := fmt.Sprintf("present_%s_%d", field.name, s.next)
			s.next++
			someStores, err := element(func() ast.Expression { return s.id(present) }, at, off+1)
			if err != nil {
				return nil, err
			}
			someStores = append([]ast.Statement{s.store(s.index(s.id("dst"), at.at(s, off)), s.u8(1))}, someStores...)
			noneStores := []ast.Statement{s.store(s.index(s.id("dst"), at.at(s, off)), s.u8(0))}
			for k := int64(0); k < elemSize; k++ {
				noneStores = append(noneStores, s.store(s.index(s.id("dst"), at.at(s, off+1+k)), s.u8(0)))
			}
			out = append(out, s.expr(s.match(fieldPath(),
				s.arm("None", "", s.block(noneStores...)),
				s.arm("Some", present, s.block(someStores...)))))
			off += 1 + elemSize
			continue
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

// keepFault records a fault code when none is recorded yet: the first
// fault of the layout wins (1 a Bool byte above one, 2 a presence byte
// above one).
func keepFault(s *synth, condition ast.Expression, code int64) ast.Statement {
	return s.assign("fault", s.cond(s.and(s.eq(s.id("fault"), s.u32(0)), condition), s.u32(code), s.id("fault")))
}

// binaryDecodeRecord emits the loads of a record into the fields of `path`
// (rooted at the decoded local) — or, for a top-level record holding
// views, into the per-field locals `locals` names — and records each Bool
// byte's fault in `fault`. `guard`, when set, is a presence condition:
// the payload's Bool bytes are checked only when it holds.
func (d *codecDeriver) binaryDecodeRecord(s *synth, typ string, path func() ast.Expression, at binaryOffset, base int64, guard func() ast.Expression, locals map[string]string) ([]ast.Statement, error) {
	fields, err := d.binaryFields(typ)
	if err != nil {
		return nil, err
	}
	out := []ast.Statement{}
	off := base
	// put stores a loaded value into the field: an assignment when the
	// field lives in a local, a field store otherwise.
	put := func(field binaryField, value ast.Expression) ast.Statement {
		if local, isLocal := locals[field.name]; isLocal {
			return s.assign(local, value)
		}
		return s.store(s.field(path(), field.name), value)
	}
	boolFault := func(position ast.Expression) ast.Statement {
		condition := s.gt(s.index(s.id("src"), position), s.u8(1))
		if guard != nil {
			condition = s.and(guard(), condition)
		}
		return keepFault(s, condition, 1)
	}
	for _, field := range fields {
		into := func() *ast.IndexExpression { return s.field(path(), field.name) }
		fieldRoot := func() ast.Expression {
			if local, isLocal := locals[field.name]; isLocal {
				return s.id(local)
			}
			return s.field(path(), field.name)
		}
		if field.typ == "view" {
			// A subslice of the input: the layout's length test covers it.
			out = append(out, put(field, s.call("subslice", s.id("src"), at.at(s, off), s.u32(field.viewBytes))))
			off += field.viewBytes
			continue
		}
		elemSize, err := d.binarySize(field.typ, map[string]bool{})
		if err != nil {
			return nil, fmt.Errorf("codec field %s.%s: %w", typ, field.name, err)
		}
		element := func(target func() *ast.IndexExpression, at binaryOffset, off int64) ([]ast.Statement, error) {
			if binaryWidth(field.typ) == 0 {
				return d.binaryDecodeRecord(s, field.typ, func() ast.Expression { return target() }, at, off, guard, nil)
			}
			stmts := []ast.Statement{s.store(target(), binaryLoad(s, field.typ, field.bigEndian, at, off))}
			if field.typ == "Bool" {
				stmts = append(stmts, boolFault(at.at(s, off)))
			}
			return stmts, nil
		}
		if field.optional {
			// The presence byte decides; a present payload is read (and its
			// Bool bytes checked), an absent one's zeros are not inspected.
			presence := at.at(s, off)
			present := fmt.Sprintf("present_%s_%d", field.name, s.next)
			s.next++
			presentCondition := s.ne(s.index(s.id("src"), presence), s.u8(0))
			if guard != nil {
				presentCondition = s.and(guard(), presentCondition)
			}
			out = append(out,
				s.decl(present, s.id("Bool"), presentCondition))
			presenceFault := s.gt(s.index(s.id("src"), presence), s.u8(1))
			if guard != nil {
				presenceFault = s.and(guard(), presenceFault)
			}
			out = append(out, keepFault(s, presenceFault, 2))
			var payload ast.Expression
			if binaryWidth(field.typ) != 0 {
				payload = binaryLoad(s, field.typ, field.bigEndian, at, off+1)
				if field.typ == "Bool" {
					out = append(out, keepFault(s, s.and(s.id(present), s.gt(s.index(s.id("src"), at.at(s, off+1)), s.u8(1))), 1))
				}
			} else {
				// A record payload is read into a local under the presence guard.
				local := fmt.Sprintf("payload_%s_%d", field.name, s.next)
				s.next++
				loads, err := d.binaryDecodeRecord(s, field.typ, func() ast.Expression { return s.id(local) }, at, off+1, func() ast.Expression { return s.id(present) }, nil)
				if err != nil {
					return nil, err
				}
				out = append(out, s.decl(local, s.id(field.typ), nil))
				out = append(out, loads...)
				payload = s.id(local)
			}
			out = append(out, put(field, s.cond(s.id(present), s.variant("Some", payload), s.variant("None", nil))))
			off += 1 + elemSize
			continue
		}
		if field.length == 0 {
			if _, isLocal := locals[field.name]; isLocal && binaryWidth(field.typ) != 0 {
				out = append(out, put(field, binaryLoad(s, field.typ, field.bigEndian, at, off)))
				if field.typ == "Bool" {
					out = append(out, boolFault(at.at(s, off)))
				}
				off += elemSize
				continue
			}
			var stmts []ast.Statement
			if binaryWidth(field.typ) == 0 {
				stmts, err = d.binaryDecodeRecord(s, field.typ, fieldRoot, at, off, guard, nil)
			} else {
				stmts, err = element(into, at, off)
			}
			if err != nil {
				return nil, err
			}
			out = append(out, stmts...)
			off += elemSize
			continue
		}
		index := fmt.Sprintf("index_%s_%d", field.name, s.next)
		s.next++
		body, err := element(func() *ast.IndexExpression { return s.index(fieldRoot(), s.id(index)) }, at.inside(index, elemSize), off)
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

	// A record with View[u8, R] fields carries its region through every
	// generated function (docs/spec/50-borrowing.md section 8c): the value
	// type is T[R] and the input View[u8, R], so the decoded record borrows
	// the input it views. Nested records are inlined, so a nested record
	// with views is refused.
	var fields []binaryField
	region := ""
	if binaryWidth(typ) == 0 {
		if fields, err = d.binaryFields(typ); err != nil {
			return err
		}
		if region, err = binaryRegion(typ, fields); err != nil {
			return err
		}
		for _, field := range fields {
			if binaryWidth(field.typ) == 0 && field.typ != "view" {
				nested, err := d.binaryFields(field.typ)
				if err != nil {
					return fmt.Errorf("codec field %s.%s: %w", typ, field.name, err)
				}
				if nestedRegion, _ := binaryRegion(field.typ, nested); nestedRegion != "" {
					return fmt.Errorf("codec: %s.%s: a nested record with view fields is not derived; borrow at the top level", typ, field.name)
				}
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

	sizeS := newSynth("codec:" + sizeName)
	sizeFn := sizeS.fnRegions(sizeName, regions, []*ast.FunctionParameter{sizeS.param("value", valueType(sizeS))}, result(sizeS),
		sizeS.expr(sizeS.variant("Ok", sizeS.u32(size))))

	encode := newSynth("codec:" + encodeName)
	var stores []ast.Statement
	if binaryWidth(typ) != 0 {
		stores = binaryStores(encode, typ, false, func() ast.Expression { return encode.id("value") }, binaryOffset{}, 0)
	} else if stores, err = d.binaryEncodeRecord(encode, typ, func() ast.Expression { return encode.id("value") }, binaryOffset{}, 0); err != nil {
		return err
	}
	stores = append(stores, encode.expr(encode.variant("Ok", encode.u32(size))))
	var encodeBody ast.Expression = encode.cond(
		encode.ge(encode.call("len", encode.id("dst")), encode.u32(size)),
		encode.block(stores...),
		encode.block(encode.expr(errVariant(encode, "DestinationTooSmall"))))
	// Every view's length is the layout's count, checked before the
	// destination: LengthMismatch names the value's fault, bytes unchanged.
	var lengths []ast.Expression
	for _, field := range fields {
		if field.typ == "view" {
			lengths = append(lengths, encode.eq(encode.call("len", encode.field(encode.id("value"), field.name)), encode.u32(field.viewBytes)))
		}
	}
	if len(lengths) > 0 {
		encodeBody = encode.cond(encode.and(lengths...), encode.block(encode.expr(encodeBody)), encode.block(encode.expr(errVariant(encode, "LengthMismatch"))))
	}
	encodeFn := encode.fnRegions(encodeName, regions,
		[]*ast.FunctionParameter{encode.param("value", valueType(encode)), encode.param("dst", encode.span(encode.id("u8")))},
		result(encode),
		encode.expr(encodeBody))

	decode := newSynth("codec:" + decodeName)
	body := []ast.Statement{decode.decl("fault", decode.id("u32"), decode.intLit(0))}
	if binaryWidth(typ) != 0 {
		body = append(body, decode.decl("value", decode.id(typ), binaryLoad(decode, typ, false, binaryOffset{}, 0)))
		if typ == "Bool" {
			body = append(body, keepFault(decode, decode.gt(decode.index(decode.id("src"), decode.u32(0)), decode.u8(1)), 1))
		}
	} else if region == "" {
		body = append(body, decode.decl("value", decode.id(typ), nil))
		loads, err := d.binaryDecodeRecord(decode, typ, func() ast.Expression { return decode.id("value") }, binaryOffset{}, 0, nil, nil)
		if err != nil {
			return err
		}
		body = append(body, loads...)
	} else {
		// A record holding views: every field decodes into a local and the
		// record is built once at the end — no zero record holding views.
		locals := map[string]string{}
		var inits []recordInit
		for _, field := range fields {
			local := "field_" + field.name
			locals[field.name] = local
			inits = append(inits, decode.set(field.name, decode.id(local)))
			switch {
			case field.typ == "view":
				// declared at its subslice below
			case field.optional:
				body = append(body, decode.decl(local, decode.app("Option", decode.id(field.typ)), nil))
			case field.length > 0:
				body = append(body, decode.decl(local, decode.array(field.length, decode.id(field.typ)), nil))
			default:
				body = append(body, decode.decl(local, decode.id(field.typ), nil))
			}
		}
		loads, err := d.binaryDecodeRecord(decode, typ, func() ast.Expression { return decode.id("value") }, binaryOffset{}, 0, nil, locals)
		if err != nil {
			return err
		}
		// The view locals are declared by their subslice assignments: turn
		// those assignments into declarations.
		for i, stmt := range loads {
			if assign, isAssign := stmt.(*ast.AssignmentStatement); isAssign && strings.HasPrefix(assign.Name.Value, "field_") {
				name := strings.TrimPrefix(assign.Name.Value, "field_")
				for _, field := range fields {
					if field.name == name && field.typ == "view" {
						loads[i] = decode.decl(assign.Name.Value, decode.view(decode.id("u8")), assign.Value)
					}
				}
			}
		}
		body = append(body, loads...)
		body = append(body, decode.decl("value", valueType(decode), decode.record(typ, inits...)))
	}
	body = append(body, decode.expr(decode.cond(decode.eq(decode.id("fault"), decode.u32(0)),
		decode.block(decode.expr(decode.variant("Ok", decode.id("value")))),
		decode.cond(decode.eq(decode.id("fault"), decode.u32(1)),
			decode.block(decode.expr(errVariant(decode, "InvalidBool"))),
			decode.block(decode.expr(errVariant(decode, "InvalidPresence")))))))
	decodeFn := decode.fnRegions(decodeName, regions,
		[]*ast.FunctionParameter{decode.param("src", srcType(decode))},
		decode.app("Result", valueType(decode), decode.id("BinaryDecodeError")),
		decode.expr(decode.cond(
			decode.ge(decode.call("len", decode.id("src")), decode.u32(size)),
			decode.block(body...),
			decode.block(decode.expr(errVariant(decode, "InputTooShort"))))))
	d.output = append(d.output, sizeFn, encodeFn, decodeFn)
	return nil
}
