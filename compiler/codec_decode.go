package compiler

import (
	"fmt"
	"strconv"

	"github.com/SCKelemen/oak/ast"
)

// Decoder helpers return concrete values plus offsets, not a token tree or
// borrowed aggregate. Recursive calls follow the statically bounded schema.
// The functions are built as typed syntax (compiler/synth.go):
// __oak_json_key_T classifies an object key, __oak_json_read_T reads one
// value at an offset, __oak_json_decode_T reads a whole document.
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
	readName, decodeName := codecName("read", typ), codecName("decode", typ)
	s := newSynth("codec:" + readName)
	var body []ast.Statement
	var keyFn *ast.FunctionStatement
	// A record with View[u8, R] fields decodes as views of its input: the
	// reader and the decoder carry the region (docs/spec/50-borrowing.md
	// section 8c), and the reader's result is a per-type record declared
	// here, since the shared JsonDecoded[T] cannot carry a region.
	region := ""
	var decodedDecl *ast.ADTType
	switch codecPrimitive(typ) {
	case "u64", "i64":
		body = integerReader(s, typ)
	case "bool":
		body = boolReader(s)
	default:
		fields, err := d.fields(typ)
		if err != nil {
			return err
		}
		if region, err = viewRegion(typ, fields); err != nil {
			return err
		}
		for _, field := range fields {
			if field.view {
				continue
			}
			if err := d.deriveDecoder(field.typ); err != nil {
				return fmt.Errorf("codec field %s.%s: %w", typ, field.name, err)
			}
		}
		keyName := codecName("key", typ)
		if d.names[keyName] {
			return fmt.Errorf("codec: generated name %s conflicts with a declaration", keyName)
		}
		keyFn = keyClassifier(newSynth("codec:"+keyName), keyName, fields)
		decodedName := ""
		if region != "" {
			decodedName = codecName("decoded", typ)
			if d.names[decodedName] {
				return fmt.Errorf("codec: generated name %s conflicts with a declaration", decodedName)
			}
			decodedDecl = s.recordType(decodedName, []string{region},
				s.set("value", s.app(typ, s.id(region))), s.set("next", s.id("u32")))
		}
		body = recordReader(s, typ, keyName, fields, decodedName)
	}
	srcType := func(b *synth) ast.Expression {
		if region != "" {
			return b.app("View", b.id("u8"), b.id(region))
		}
		return b.view(b.id("u8"))
	}
	regions := []string{}
	if region != "" {
		regions = []string{region}
	}
	readResult := decodedResult(s, typ)
	if region != "" {
		readResult = s.app("Result", s.app(codecName("decoded", typ), s.id(region)), s.id("JsonDecodeError"))
	}
	readFn := s.fnRegions(readName, regions,
		[]*ast.FunctionParameter{s.param("src", srcType(s)), s.param("offset", s.id("u32"))},
		readResult, body...)

	// For this derivation subset, successful complete parsing establishes
	// UTF-8: scalar values and delimiters are ASCII, and matched keys are
	// validated literals or pass Unicode decoding. On failure, scan the full
	// input to retain InvalidEncoding precedence even beyond the first
	// syntax error. A view field's bytes are handed back unvalidated by the
	// scan, so a borrowed record also checks the input on success.
	dec := newSynth("codec:" + decodeName)
	decodeResult := dec.app("Result", dec.id(typ), dec.id("JsonDecodeError"))
	readResultType := decodedResult(dec, typ)
	var success ast.Expression = dec.block(dec.expr(dec.variant("Ok", dec.field(dec.id("item"), "value"))))
	if region != "" {
		decodeResult = dec.app("Result", dec.app(typ, dec.id(region)), dec.id("JsonDecodeError"))
		readResultType = dec.app("Result", dec.app(codecName("decoded", typ), dec.id(region)), dec.id("JsonDecodeError"))
		success = dec.block(dec.expr(dec.cond(
			dec.call("json_valid_utf8", dec.id("src")),
			dec.block(dec.expr(dec.variant("Ok", dec.field(dec.id("item"), "value")))),
			dec.block(dec.expr(errVariant(dec, "InvalidEncoding"))))))
	}
	decodeFn := dec.fnRegions(decodeName, regions,
		[]*ast.FunctionParameter{dec.param("src", srcType(dec))},
		decodeResult,
		dec.decl("result", readResultType, dec.call(readName, dec.id("src"), dec.u32(0))),
		dec.expr(dec.match(dec.id("result"),
			dec.arm("Err", "reason", dec.block(dec.expr(dec.cond(
				dec.call("json_valid_utf8", dec.id("src")),
				dec.block(dec.expr(dec.variant("Err", dec.id("reason")))),
				dec.block(dec.expr(errVariant(dec, "InvalidEncoding"))))))),
			dec.arm("Ok", "item", dec.block(dec.expr(dec.cond(
				dec.ne(dec.call("json_skip_space", dec.id("src"), dec.field(dec.id("item"), "next")), dec.call("len", dec.id("src"))),
				dec.block(dec.expr(dec.cond(
					dec.call("json_valid_utf8", dec.id("src")),
					dec.block(dec.expr(errVariant(dec, "InvalidSyntax"))),
					dec.block(dec.expr(errVariant(dec, "InvalidEncoding")))))),
				success)))))))
	if decodedDecl != nil {
		d.output = append(d.output, decodedDecl)
	}
	if keyFn != nil {
		d.output = append(d.output, keyFn)
	}
	d.output = append(d.output, readFn, decodeFn)
	d.decodeGenerated[typ] = true
	return nil
}

// decodedResult is Result[JsonDecoded[T], JsonDecodeError].
func decodedResult(s *synth, typ string) ast.Expression {
	return s.app("Result", s.app("JsonDecoded", s.id(typ)), s.id("JsonDecodeError"))
}

// errBlock is { .Err(.Name) }.
func errBlock(s *synth, name string) ast.Expression {
	return s.block(s.expr(errVariant(s, name)))
}

// decodedItem completes a reader: item: JsonDecoded[T]; item.value = value;
// item.next = next; .Ok(item), after the leading statements.
func decodedItem(s *synth, typ string, value, next ast.Expression, leading ...ast.Statement) ast.Expression {
	statements := append(leading,
		s.decl("item", s.app("JsonDecoded", s.id(typ)), nil),
		s.store(s.field(s.id("item"), "value"), value),
		s.store(s.field(s.id("item"), "next"), next),
		s.expr(s.variant("Ok", s.id("item"))))
	return s.block(statements...)
}

// integerReader scans an integer token and range-checks its magnitude for
// the fixed width: unsigned types reject a sign, signed types accept one
// more magnitude when negative.
func integerReader(s *synth, typ string) []ast.Statement {
	bits, _ := strconv.Atoi(typ[1:])
	magnitude := func() ast.Expression { return s.field(s.id("raw"), "magnitude") }
	var success ast.Expression
	if codecPrimitive(typ) == "u64" {
		maximum := ^uint64(0)
		if bits < 64 {
			maximum = (uint64(1) << bits) - 1
		}
		conversion := magnitude()
		if bits < 64 {
			conversion = s.call(typ+"_trunc_u64", magnitude())
		}
		success = s.cond(s.id("negative"), errBlock(s, "TypeMismatch"),
			s.cond(s.gt(magnitude(), s.u64(maximum)), errBlock(s, "NumericOverflow"),
				decodedItem(s, typ, conversion, s.field(s.id("raw"), "next"))))
	} else {
		negativeMax := uint64(1) << (bits - 1)
		conversion := ast.Expression(s.id("number"))
		if bits < 64 {
			conversion = s.call(typ+"_trunc_i64", s.id("number"))
		}
		// number = negative ? -(magnitude - 1) - 1 : magnitude, so the most
		// negative value never overflows the positive range on the way.
		sign := s.expr(s.cond(s.and(s.id("negative"), s.gt(magnitude(), s.u64(0))),
			s.block(s.assign("number", s.sub(s.sub(s.i64(0), s.call("i64_bits_u64", s.sub(magnitude(), s.u64(1)))), s.i64(1)))),
			s.block(s.assign("number", s.call("i64_bits_u64", magnitude())))))
		success = s.block(
			s.decl("limit", s.id("u64"), s.cond(s.id("negative"), s.u64(negativeMax), s.u64(negativeMax-1))),
			s.expr(s.cond(s.gt(magnitude(), s.id("limit")), errBlock(s, "NumericOverflow"),
				decodedItem(s, typ, conversion, s.field(s.id("raw"), "next"),
					s.decl("number", s.id("i64"), s.i64(0)),
					sign))))
	}
	return []ast.Statement{
		s.decl("raw", s.id("JsonIntegerScan"), s.call("json_scan_integer", s.id("src"), s.id("offset"))),
		s.decl("negative", s.id("Bool"), s.eq(s.field(s.id("raw"), "status"), s.u32(1))),
		s.expr(s.cond(s.gt(s.field(s.id("raw"), "status"), s.u32(1)),
			s.block(s.expr(s.variant("Err", s.call("json_decode_error", s.sub(s.field(s.id("raw"), "status"), s.u32(1)))))),
			success)),
	}
}

// srcWord is the little-endian u32 of src[at+base .. at+base+3], as the
// or of four shifted bytes.
func srcWord(s *synth, at func() ast.Expression, base int) ast.Expression {
	terms := make([]ast.Expression, 0, 4)
	for k := 0; k < 4; k++ {
		terms = append(terms, s.infix(s.conv("u32", s.index(s.id("src"), s.add(at(), s.u32(int64(base+k))))), "<<", s.u32(int64(8*k))))
	}
	return s.chain("|", terms...)
}

// srcRemaining is len(src) - at >= n.
func srcRemaining(s *synth, at func() ast.Expression, n int) ast.Expression {
	return s.ge(s.sub(s.call("len", s.id("src")), at()), s.u32(int64(n)))
}

// tokenAt is JsonToken { kind, start: at, end: at + n }.
func tokenAt(s *synth, kind int64, at func() ast.Expression, n int) ast.Expression {
	return s.record("JsonToken", s.set("kind", s.u32(kind)), s.set("start", at()), s.set("end", s.add(at(), s.u32(int64(n)))))
}

// boolReader matches the literals true and false by their packed bytes
// before falling back to the tokenizer.
func boolReader(s *synth) []ast.Statement {
	at := func() ast.Expression { return s.id("at") }
	kind := func() ast.Expression { return s.field(s.id("part"), "kind") }
	return []ast.Statement{
		s.decl("at", s.id("u32"), s.call("json_skip_space", s.id("src"), s.id("offset"))),
		s.decl("part", s.id("JsonToken"), nil),
		s.expr(s.cond(
			s.and(srcRemaining(s, at, 4), s.eq(srcWord(s, at, 0), s.u32(1702195828)), s.call("json_value_boundary", s.id("src"), s.add(at(), s.u32(4)))),
			s.block(s.assign("part", tokenAt(s, 8, at, 4))),
			s.cond(
				s.and(srcRemaining(s, at, 5), s.eq(srcWord(s, at, 0), s.u32(1936482662)), s.eq(s.index(s.id("src"), s.add(at(), s.u32(4))), s.u8(101)), s.call("json_value_boundary", s.id("src"), s.add(at(), s.u32(5)))),
				s.block(s.assign("part", tokenAt(s, 9, at, 5))),
				s.block(s.assign("part", s.call("json_token", s.id("src"), at())))))),
		s.expr(s.cond(s.le(kind(), s.u32(1)), errBlock(s, "InvalidSyntax"),
			s.cond(s.and(s.ne(kind(), s.u32(8)), s.ne(kind(), s.u32(9))), errBlock(s, "TypeMismatch"),
				decodedItem(s, "Bool", s.eq(kind(), s.u32(8)), s.field(s.id("part"), "end"))))),
	}
}

// keyClassifier maps an object key token to its 1-based field index, 0 for
// an unknown key. Key storage stays out of the record reader's live state.
func keyClassifier(k *synth, name string, fields []codecField) *ast.FunctionStatement {
	body := []ast.Statement{}
	for i, field := range fields {
		data := fmt.Sprintf("key%d_data", i)
		body = append(body, k.decl(data, k.array(int64(len(field.wire)), k.id("u8")), nil))
		for j, b := range []byte(field.wire) {
			body = append(body, k.store(k.index(k.id(data), k.intLit(int64(j))), k.u8(int64(b))))
		}
		body = append(body, k.decl(fmt.Sprintf("key%d", i), k.view(k.id("u8")), k.call("view", k.addressOf(data))))
	}
	var result ast.Expression = k.u32(0)
	for i := len(fields) - 1; i >= 0; i-- {
		result = k.cond(k.call("json_key_equal", k.id("src"), k.id("key"), k.id(fmt.Sprintf("key%d", i))), k.u32(int64(i+1)), result)
	}
	body = append(body, k.expr(result))
	return k.fn(name, []*ast.FunctionParameter{k.param("src", k.view(k.id("u8"))), k.param("key", k.id("JsonToken"))}, k.id("u32"), body...)
}

// separatorScan reads the byte after a value into separator.kind: 5 for a
// comma, 12 for a closing bracket, 3 for a closing brace, 1 otherwise.
func separatorScan(s *synth) []ast.Statement {
	return []ast.Statement{
		s.decl("separator_at", s.id("u32"), s.call("json_skip_space", s.id("src"), s.id("at"))),
		s.decl("separator", s.id("JsonToken"), s.record("JsonToken", s.set("kind", s.u32(1)), s.set("start", s.id("separator_at")), s.set("end", s.id("separator_at")))),
		s.expr(s.cond(s.lt(s.id("separator_at"), s.call("len", s.id("src"))), s.block(
			s.decl("unit", s.id("u8"), s.index(s.id("src"), s.id("separator_at"))),
			s.store(s.field(s.id("separator"), "kind"),
				s.cond(s.eq(s.id("unit"), s.u8(44)), s.u32(5),
					s.cond(s.eq(s.id("unit"), s.u8(93)), s.u32(12),
						s.cond(s.eq(s.id("unit"), s.u8(125)), s.u32(3), s.u32(1))))),
			s.store(s.field(s.id("separator"), "end"), s.add(s.id("separator_at"), s.u32(1)))), nil)),
	}
}

// recordReader reads an object: braces, keys classified by the fast path
// or the classifier, each field decoded once, separators checked, and
// every field required.
func recordReader(s *synth, typ, keyName string, fields []codecField, decodedName string) []ast.Statement {
	at := func() ast.Expression { return s.id("at") }
	status := func() ast.Expression { return s.id("status") }
	srcLen := func() ast.Expression { return s.call("len", s.id("src")) }
	setStatus := func(code int64) ast.Statement { return s.assign("status", s.u32(code)) }
	// A borrowed record (decodedName set) cannot start from a zero record
	// holding views, so its fields decode into locals — a view's start and
	// length as two words — and the record is built once at the end.
	views := decodedName != ""
	local := func(i int) string { return fmt.Sprintf("field%d", i) }
	fieldIndex := map[string]int{}
	for i, field := range fields {
		fieldIndex[field.name] = i
	}
	fieldOf := func(name string) ast.Expression {
		if views {
			return s.id(local(fieldIndex[name]))
		}
		return s.field(s.id("value"), name)
	}
	storeField := func(name string, value ast.Expression) ast.Statement {
		if views {
			return s.assign(local(fieldIndex[name]), value)
		}
		return s.store(s.field(s.id("value"), name), value)
	}
	readCall := func(field codecField, from ast.Expression) ast.Expression {
		return s.call(codecName("read", field.typ), s.id("src"), from)
	}
	failArm := func() *ast.MatchArm {
		return s.arm("Err", "reason", s.block(s.assign("status", s.call("json_decode_error_code", s.id("reason")))))
	}

	inner := []ast.Statement{}
	if views {
		for i, field := range fields {
			switch {
			case field.view:
				inner = append(inner,
					s.decl(local(i)+"_start", s.id("u32"), s.intLit(0)),
					s.decl(local(i)+"_len", s.id("u32"), s.intLit(0)))
			case field.nullable:
				inner = append(inner, s.decl(local(i), s.app("Option", s.id(field.typ)), nil))
			case field.length > 0:
				inner = append(inner, s.decl(local(i), s.array(field.length, s.id(field.typ)), nil))
			default:
				inner = append(inner, s.decl(local(i), s.id(field.typ), nil))
			}
		}
	} else {
		inner = append(inner, s.decl("value", s.id(typ), nil))
	}
	inner = append(inner,
		s.decl("at", s.id("u32"), s.field(s.id("opening"), "end")),
		s.decl("status", s.id("u32"), s.intLit(0)),
		s.decl("done", s.id("Bool"), s.boolean(false)))
	for i := range fields {
		inner = append(inner, s.decl(fmt.Sprintf("seen%d", i), s.id("Bool"), s.boolean(false)))
	}
	inner = append(inner,
		s.decl("first", s.id("u32"), s.call("json_skip_space", s.id("src"), at())),
		s.expr(s.cond(s.and(s.lt(s.id("first"), srcLen()), s.eq(s.index(s.id("src"), s.id("first")), s.u8(125))),
			s.block(s.assign("done", s.boolean(true)), s.assign("at", s.add(s.id("first"), s.u32(1)))), nil)))

	// Key detection: match bounded literal spellings directly; escaped and
	// unusual keys retain the full tokenizer and Unicode comparison path.
	var detect ast.Expression = s.cond(s.boolean(true), s.block(
		s.assign("key", s.call("json_token", s.id("src"), at())),
		s.assign("field_index", s.call(keyName, s.id("src"), s.id("key")))), nil)
	for i := len(fields) - 1; i >= 0; i-- {
		literal := []byte("\"" + fields[i].wire + "\"")
		plain := len(literal) <= 34
		for _, b := range []byte(fields[i].wire) {
			plain = plain && b >= 32 && b < 127 && b != '\\' && b != '"'
		}
		if !plain {
			continue
		}
		terms := []ast.Expression{srcRemaining(s, at, len(literal))}
		for j := 0; j < len(literal); {
			if len(literal)-j >= 4 {
				var word uint32
				for k := 0; k < 4; k++ {
					word |= uint32(literal[j+k]) << (8 * k)
				}
				terms = append(terms, s.eq(srcWord(s, at, j), s.u32(int64(word))))
				j += 4
			} else {
				terms = append(terms, s.eq(s.index(s.id("src"), s.add(at(), s.u32(int64(j)))), s.u8(int64(literal[j]))))
				j++
			}
		}
		detect = s.cond(s.and(terms...), s.block(
			s.assign("field_index", s.u32(int64(i+1))),
			s.assign("key", tokenAt(s, 6, at, len(literal)))), detect)
	}

	// Field dispatch on field_index, innermost first.
	var dispatch ast.Expression = s.block(setStatus(7))
	for i := len(fields) - 1; i >= 0; i-- {
		field := fields[i]
		seen := fmt.Sprintf("seen%d", i)
		part := fmt.Sprintf("part%d", i)
		colonEnd := func() ast.Expression { return s.field(s.id("colon"), "end") }
		var decode ast.Expression
		switch {
		case field.view:
			// The string token, quotes included, becomes the view: its
			// start and length are kept until the record is built.
			decode = s.block(
				s.decl("token", s.id("JsonToken"), s.call("json_token", s.id("src"), colonEnd())),
				s.expr(s.cond(s.eq(s.field(s.id("token"), "kind"), s.u32(6)),
					s.block(
						s.assign(local(i)+"_start", s.field(s.id("token"), "start")),
						s.assign(local(i)+"_len", s.sub(s.field(s.id("token"), "end"), s.field(s.id("token"), "start"))),
						s.assign("at", s.field(s.id("token"), "end")),
						s.assign(seen, s.boolean(true))),
					s.cond(s.le(s.field(s.id("token"), "kind"), s.u32(1)), s.block(setStatus(2)), s.block(setStatus(3))))))
		case field.nullable:
			decode = s.block(
				s.decl("token", s.id("JsonToken"), s.call("json_token", s.id("src"), colonEnd())),
				s.expr(s.cond(s.eq(s.field(s.id("token"), "kind"), s.u32(10)),
					s.block(
						s.decl("absent", s.app("Option", s.id(field.typ)), s.variant("None", nil)),
						storeField(field.name, s.id("absent")),
						s.assign("at", s.field(s.id("token"), "end")),
						s.assign(seen, s.boolean(true))),
					s.block(
						s.decl(part, decodedResult(s, field.typ), readCall(field, colonEnd())),
						s.expr(s.match(s.id(part), failArm(), s.arm("Ok", "decoded", s.block(
							s.decl("present", s.app("Option", s.id(field.typ)), s.variant("Some", s.field(s.id("decoded"), "value"))),
							storeField(field.name, s.id("present")),
							s.assign("at", s.field(s.id("decoded"), "next")),
							s.assign(seen, s.boolean(true))))))))))
		case field.length == 0:
			decode = s.block(
				s.decl(part, decodedResult(s, field.typ), readCall(field, colonEnd())),
				s.expr(s.match(s.id(part), failArm(), s.arm("Ok", "decoded", s.block(
					storeField(field.name, s.field(s.id("decoded"), "value")),
					s.assign("at", s.field(s.id("decoded"), "next")),
					s.assign(seen, s.boolean(true)))))))
		default:
			sepKind := func() ast.Expression { return s.field(s.id("separator"), "kind") }
			sepEnd := func() ast.Expression { return s.field(s.id("separator"), "end") }
			afterElement := append(separatorScan(s),
				s.expr(s.cond(s.eq(s.id("index"), s.u32(field.length)),
					s.block(s.expr(s.cond(s.eq(sepKind(), s.u32(12)), s.block(s.assign("at", sepEnd())),
						s.cond(s.eq(sepKind(), s.u32(5)), s.block(
							s.decl("extra", s.id("JsonToken"), s.call("json_token", s.id("src"), sepEnd())),
							s.expr(s.cond(s.or(s.le(s.field(s.id("extra"), "kind"), s.u32(1)), s.eq(s.field(s.id("extra"), "kind"), s.u32(12))),
								s.block(setStatus(2)), s.block(setStatus(8))))),
							s.block(setStatus(2)))))),
					s.cond(s.eq(sepKind(), s.u32(12)), s.block(setStatus(8)),
						s.cond(s.eq(sepKind(), s.u32(5)), s.block(s.assign("at", sepEnd())), s.block(setStatus(2)))))))
			decode = s.block(
				s.decl("array_start", s.id("JsonToken"), s.call("json_token", s.id("src"), colonEnd())),
				s.expr(s.cond(s.le(s.field(s.id("array_start"), "kind"), s.u32(1)), s.block(setStatus(2)),
					s.cond(s.ne(s.field(s.id("array_start"), "kind"), s.u32(11)), s.block(setStatus(3)),
						s.block(
							s.assign("at", s.field(s.id("array_start"), "end")),
							s.decl("index", s.id("u32"), s.intLit(0)),
							s.loop(s.and(s.lt(s.id("index"), s.u32(field.length)), s.eq(status(), s.u32(0))),
								s.decl("lookahead", s.id("u32"), s.call("json_skip_space", s.id("src"), at())),
								s.expr(s.cond(s.and(s.lt(s.id("lookahead"), srcLen()), s.eq(s.index(s.id("src"), s.id("lookahead")), s.u8(93))),
									s.block(s.assign("status", s.cond(s.eq(s.id("index"), s.u32(0)), s.u32(8), s.u32(2)))),
									s.block(
										s.decl("part", decodedResult(s, field.typ), readCall(field, at())),
										s.expr(s.match(s.id("part"), failArm(), s.arm("Ok", "decoded", s.block(
											s.store(s.index(fieldOf(field.name), s.id("index")), s.field(s.id("decoded"), "value")),
											s.assign("at", s.field(s.id("decoded"), "next")),
											s.assign("index", s.add(s.id("index"), s.u32(1)))))))))),
								s.expr(s.cond(s.eq(status(), s.u32(0)), s.block(afterElement...), nil))),
							s.assign(seen, s.eq(status(), s.u32(0))))))))
		}
		dispatch = s.cond(s.eq(s.id("field_index"), s.u32(int64(i+1))),
			s.block(s.expr(s.cond(s.id(seen), s.block(setStatus(6)), decode))),
			dispatch)
	}

	sepKind := func() ast.Expression { return s.field(s.id("separator"), "kind") }
	afterValue := append(separatorScan(s),
		s.expr(s.cond(s.eq(sepKind(), s.u32(3)), s.block(s.assign("done", s.boolean(true)), s.assign("at", s.field(s.id("separator"), "end"))),
			s.cond(s.eq(sepKind(), s.u32(5)), s.block(s.assign("at", s.field(s.id("separator"), "end"))), s.block(setStatus(2))))))

	inner = append(inner, s.loop(s.and(s.not(s.id("done")), s.eq(status(), s.u32(0))),
		s.assign("at", s.call("json_skip_space", s.id("src"), at())),
		s.decl("key", s.id("JsonToken"), nil),
		s.decl("field_index", s.id("u32"), s.intLit(0)),
		s.expr(detect),
		s.expr(s.cond(s.ne(s.field(s.id("key"), "kind"), s.u32(6)), s.block(setStatus(2)), s.block(
			s.decl("colon_at", s.id("u32"), s.call("json_skip_space", s.id("src"), s.field(s.id("key"), "end"))),
			s.decl("colon", s.id("JsonToken"), s.record("JsonToken", s.set("kind", s.u32(4)), s.set("start", s.id("colon_at")), s.set("end", s.id("colon_at")))),
			s.expr(s.cond(s.or(s.ge(s.id("colon_at"), srcLen()), s.ne(s.index(s.id("src"), s.id("colon_at")), s.u8(58))), s.block(setStatus(2)), s.block(
				s.store(s.field(s.id("colon"), "end"), s.add(s.id("colon_at"), s.u32(1))),
				s.expr(dispatch))))))),
		s.expr(s.cond(s.eq(status(), s.u32(0)), s.block(afterValue...), nil))))

	required := []ast.Expression{s.boolean(true)}
	for i := range fields {
		required = append(required, s.id(fmt.Sprintf("seen%d", i)))
	}
	var completed ast.Expression = decodedItem(s, typ, s.id("value"), at())
	if views {
		var build []ast.Statement
		var inits []recordInit
		for i, field := range fields {
			if field.view {
				build = append(build, s.decl(local(i), s.view(s.id("u8")),
					s.call("subslice", s.id("src"), s.id(local(i)+"_start"), s.id(local(i)+"_len"))))
			}
			inits = append(inits, s.set(field.name, s.id(local(i))))
		}
		build = append(build,
			s.decl("value", s.id(typ), s.record(typ, inits...)),
			s.decl("item", s.id(decodedName), s.record(decodedName, s.set("value", s.id("value")), s.set("next", at()))),
			s.expr(s.variant("Ok", s.id("item"))))
		completed = s.block(build...)
	}
	inner = append(inner, s.expr(s.cond(s.ne(status(), s.u32(0)),
		s.block(s.expr(s.variant("Err", s.call("json_decode_error", status())))),
		s.cond(s.not(s.and(required...)), errBlock(s, "MissingField"), completed))))

	return []ast.Statement{
		s.decl("opening", s.id("JsonToken"), s.call("json_token", s.id("src"), s.id("offset"))),
		s.expr(s.cond(s.le(s.field(s.id("opening"), "kind"), s.u32(1)), errBlock(s, "InvalidSyntax"),
			s.cond(s.ne(s.field(s.id("opening"), "kind"), s.u32(2)), errBlock(s, "TypeMismatch"),
				s.block(inner...)))),
	}
}
