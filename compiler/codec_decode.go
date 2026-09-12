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
// value at an offset, __oak_json_locate_T reads a whole document and
// reports failures with their byte offset (Result[T, JsonFault]), and
// __oak_json_decode_T is the same document read with the offset dropped
// (Result[T, JsonDecodeError]). Every error site records the offset of
// the offending token — a value's start after whitespace, an unknown or
// duplicate key's start, the byte where a separator or colon was expected,
// the byte where UTF-8 failed — and nested failures pass theirs up
// (docs/spec/71-codecs.md section 13, "Positions").
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
	for _, operation := range []string{"read", "decode", "locate"} {
		if d.names[codecName(operation, typ)] {
			return fmt.Errorf("codec: generated name %s conflicts with a declaration", codecName(operation, typ))
		}
	}
	readName, decodeName, locateName := codecName("read", typ), codecName("decode", typ), codecName("locate", typ)
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
		readResult = s.app("Result", s.app(codecName("decoded", typ), s.id(region)), s.id("JsonFault"))
	}
	readFn := s.fnRegions(readName, regions,
		[]*ast.FunctionParameter{s.param("src", srcType(s)), s.param("offset", s.id("u32"))},
		readResult, body...)

	// For this derivation subset, successful complete parsing establishes
	// UTF-8: scalar values and delimiters are ASCII, and matched keys are
	// validated literals or pass Unicode decoding. On failure, scan the full
	// input to retain InvalidEncoding precedence even beyond the first
	// syntax error — positioned at the first ill-formed byte. A view field's
	// bytes are handed back unvalidated by the scan, so a borrowed record
	// also checks the input on success. The positioned root does the work;
	// the plain root drops the offset.
	loc := newSynth("codec:" + locateName)
	locateResult := loc.app("Result", loc.id(typ), loc.id("JsonFault"))
	readResultType := decodedResult(loc, typ)
	encodingFault := func(b *synth) ast.Expression {
		return faultVariant(b, "InvalidEncoding", b.call("json_utf8_first_error", b.id("src")))
	}
	var success ast.Expression = loc.block(loc.expr(loc.variant("Ok", loc.field(loc.id("item"), "value"))))
	if region != "" {
		locateResult = loc.app("Result", loc.app(typ, loc.id(region)), loc.id("JsonFault"))
		readResultType = loc.app("Result", loc.app(codecName("decoded", typ), loc.id(region)), loc.id("JsonFault"))
		success = loc.block(loc.expr(loc.cond(
			loc.call("json_valid_utf8", loc.id("src")),
			loc.block(loc.expr(loc.variant("Ok", loc.field(loc.id("item"), "value")))),
			loc.block(loc.expr(encodingFault(loc))))))
	}
	locateFn := loc.fnRegions(locateName, regions,
		[]*ast.FunctionParameter{loc.param("src", srcType(loc))},
		locateResult,
		loc.decl("result", readResultType, loc.call(readName, loc.id("src"), loc.u32(0))),
		loc.expr(loc.match(loc.id("result"),
			loc.arm("Err", "fault", loc.block(loc.expr(loc.cond(
				loc.call("json_valid_utf8", loc.id("src")),
				loc.block(loc.expr(loc.variant("Err", loc.id("fault")))),
				loc.block(loc.expr(encodingFault(loc))))))),
			loc.arm("Ok", "item", loc.block(
				loc.decl("trailing", loc.id("u32"), loc.call("json_skip_space", loc.id("src"), loc.field(loc.id("item"), "next"))),
				loc.expr(loc.cond(
					loc.ne(loc.id("trailing"), loc.call("len", loc.id("src"))),
					loc.block(loc.expr(loc.cond(
						loc.call("json_valid_utf8", loc.id("src")),
						loc.block(loc.expr(faultVariant(loc, "InvalidSyntax", loc.id("trailing")))),
						loc.block(loc.expr(encodingFault(loc)))))),
					success)))))))

	dec := newSynth("codec:" + decodeName)
	decodeResult := dec.app("Result", dec.id(typ), dec.id("JsonDecodeError"))
	locatedType := dec.app("Result", dec.id(typ), dec.id("JsonFault"))
	if region != "" {
		decodeResult = dec.app("Result", dec.app(typ, dec.id(region)), dec.id("JsonDecodeError"))
		locatedType = dec.app("Result", dec.app(typ, dec.id(region)), dec.id("JsonFault"))
	}
	decodeFn := dec.fnRegions(decodeName, regions,
		[]*ast.FunctionParameter{dec.param("src", srcType(dec))},
		decodeResult,
		dec.decl("located", locatedType, dec.call(locateName, dec.id("src"))),
		dec.expr(dec.match(dec.id("located"),
			dec.arm("Err", "fault", dec.block(dec.expr(dec.variant("Err", dec.field(dec.id("fault"), "error"))))),
			dec.arm("Ok", "value", dec.block(dec.expr(dec.variant("Ok", dec.id("value"))))))))
	if decodedDecl != nil {
		d.output = append(d.output, decodedDecl)
	}
	if keyFn != nil {
		d.output = append(d.output, keyFn)
	}
	d.output = append(d.output, readFn, locateFn, decodeFn)
	d.decodeGenerated[typ] = true
	return nil
}

// decodedResult is Result[JsonDecoded[T], JsonFault].
func decodedResult(s *synth, typ string) ast.Expression {
	return s.app("Result", s.app("JsonDecoded", s.id(typ)), s.id("JsonFault"))
}

// faultVariant is .Err(JsonFault { error: .Name, at: at }).
func faultVariant(s *synth, name string, at ast.Expression) ast.Expression {
	return s.variant("Err", s.record("JsonFault", s.set("error", s.variant(name, nil)), s.set("at", at)))
}

// faultCode is .Err(JsonFault { error: json_decode_error(code), at: at }).
func faultCode(s *synth, code, at ast.Expression) ast.Expression {
	return s.variant("Err", s.record("JsonFault", s.set("error", s.call("json_decode_error", code)), s.set("at", at)))
}

// errBlock is { .Err(JsonFault { error: .Name, at: at }) }.
func errBlock(s *synth, name string, at ast.Expression) ast.Expression {
	return s.block(s.expr(faultVariant(s, name, at)))
}

// valueStart is json_skip_space(src, from): a value's first byte, the
// position an error about that value reports. Called only on error paths.
func valueStart(s *synth, from ast.Expression) ast.Expression {
	return s.call("json_skip_space", s.id("src"), from)
}

// setFault records a failure inside a record reader — its code in `status`
// and the offending byte in `fault_at` — as a block expression, the shape
// the conditional branches take.
func setFault(s *synth, code int64, at ast.Expression) ast.Expression {
	return s.block(s.assign("status", s.u32(code)), s.assign("fault_at", at))
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
		success = s.cond(s.id("negative"), errBlock(s, "TypeMismatch", valueStart(s, s.id("offset"))),
			s.cond(s.gt(magnitude(), s.u64(maximum)), errBlock(s, "NumericOverflow", valueStart(s, s.id("offset"))),
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
			s.expr(s.cond(s.gt(magnitude(), s.id("limit")), errBlock(s, "NumericOverflow", valueStart(s, s.id("offset"))),
				decodedItem(s, typ, conversion, s.field(s.id("raw"), "next"),
					s.decl("number", s.id("i64"), s.i64(0)),
					sign))))
	}
	// The value's start after whitespace is the position of every error
	// the scanner or the width check reports; it is computed only on that
	// path, since the scanner skips the space itself (the hot path stays
	// one call, docs/spec/71-codecs.md section 19).
	return []ast.Statement{
		s.decl("raw", s.id("JsonIntegerScan"), s.call("json_scan_integer", s.id("src"), s.id("offset"))),
		s.decl("negative", s.id("Bool"), s.eq(s.field(s.id("raw"), "status"), s.u32(1))),
		s.expr(s.cond(s.gt(s.field(s.id("raw"), "status"), s.u32(1)),
			s.block(s.expr(faultCode(s, s.sub(s.field(s.id("raw"), "status"), s.u32(1)), valueStart(s, s.id("offset"))))),
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

// srcWord64 is the little-endian u64 of src[at+base .. at+base+7]; the
// backend coalesces the eight bytes into one checked load.
func srcWord64(s *synth, at func() ast.Expression, base int) ast.Expression {
	terms := make([]ast.Expression, 0, 8)
	for k := 0; k < 8; k++ {
		terms = append(terms, s.infix(s.conv("u64", s.index(s.id("src"), s.add(at(), s.u32(int64(base+k))))), "<<", s.u64(uint64(8*k))))
	}
	return s.chain("|", terms...)
}

// srcRemaining is the wrap-free guard that n bytes remain at `at`:
// `len(src) >= n && at <= len(src) - n`, the spelling the extent facts
// accept (docs/spec/50-borrowing.md), so the byte reads under it are
// proven and the packed loads carry no check.
func srcRemaining(s *synth, at func() ast.Expression, n int) ast.Expression {
	return s.and(s.ge(s.call("len", s.id("src")), s.u32(int64(n))),
		s.le(at(), s.sub(s.call("len", s.id("src")), s.u32(int64(n)))))
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
		s.expr(s.cond(s.le(kind(), s.u32(1)), errBlock(s, "InvalidSyntax", at()),
			s.cond(s.and(s.ne(kind(), s.u32(8)), s.ne(kind(), s.u32(9))), errBlock(s, "TypeMismatch", at()),
				decodedItem(s, "Bool", s.eq(kind(), s.u32(8)), s.field(s.id("part"), "end"))))),
	}
}

// scalarDecode decodes an integer or Boolean field in place inside a record
// reader: the scanner's status and the width check set `status`, a success
// stores the value, advances `at`, and runs `done`. Inlining the per-type
// reader saves its Result round trip — the aggregate return and the error
// code mapped to a variant and back — on the decoder's hot path
// (docs/spec/71-codecs.md section 19). Nil for any other type.
func scalarDecode(s *synth, typ string, from ast.Expression, store func(ast.Expression) ast.Statement, done ...ast.Statement) []ast.Statement {
	// Every failure of a scalar is positioned at the value's start after
	// whitespace, computed on the failure path only: the scanner skips the
	// space itself and the hot path stays one call.
	setStatus := func(code int64) ast.Expression { return setFault(s, code, valueStart(s, from)) }
	success := func(value ast.Expression, next ast.Expression, leading ...ast.Statement) ast.Expression {
		statements := append(leading, store(value), s.assign("at", next))
		return s.block(append(statements, done...)...)
	}
	switch codecPrimitive(typ) {
	case "u64", "i64":
		bits, _ := strconv.Atoi(typ[1:])
		magnitude := func() ast.Expression { return s.field(s.id("raw"), "magnitude") }
		next := func() ast.Expression { return s.field(s.id("raw"), "next") }
		negative := func() ast.Expression { return s.eq(s.field(s.id("raw"), "status"), s.u32(1)) }
		var checked ast.Expression
		if codecPrimitive(typ) == "u64" {
			maximum := ^uint64(0)
			if bits < 64 {
				maximum = (uint64(1) << bits) - 1
			}
			conversion := magnitude()
			if bits < 64 {
				conversion = s.call(typ+"_trunc_u64", magnitude())
			}
			checked = s.cond(negative(), setStatus(3),
				s.cond(s.gt(magnitude(), s.u64(maximum)), setStatus(4),
					success(conversion, next())))
		} else {
			negativeMax := uint64(1) << (bits - 1)
			conversion := ast.Expression(s.id("number"))
			if bits < 64 {
				conversion = s.call(typ+"_trunc_i64", s.id("number"))
			}
			sign := s.expr(s.cond(s.and(negative(), s.gt(magnitude(), s.u64(0))),
				s.block(s.assign("number", s.sub(s.sub(s.i64(0), s.call("i64_bits_u64", s.sub(magnitude(), s.u64(1)))), s.i64(1)))),
				s.block(s.assign("number", s.call("i64_bits_u64", magnitude())))))
			checked = s.block(
				s.decl("limit", s.id("u64"), s.cond(negative(), s.u64(negativeMax), s.u64(negativeMax-1))),
				s.expr(s.cond(s.gt(magnitude(), s.id("limit")), setStatus(4),
					success(conversion, next(), s.decl("number", s.id("i64"), s.i64(0)), sign))))
		}
		return []ast.Statement{
			s.decl("raw", s.id("JsonIntegerScan"), s.call("json_scan_integer", s.id("src"), from)),
			// A scanner status above one is json_decode_error_code + 1.
			s.expr(s.cond(s.gt(s.field(s.id("raw"), "status"), s.u32(1)),
				s.block(s.assign("status", s.sub(s.field(s.id("raw"), "status"), s.u32(1))), s.assign("fault_at", valueStart(s, from))),
				checked)),
		}
	case "bool":
		at := func() ast.Expression { return s.id("value_at") }
		kind := func() ast.Expression { return s.field(s.id("part"), "kind") }
		return []ast.Statement{
			s.decl("value_at", s.id("u32"), s.call("json_skip_space", s.id("src"), from)),
			s.decl("part", s.id("JsonToken"), nil),
			s.expr(s.cond(
				s.and(srcRemaining(s, at, 4), s.eq(srcWord(s, at, 0), s.u32(1702195828)), s.call("json_value_boundary", s.id("src"), s.add(at(), s.u32(4)))),
				s.block(s.assign("part", tokenAt(s, 8, at, 4))),
				s.cond(
					s.and(srcRemaining(s, at, 5), s.eq(srcWord(s, at, 0), s.u32(1936482662)), s.eq(s.index(s.id("src"), s.add(at(), s.u32(4))), s.u8(101)), s.call("json_value_boundary", s.id("src"), s.add(at(), s.u32(5)))),
					s.block(s.assign("part", tokenAt(s, 9, at, 5))),
					s.block(s.assign("part", s.call("json_token", s.id("src"), at())))))),
			s.expr(s.cond(s.le(kind(), s.u32(1)), setStatus(2),
				s.cond(s.and(s.ne(kind(), s.u32(8)), s.ne(kind(), s.u32(9))), setStatus(3),
					success(s.eq(kind(), s.u32(8)), s.field(s.id("part"), "end"))))),
		}
	}
	return nil
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
	// The tokenizer path is reached for escaped, non-ASCII, and unknown
	// keys. A key that decodes into sixty-four bytes is decoded once and
	// compared byte for byte against each spelling; one that does not fit
	// keeps the per-field Unicode comparison.
	var semantic ast.Expression = k.u32(0)
	var decoded ast.Expression = k.u32(0)
	for i := len(fields) - 1; i >= 0; i-- {
		semantic = k.cond(k.call("json_key_equal", k.id("src"), k.id("key"), k.id(fmt.Sprintf("key%d", i))), k.u32(int64(i+1)), semantic)
		decoded = k.cond(k.call("json_key_decoded_equal", k.id("decoded"), k.id(fmt.Sprintf("key%d", i))), k.u32(int64(i+1)), decoded)
	}
	body = append(body,
		k.decl("storage", k.array(64, k.id("u8")), nil),
		k.decl("decoded_len", k.id("u32"), k.call("json_key_decode", k.id("src"), k.id("key"), k.call("span", k.addressOf("storage")))),
		k.decl("storage_view", k.view(k.id("u8")), k.call("view", k.addressOf("storage"))),
		k.expr(k.cond(k.eq(k.id("decoded_len"), k.u32(4294967295)), k.block(k.expr(semantic)),
			k.block(
				k.decl("decoded", k.view(k.id("u8")), k.call("subslice", k.id("storage_view"), k.u32(0), k.id("decoded_len"))),
				k.expr(decoded)))))
	return k.fn(name, []*ast.FunctionParameter{k.param("src", k.view(k.id("u8"))), k.param("key", k.id("JsonToken"))}, k.id("u32"), body...)
}

// recordReader reads an object: braces, keys classified by the fast path
// or the classifier, each field decoded once, separators checked, and
// every field required.
func recordReader(s *synth, typ, keyName string, fields []codecField, decodedName string) []ast.Statement {
	at := func() ast.Expression { return s.id("at") }
	status := func() ast.Expression { return s.id("status") }
	srcLen := func() ast.Expression { return s.call("len", s.id("src")) }
	setStatus := func(code int64, at ast.Expression) ast.Expression { return setFault(s, code, at) }
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
	// A nested reader's fault passes its code and its position up.
	failArm := func() *ast.MatchArm {
		return s.arm("Err", "reason", s.block(
			s.assign("status", s.call("json_decode_error_code", s.field(s.id("reason"), "error"))),
			s.assign("fault_at", s.field(s.id("reason"), "at"))))
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
		s.decl("fault_at", s.id("u32"), s.intLit(0)),
		s.decl("done", s.id("Bool"), s.boolean(false)))
	for i := range fields {
		inner = append(inner, s.decl(fmt.Sprintf("seen%d", i), s.id("Bool"), s.boolean(false)))
	}
	// The whitespace after the brace is skipped once: the first key's
	// detection starts at `first`.
	inner = append(inner,
		s.decl("first", s.id("u32"), s.call("json_skip_space", s.id("src"), at())),
		s.assign("at", s.id("first")),
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
			if j == 0 && len(literal) >= 8 {
				var word uint64
				for k := 0; k < 8; k++ {
					word |= uint64(literal[k]) << (8 * k)
				}
				terms = append(terms, s.eq(srcWord64(s, at, 0), s.u64(word)))
				j += 8
			} else if len(literal)-j >= 4 {
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
	keyStart := func() ast.Expression { return s.field(s.id("key"), "start") }
	var dispatch ast.Expression = setStatus(7, keyStart())
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
					s.cond(s.le(s.field(s.id("token"), "kind"), s.u32(1)), setStatus(2, s.field(s.id("token"), "start")), setStatus(3, s.field(s.id("token"), "start"))))))
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
			if inline := scalarDecode(s, field.typ, colonEnd(), func(value ast.Expression) ast.Statement {
				return storeField(field.name, value)
			}, s.assign(seen, s.boolean(true))); inline != nil {
				decode = s.block(inline...)
				break
			}
			decode = s.block(
				s.decl(part, decodedResult(s, field.typ), readCall(field, colonEnd())),
				s.expr(s.match(s.id(part), failArm(), s.arm("Ok", "decoded", s.block(
					storeField(field.name, s.field(s.id("decoded"), "value")),
					s.assign("at", s.field(s.id("decoded"), "next")),
					s.assign(seen, s.boolean(true)))))))
		default:
			// After an element: at the declared length a closing bracket ends
			// the array and a comma means too many elements (LengthMismatch,
			// unless what follows is malformed); before it a comma continues
			// and a closing bracket means too few. One byte under its guard,
			// no token record; every fault is positioned at the byte read.
			sepEnd := func() ast.Expression { return s.add(s.id("separator_at"), s.u32(1)) }
			afterElement := []ast.Statement{
				s.decl("separator_at", s.id("u32"), s.call("json_skip_space", s.id("src"), at())),
				s.expr(s.cond(s.lt(s.id("separator_at"), srcLen()),
					s.block(
						s.decl("unit", s.id("u8"), s.index(s.id("src"), s.id("separator_at"))),
						s.expr(s.cond(s.eq(s.id("index"), s.u32(field.length)),
							s.block(s.expr(s.cond(s.eq(s.id("unit"), s.u8(93)), s.block(s.assign("at", sepEnd())),
								s.cond(s.eq(s.id("unit"), s.u8(44)), s.block(
									s.decl("extra", s.id("JsonToken"), s.call("json_token", s.id("src"), sepEnd())),
									s.expr(s.cond(s.or(s.le(s.field(s.id("extra"), "kind"), s.u32(1)), s.eq(s.field(s.id("extra"), "kind"), s.u32(12))),
										setStatus(2, s.field(s.id("extra"), "start")), setStatus(8, s.field(s.id("extra"), "start"))))),
									setStatus(2, s.id("separator_at")))))),
							s.cond(s.eq(s.id("unit"), s.u8(93)), setStatus(8, s.id("separator_at")),
								s.cond(s.eq(s.id("unit"), s.u8(44)), s.block(s.assign("at", sepEnd())), setStatus(2, s.id("separator_at"))))))),
					setStatus(2, s.id("separator_at")))),
			}
			// Each element decodes in place when it is a scalar; the per-type
			// reader otherwise.
			// A scalar element scans from the lookahead position, which the
			// closing-bracket test has already moved past the whitespace.
			var elementDecode ast.Expression
			if inline := scalarDecode(s, field.typ, s.id("lookahead"), func(value ast.Expression) ast.Statement {
				return s.store(s.index(fieldOf(field.name), s.id("index")), value)
			}, s.assign("index", s.add(s.id("index"), s.u32(1)))); inline != nil {
				elementDecode = s.block(inline...)
			} else {
				elementDecode = s.block(
					s.decl("part", decodedResult(s, field.typ), readCall(field, at())),
					s.expr(s.match(s.id("part"), failArm(), s.arm("Ok", "decoded", s.block(
						s.store(s.index(fieldOf(field.name), s.id("index")), s.field(s.id("decoded"), "value")),
						s.assign("at", s.field(s.id("decoded"), "next")),
						s.assign("index", s.add(s.id("index"), s.u32(1))))))))
			}
			// The opening bracket is one byte after whitespace; anything else
			// is classified by the tokenizer only to pick the error.
			decode = s.block(
				s.decl("array_at", s.id("u32"), s.call("json_skip_space", s.id("src"), colonEnd())),
				s.expr(s.cond(s.not(s.and(s.lt(s.id("array_at"), srcLen()), s.eq(s.index(s.id("src"), s.id("array_at")), s.u8(91)))),
					s.block(
						s.decl("array_start", s.id("JsonToken"), s.call("json_token", s.id("src"), s.id("array_at"))),
						s.expr(s.cond(s.le(s.field(s.id("array_start"), "kind"), s.u32(1)), setStatus(2, s.id("array_at")), setStatus(3, s.id("array_at"))))),
					s.block(
						s.assign("at", s.add(s.id("array_at"), s.u32(1))),
						s.decl("index", s.id("u32"), s.intLit(0)),
						s.loop(s.and(s.lt(s.id("index"), s.u32(field.length)), s.eq(status(), s.u32(0))),
							s.decl("lookahead", s.id("u32"), s.call("json_skip_space", s.id("src"), at())),
							s.expr(s.cond(s.and(s.lt(s.id("lookahead"), srcLen()), s.eq(s.index(s.id("src"), s.id("lookahead")), s.u8(93))),
								s.block(s.assign("status", s.cond(s.eq(s.id("index"), s.u32(0)), s.u32(8), s.u32(2))), s.assign("fault_at", s.id("lookahead"))),
								elementDecode)),
							s.expr(s.cond(s.eq(status(), s.u32(0)), s.block(afterElement...), nil))),
						s.assign(seen, s.eq(status(), s.u32(0)))))))
		}
		dispatch = s.cond(s.eq(s.id("field_index"), s.u32(int64(i+1))),
			s.block(s.expr(s.cond(s.id(seen), setStatus(6, keyStart()), decode))),
			dispatch)
	}

	// After a value: a comma continues, a closing brace ends, anything else
	// (the end of the input included) is InvalidSyntax at that byte — one
	// byte read under its own guard, no token record.
	afterValue := []ast.Statement{
		s.decl("separator_at", s.id("u32"), s.call("json_skip_space", s.id("src"), at())),
		s.expr(s.cond(s.lt(s.id("separator_at"), srcLen()),
			s.block(
				s.decl("unit", s.id("u8"), s.index(s.id("src"), s.id("separator_at"))),
				s.expr(s.cond(s.eq(s.id("unit"), s.u8(44)), s.block(s.assign("at", s.add(s.id("separator_at"), s.u32(1)))),
					s.cond(s.eq(s.id("unit"), s.u8(125)), s.block(s.assign("done", s.boolean(true)), s.assign("at", s.add(s.id("separator_at"), s.u32(1)))),
						setStatus(2, s.id("separator_at")))))),
			setStatus(2, s.id("separator_at")))),
	}

	inner = append(inner, s.loop(s.and(s.not(s.id("done")), s.eq(status(), s.u32(0))),
		s.assign("at", s.call("json_skip_space", s.id("src"), at())),
		s.decl("key", s.id("JsonToken"), nil),
		s.decl("field_index", s.id("u32"), s.intLit(0)),
		s.expr(detect),
		s.expr(s.cond(s.ne(s.field(s.id("key"), "kind"), s.u32(6)), setStatus(2, keyStart()), s.block(
			s.decl("colon_at", s.id("u32"), s.call("json_skip_space", s.id("src"), s.field(s.id("key"), "end"))),
			s.decl("colon", s.id("JsonToken"), s.record("JsonToken", s.set("kind", s.u32(4)), s.set("start", s.id("colon_at")), s.set("end", s.id("colon_at")))),
			s.expr(s.cond(s.or(s.ge(s.id("colon_at"), srcLen()), s.ne(s.index(s.id("src"), s.id("colon_at")), s.u8(58))), setStatus(2, s.id("colon_at")), s.block(
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
		s.block(s.expr(faultCode(s, status(), s.id("fault_at")))),
		s.cond(s.not(s.and(required...)), errBlock(s, "MissingField", at()), completed))))

	// The opening brace is one byte after whitespace; anything else is
	// classified by the tokenizer only to pick the error.
	return []ast.Statement{
		s.decl("open_at", s.id("u32"), s.call("json_skip_space", s.id("src"), s.id("offset"))),
		s.expr(s.cond(s.and(s.lt(s.id("open_at"), srcLen()), s.eq(s.index(s.id("src"), s.id("open_at")), s.u8(123))),
			s.block(append([]ast.Statement{s.decl("opening", s.id("JsonToken"), tokenAt(s, 2, func() ast.Expression { return s.id("open_at") }, 1))}, inner...)...),
			s.block(
				s.decl("opening", s.id("JsonToken"), s.call("json_token", s.id("src"), s.id("open_at"))),
				s.expr(s.cond(s.le(s.field(s.id("opening"), "kind"), s.u32(1)), errBlock(s, "InvalidSyntax", s.id("open_at")), errBlock(s, "TypeMismatch", s.id("open_at"))))))),
	}
}
