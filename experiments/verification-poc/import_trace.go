package main

import (
	"fmt"
	"reflect"
	"strconv"
	"strings"
)

type Receipt struct {
	Format    string `json:"format"`
	Digest    string `json:"semantic_digest"`
	Backend   string `json:"backend"`
	QuerySHA  string `json:"query_sha256"`
	OutputSHA string `json:"output_sha256"`
	Bound     *int   `json:"bound"`
}

func receipt(m *Model, backend, query, raw string, bound *int) Receipt {
	return Receipt{"oak-go-trace-receipt-1", m.Digest, backend, digest(query), digest(raw), bound}
}
func sexprs(text string) (out []any, err error) {
	if len(text) > 20_000_000 {
		return nil, fmt.Errorf("solver output limit")
	}
	tokens := strings.Fields(strings.NewReplacer("(", " ( ", ")", " ) ").Replace(text))
	pos := 0
	var read func(int) (any, error)
	read = func(depth int) (any, error) {
		if pos >= len(tokens) || depth > 128 {
			return nil, fmt.Errorf("invalid S-expression")
		}
		token := tokens[pos]
		pos++
		if token == ")" {
			return nil, fmt.Errorf("unexpected closing parenthesis")
		}
		if token != "(" {
			return token, nil
		}
		a := []any{}
		for pos < len(tokens) && tokens[pos] != ")" {
			v, e := read(depth + 1)
			if e != nil {
				return nil, e
			}
			a = append(a, v)
		}
		if pos >= len(tokens) {
			return nil, fmt.Errorf("unterminated S-expression")
		}
		pos++
		return a, nil
	}
	for pos < len(tokens) {
		v, e := read(0)
		if e != nil {
			return nil, e
		}
		out = append(out, v)
	}
	return out, nil
}
func smtValue(m *Model, t string, raw any) any {
	if t == "Bool" {
		s, ok := raw.(string)
		demand(ok && (s == "true" || s == "false"), "expected SMT Boolean")
		return s == "true"
	}
	width := m.width(t)
	var n int64
	var e error
	if s, ok := raw.(string); ok && strings.HasPrefix(s, "#b") {
		demand(len(s)-2 == width, "bit-vector width mismatch")
		n, e = strconv.ParseInt(s[2:], 2, 32)
	} else if ok && strings.HasPrefix(s, "#x") {
		demand((len(s)-2)*4 == width, "bit-vector width mismatch")
		n, e = strconv.ParseInt(s[2:], 16, 32)
	} else {
		a := array(raw)
		demand(len(a) == 3 && str(a[0]) == "_" && strings.HasPrefix(str(a[1]), "bv") && str(a[2]) == strconv.Itoa(width), "invalid bit-vector")
		n, e = strconv.ParseInt(str(a[1])[2:], 10, 32)
	}
	demand(e == nil && n >= 0 && n < int64(1<<width), "invalid bit-vector value")
	if t == "u8" {
		return int(n)
	}
	demand(int(n) < len(m.Enums[t]), "unused enum encoding")
	return m.Enums[t][n]
}
func fromZ3(m *Model, text string, bound int) (states []State, err error) {
	defer func() {
		if e := recover(); e != nil {
			states = nil
			err = fmt.Errorf("invalid Z3 trace: %v", e)
		}
	}()
	demand(bound >= 0 && bound <= 64, "invalid bound")
	a, e := sexprs(text)
	if e != nil {
		return nil, e
	}
	demand(len(a) == 2 && str(a[0]) == "sat", "expected SAT plus get-value result")
	values := map[string]any{}
	for _, v := range array(a[1]) {
		pair := array(v)
		demand(len(pair) == 2, "invalid value pair")
		key := str(pair[0])
		_, present := values[key]
		demand(!present, "duplicate SMT variable")
		values[key] = pair[1]
	}
	demand(len(values) == (bound+1)*len(m.Fields), "SMT variable set mismatch")
	for i := 0; i <= bound; i++ {
		s := State{}
		for _, f := range m.Fields {
			key := fmt.Sprintf("s%d_f_%s", i, f.Name)
			v, ok := values[key]
			demand(ok, "missing SMT variable")
			s[f.Name] = smtValue(m, f.Type, v)
		}
		states = append(states, s)
	}
	return states, nil
}
func fromTLC(m *Model, text string) (states []State, err error) {
	defer func() {
		if e := recover(); e != nil {
			states = nil
			err = fmt.Errorf("invalid TLC trace: %v", e)
		}
	}()
	var raw map[string]any
	if e := decode([]byte(text), &raw); e != nil {
		return nil, e
	}
	vars := array(raw["vars"])
	demand(len(vars) == 1 && str(vars[0]) == "state", "unexpected TLC variable set")
	graph, ok := raw["counterexample"].(map[string]any)
	demand(ok, "missing TLC counterexample")
	entries := array(graph["state"])
	demand(len(entries) > 0 && len(entries) <= 4096, "invalid TLC trace size")
	levels := map[int]State{}
	for _, v := range entries {
		entry := array(v)
		demand(len(entry) == 2, "invalid TLC state entry")
		level, e := number(entry[0])
		demand(e == nil && level > 0 && levels[level] == nil, "invalid/duplicate TLC level")
		record, ok := entry[1].(map[string]any)
		demand(ok && len(record) == 1, "unexpected TLC state variables")
		fields, ok := record["state"].(map[string]any)
		demand(ok && len(fields) == len(m.Fields), "TLC fields mismatch")
		s := State{}
		for _, f := range m.Fields {
			v, ok := fields["f_"+f.Name]
			demand(ok, "missing TLC field")
			if m.Enums[f.Type] != nil {
				txt := str(v)
				demand(strings.HasPrefix(txt, f.Type+"."), "nominal enum mismatch")
				v = strings.TrimPrefix(txt, f.Type+".")
			}
			s[f.Name] = v
		}
		demand(m.valid(s) == nil, "invalid typed TLC state")
		levels[level] = s
	}
	for i := 1; i <= len(levels); i++ {
		demand(levels[i] != nil, "noncontiguous TLC levels")
		states = append(states, levels[i])
	}
	return states, nil
}
func importTrace(m *Model, backend, query, raw string, r Receipt, bound *int) (*Certificate, error) {
	if !reflect.DeepEqual(r, receipt(m, backend, query, raw, bound)) {
		return nil, fmt.Errorf("stale or mismatched trace receipt")
	}
	var states []State
	var e error
	switch backend {
	case "z3":
		if bound == nil {
			return nil, fmt.Errorf("missing BMC bound")
		}
		expected, err := bmc(m, *bound, true)
		if err != nil || query != expected {
			return nil, fmt.Errorf("wrong BMC query")
		}
		states, e = fromZ3(m, raw, *bound)
	case "tlc":
		files := project(m)
		if bound != nil || query != files["Model.tla"]+"\n"+files["Model.cfg"] {
			return nil, fmt.Errorf("wrong TLC specification/configuration")
		}
		states, e = fromTLC(m, raw)
	default:
		return nil, fmt.Errorf("unsupported trace backend")
	}
	if e != nil {
		return nil, e
	}
	if e := replay(m, states); e != nil {
		return nil, e
	}
	for i, s := range states {
		if !truth(m.Terms["invariant"], s, nil) {
			c := &Certificate{Format: evidenceFormat, Digest: m.Digest, Kind: "trace", States: states[:i+1]}
			_, e := verify(m, c)
			return c, e
		}
	}
	return nil, fmt.Errorf("trace has no safety violation")
}
