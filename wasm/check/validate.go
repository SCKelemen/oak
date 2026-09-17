// Package check decodes and validates Oak's bounded scalar Wasm byte profile.
// It depends only on the Go standard library, not on the emitter, compiler,
// or OptIR. Acceptance checks Wasm structure/types, NOT Oak correspondence,
// Bool domains, termination, host runtime correctness, or a proof certificate.
package check

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"unicode/utf8"
)

const (
	Profile          = "oak.wasm.scalar.v1"
	Validator        = "oak.wasm.check.v1"
	CoreSpecRevision = "779957d81feca2ec6a372c40a9130e28ef390645"
	MaxModuleBytes   = 1 << 20
	maxFunctions     = 128
	maxParameters    = 64
	maxLocals        = 16449 // SSA locals, parameters and dispatcher PC
	maxTotalLocals   = 65536
	maxInstructions  = 262144
	maxControlDepth  = 128
	maxStack         = 16384
)

type ValueType string

const (
	I32 ValueType = "i32"
	I64 ValueType = "i64"
)

type Export struct {
	Name       string      `json:"name"`
	Function   uint32      `json:"function"`
	Parameters []ValueType `json:"parameters"`
	Results    []ValueType `json:"results"`
}

// Report is diagnostic evidence about the exact SHA256 snapshot. It is not an
// admission token; callers must revalidate after changing bytes or metadata.
type Report struct {
	Profile       string   `json:"profile"`
	Validator     string   `json:"validator"`
	Specification string   `json:"specification"`
	SHA256        string   `json:"sha256"`
	Functions     int      `json:"functions"`
	Instructions  int      `json:"instructions"`
	Exports       []Export `json:"exports"`
}

type signature struct {
	parameters []ValueType
	results    []ValueType
}

// Validate snapshots data and checks the entire module without executing it.
// The profile is deliberately narrower than Core Wasm: unsupported sections
// and instructions fail closed, even where a general Wasm engine accepts them.
func Validate(data []byte) (Report, error) {
	if len(data) > MaxModuleBytes {
		return Report{}, fmt.Errorf("wasm check: module exceeds 1 MiB")
	}
	snapshot := append([]byte(nil), data...)
	r := reader{data: snapshot}
	if !bytes.Equal(r.take(8), []byte{0, 0x61, 0x73, 0x6d, 1, 0, 0, 0}) {
		r.fail("invalid Wasm magic/version")
	}
	var types, functions []signature
	out := Report{Profile: Profile, Validator: Validator, Specification: CoreSpecRevision, Exports: []Export{}}
	totalLocals := 0
	// Require each section exactly once, in order, with exact length coverage.
	// No custom sections, imports, start, memory or other ambient authority.
	for _, section := range []byte{1, 3, 7, 10} {
		if r.byte() != section {
			r.fail("expected section %d", section)
		}
		length := r.u32()
		s := r.sub(length)
		if s.err != nil {
			return Report{}, s.err
		}
		switch section {
		case 1:
			n := s.count(maxFunctions)
			if n == 0 {
				s.fail("no function types")
			}
			for i := 0; i < n && s.err == nil; i++ {
				if s.byte() != 0x60 {
					s.fail("expected function type")
				}
				var sig signature
				for j, count := 0, s.count(maxParameters); j < count && s.err == nil; j++ {
					sig.parameters = append(sig.parameters, s.valueType())
				}
				for j, count := 0, s.count(1); j < count && s.err == nil; j++ {
					sig.results = append(sig.results, s.valueType())
				}
				types = append(types, sig)
			}
		case 3:
			n := s.count(maxFunctions)
			if n == 0 {
				s.fail("no functions")
			}
			for i := 0; i < n && s.err == nil; i++ {
				idx := s.u32()
				if uint64(idx) >= uint64(len(types)) {
					s.fail("unknown type index %d", idx)
					break
				}
				functions = append(functions, types[idx])
			}
		case 7:
			names := map[string]bool{}
			for i, n := 0, s.count(maxFunctions); i < n && s.err == nil; i++ {
				nameLength := s.count(256)
				name := string(s.take(uint32(nameLength)))
				if name == "" || !utf8.ValidString(name) || names[name] {
					s.fail("invalid or duplicate export name")
					break
				}
				names[name] = true
				if s.byte() != 0 {
					s.fail("only function exports are admitted")
				}
				idx := s.u32()
				if uint64(idx) >= uint64(len(functions)) {
					s.fail("unknown export function %d", idx)
					break
				}
				sig := functions[idx]
				out.Exports = append(out.Exports, Export{Name: name, Function: idx, Parameters: append([]ValueType{}, sig.parameters...), Results: append([]ValueType{}, sig.results...)})
			}
		case 10:
			n := s.count(maxFunctions)
			if n != len(functions) {
				s.fail("function/code counts disagree")
			}
			for i := 0; i < n && s.err == nil; i++ {
				body := s.sub(s.u32())
				if err := validateBody(&body, functions[i], functions, &totalLocals, &out.Instructions); err != nil {
					return Report{}, fmt.Errorf("wasm check: function %d: %w", i, err)
				}
			}
		}
		if err := s.done(); err != nil {
			return Report{}, err
		}
	}
	if err := r.done(); err != nil {
		return Report{}, err
	}
	hash := sha256.Sum256(snapshot)
	out.SHA256 = hex.EncodeToString(hash[:])
	out.Functions = len(functions)
	return out, nil
}
