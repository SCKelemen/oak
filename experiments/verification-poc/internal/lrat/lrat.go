// Package lrat checks ASCII LRAT RUP additions and deletions. It has no Oak,
// encoder, producer, or external solver dependency. RAT hints are unsupported.
package lrat

import (
	"fmt"
	"strconv"
	"strings"
)

type Clause map[int]bool
type Formula struct {
	Variables int
	Clauses   []Clause
}
type Result struct {
	Accepted  bool `json:"accepted"`
	Additions int  `json:"additions"`
	Deletions int  `json:"deletions"`
}

func abs(x int) int {
	if x < 0 {
		return -x
	}
	return x
}
func integer(s string) (int, error) {
	n, err := strconv.Atoi(s)
	if err != nil || n < -2147483647 || n > 2147483647 {
		return 0, fmt.Errorf("invalid bounded integer %q", s)
	}
	return n, nil
}
func Parse(text string) (Formula, error) {
	var f Formula
	if len(text) > 20_000_000 {
		return f, fmt.Errorf("CNF input limit")
	}
	header := false
	expected := 0
	clause := Clause{}
	for _, line := range strings.Split(text, "\n") {
		words := strings.Fields(line)
		if len(words) == 0 || words[0] == "c" {
			continue
		}
		if words[0] == "p" {
			if header || len(words) != 4 || words[1] != "cnf" {
				return f, fmt.Errorf("invalid DIMACS header")
			}
			n, e := integer(words[2])
			if e != nil || n < 0 {
				return f, fmt.Errorf("invalid variable count")
			}
			m, e := integer(words[3])
			if e != nil || m < 0 {
				return f, fmt.Errorf("invalid clause count")
			}
			f.Variables = n
			expected = m
			header = true
			continue
		}
		if !header {
			return f, fmt.Errorf("missing DIMACS header")
		}
		for _, word := range words {
			n, e := integer(word)
			if e != nil {
				return f, e
			}
			if n == 0 {
				f.Clauses = append(f.Clauses, clause)
				clause = Clause{}
			} else {
				if abs(n) > f.Variables {
					return f, fmt.Errorf("literal outside variable domain")
				}
				clause[n] = true
			}
		}
	}
	if !header || len(clause) != 0 || len(f.Clauses) != expected {
		return f, fmt.Errorf("unterminated clause or count mismatch")
	}
	return f, nil
}
func rup(db map[int]Clause, c Clause, hints []int) error {
	assigned := Clause{}
	for x := range c {
		assigned[-x] = true
	}
	for _, id := range hints {
		if id <= 0 || db[id] == nil {
			return fmt.Errorf("unsupported RAT or absent/deleted/future hint")
		}
	}
	for x := range assigned {
		if assigned[-x] {
			return nil
		}
	}
	for i, id := range hints {
		remaining := 0
		unit := 0
		for x := range db[id] {
			if assigned[x] {
				return fmt.Errorf("hint is already satisfied")
			}
			if !assigned[-x] {
				remaining++
				unit = x
			}
		}
		if remaining == 0 {
			if i != len(hints)-1 {
				return fmt.Errorf("unused hints after conflict")
			}
			return nil
		}
		if remaining != 1 {
			return fmt.Errorf("hint is not unit or conflicting")
		}
		assigned[unit] = true
	}
	return fmt.Errorf("RUP chain has no conflict")
}
func Check(cnf, proof string) (Result, error) {
	result := Result{}
	if len(proof) > 50_000_000 {
		return result, fmt.Errorf("proof input limit")
	}
	f, err := Parse(cnf)
	if err != nil {
		return result, err
	}
	db := map[int]Clause{}
	empty := false
	for i, c := range f.Clauses {
		db[i+1] = c
		if len(c) == 0 {
			empty = true
		}
	}
	last := len(db)
	for index, line := range strings.Split(proof, "\n") {
		w := strings.Fields(line)
		if len(w) == 0 || w[0] == "c" {
			continue
		}
		fail := func(s string) (Result, error) { return result, fmt.Errorf("LRAT line %d: %s", index+1, s) }
		if len(w) < 3 {
			return fail("short line")
		}
		id, e := integer(w[0])
		if e != nil {
			return fail(e.Error())
		}
		if w[1] == "d" {
			if id < last || w[len(w)-1] != "0" {
				return fail("invalid deletion")
			}
			seen := map[int]bool{}
			for _, word := range w[2 : len(w)-1] {
				n, e := integer(word)
				if e != nil || n <= 0 || db[n] == nil || seen[n] {
					return fail("invalid deletion reference")
				}
				seen[n] = true
				delete(db, n)
				result.Deletions++
			}
			continue
		}
		if id <= last {
			return fail("addition IDs must increase")
		}
		nums := []int{}
		zeros := []int{}
		for _, word := range w[1:] {
			n, e := integer(word)
			if e != nil {
				return fail(e.Error())
			}
			if n == 0 {
				zeros = append(zeros, len(nums))
			}
			nums = append(nums, n)
		}
		if len(zeros) != 2 || zeros[1] != len(nums)-1 {
			return fail("expected two zero terminators")
		}
		c := Clause{}
		for _, x := range nums[:zeros[0]] {
			if abs(x) > f.Variables {
				return fail("undeclared variable")
			}
			c[x] = true
		}
		if e := rup(db, c, nums[zeros[0]+1:len(nums)-1]); e != nil {
			return fail(e.Error())
		}
		db[id] = c
		last = id
		result.Additions++
		if len(c) == 0 {
			empty = true
		}
	}
	if !empty {
		return result, fmt.Errorf("proof never establishes the empty clause")
	}
	result.Accepted = true
	return result, nil
}

// CheckRUPDecoded exposes one decoded RUP step for differential testing of
// bounded self-hosted kernels. Clauses and literals use DIMACS conventions.
func CheckRUPDecoded(variables int, clauses [][]int, target []int, hints []int) error {
	if variables <= 0 {
		return fmt.Errorf("invalid variable count")
	}
	db := map[int]Clause{}
	convert := func(xs []int) (Clause, error) {
		c := Clause{}
		for _, x := range xs {
			if x == 0 || abs(x) > variables {
				return nil, fmt.Errorf("literal outside variable domain")
			}
			c[x] = true
		}
		return c, nil
	}
	for i, xs := range clauses {
		c, e := convert(xs)
		if e != nil {
			return e
		}
		db[i+1] = c
	}
	c, e := convert(target)
	if e != nil {
		return e
	}
	return rup(db, c, hints)
}
