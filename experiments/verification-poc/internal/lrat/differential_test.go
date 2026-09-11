package lrat

import (
	"encoding/json"
	"fmt"
	"math/rand"
	"os"
	"strings"
	"testing"
)

// This corpus checks decisions, not error wording. JSON is a test transport;
// it is not a replacement for the production DIMACS/LRAT parsers.
type commandCase struct {
	Kind   string `json:"kind"`
	ID     int    `json:"id"`
	Clause []int  `json:"clause"`
	Hints  []int  `json:"hints"`
	IDs    []int  `json:"ids"`
}
type differentialCase struct {
	Name      string        `json:"name"`
	Kind      string        `json:"kind"`
	Variables int           `json:"variables"`
	Database  [][]int       `json:"database"`
	Clause    []int         `json:"clause"`
	Hints     []int         `json:"hints"`
	Commands  []commandCase `json:"commands"`
	Expected  bool          `json:"expected"`
}

func literalSet(xs []int) Clause {
	c := Clause{}
	for _, x := range xs {
		c[x] = true
	}
	return c
}
func clauseMask(variables, mask int) []int {
	out := []int{}
	for v := 1; v <= variables; v++ {
		if mask&(1<<(2*(v-1))) != 0 {
			out = append(out, v)
		}
		if mask&(1<<(2*(v-1)+1)) != 0 {
			out = append(out, -v)
		}
	}
	return out
}
func clauseTrue(c []int, assignment int) bool {
	for _, x := range c {
		if (assignment&(1<<(abs(x)-1)) != 0) == (x > 0) {
			return true
		}
	}
	return false
}
func entails(db [][]int, target []int, variables int) bool {
	for assignment := 0; assignment < 1<<variables; assignment++ {
		model := true
		for _, c := range db {
			if !clauseTrue(c, assignment) {
				model = false
				break
			}
		}
		if model && !clauseTrue(target, assignment) {
			return false
		}
	}
	return true
}
func emitNumbers(b *strings.Builder, xs []int) {
	for _, x := range xs {
		fmt.Fprintf(b, "%d ", x)
	}
	b.WriteString("0")
}
func proofTexts(c differentialCase) (string, string) {
	var cnf, proof strings.Builder
	fmt.Fprintf(&cnf, "p cnf %d %d\n", c.Variables, len(c.Database))
	for _, clause := range c.Database {
		emitNumbers(&cnf, clause)
		cnf.WriteByte('\n')
	}
	for _, command := range c.Commands {
		fmt.Fprintf(&proof, "%d ", command.ID)
		if command.Kind == "delete" {
			proof.WriteString("d ")
			emitNumbers(&proof, command.IDs)
		} else {
			emitNumbers(&proof, command.Clause)
			proof.WriteByte(' ')
			emitNumbers(&proof, command.Hints)
		}
		proof.WriteByte('\n')
	}
	return cnf.String(), proof.String()
}
func proofDecision(c differentialCase) bool {
	cnf, proof := proofTexts(c)
	result, err := Check(cnf, proof)
	return err == nil && result.Accepted
}
func TestLeanDifferentialCorpus(t *testing.T) {
	cases := []differentialCase{}
	add := func(c differentialCase) {
		c.Name = fmt.Sprintf("%s-%05d", c.Kind, len(cases))
		if c.Clause == nil {
			c.Clause = []int{}
		}
		if c.Hints == nil {
			c.Hints = []int{}
		}
		if c.Commands == nil {
			c.Commands = []commandCase{}
		}
		if c.Database == nil {
			c.Database = [][]int{}
		}
		for i := range c.Commands {
			if c.Commands[i].Clause == nil {
				c.Commands[i].Clause = []int{}
			}
			if c.Commands[i].Hints == nil {
				c.Commands[i].Hints = []int{}
			}
			if c.Commands[i].IDs == nil {
				c.Commands[i].IDs = []int{}
			}
		}
		if c.Kind == "rup" {
			db := map[int]Clause{}
			for i, clause := range c.Database {
				db[i+1] = literalSet(clause)
			}
			c.Expected = rup(db, literalSet(c.Clause), c.Hints) == nil
			if c.Expected && !entails(c.Database, c.Clause, c.Variables) {
				t.Fatalf("unsound RUP: %+v", c)
			}
		} else {
			c.Expected = proofDecision(c)
			if c.Expected && !entails(c.Database, nil, c.Variables) {
				t.Fatalf("unsound proof: %+v", c)
			}
		}
		cases = append(cases, c)
	}
	// Exhaust all one-variable clauses, two-entry databases, target clauses,
	// and hint chains of length 0..3 over RAT, zero, live, and absent IDs.
	hints := [][]int{{}}
	frontier := [][]int{{}}
	for depth := 0; depth < 3; depth++ {
		next := [][]int{}
		for _, prefix := range frontier {
			for _, id := range []int{-1, 0, 1, 2, 3} {
				h := append(append([]int{}, prefix...), id)
				next = append(next, h)
				hints = append(hints, h)
			}
		}
		frontier = next
	}
	for a := 0; a < 4; a++ {
		for b := 0; b < 4; b++ {
			for target := 0; target < 4; target++ {
				for _, h := range hints {
					add(differentialCase{Kind: "rup", Variables: 1, Database: [][]int{clauseMask(1, a), clauseMask(1, b)}, Clause: clauseMask(1, target), Hints: h})
				}
			}
		}
	}
	// Seeded larger clauses exercise multi-unit chains and duplicate literals.
	rng := rand.New(rand.NewSource(20260907))
	for i := 0; i < 512; i++ {
		db := [][]int{}
		for j := 0; j < 4; j++ {
			db = append(db, clauseMask(3, rng.Intn(64)))
		}
		target := clauseMask(3, rng.Intn(64))
		if len(target) > 0 && i%2 == 0 {
			target = append(target, target[0])
		}
		h := []int{}
		for j, length := 0, rng.Intn(6); j < length; j++ {
			h = append(h, 1+rng.Intn(5))
		}
		add(differentialCase{Kind: "rup", Variables: 3, Database: db, Clause: target, Hints: h})
	}
	for _, h := range [][]int{{1, 2, 3}, {2, 1, 3}, {1, 1, 2, 3}, {1, 2}, {1, 2, 3, 1}} {
		add(differentialCase{Kind: "rup", Variables: 2, Database: [][]int{{1}, {-1, 2}, {-2}}, Hints: h})
	}
	add(differentialCase{Kind: "rup", Variables: 2, Database: [][]int{{1}, {-1, 2}}, Clause: []int{2}, Hints: []int{1, 2}})
	add(differentialCase{Kind: "proof", Variables: 2, Database: [][]int{{1}, {-1, 2}, {-2}}, Commands: []commandCase{
		{Kind: "add", ID: 4, Hints: []int{1, 2, 3}},
	}})
	add(differentialCase{Kind: "proof", Variables: 0})
	add(differentialCase{Kind: "proof", Variables: 0, Database: [][]int{{}}, Commands: []commandCase{
		{Kind: "delete", ID: 1, IDs: []int{1}},
	}})
	// Decoded stream tests cover ordering, deletion, reuse, and validation
	// after an empty clause has already been established.
	operations := []commandCase{
		{Kind: "add", ID: 3, Hints: []int{1, 2}},
		{Kind: "add", ID: 4, Hints: []int{1, 2}},
		{Kind: "add", ID: 3, Clause: []int{1}, Hints: []int{1}},
		{Kind: "add", ID: 3, Clause: []int{1, -1}},
		{Kind: "add", ID: 3, Clause: []int{1, -1}, Hints: []int{9}},
		{Kind: "add", ID: 2, Hints: []int{1, 2}},
		{Kind: "add", ID: 4, Clause: []int{2}, Hints: []int{1, 2}},
		{Kind: "delete", ID: 2, IDs: []int{1}},
		{Kind: "delete", ID: 3, IDs: []int{1, 1}},
		{Kind: "delete", ID: 4, IDs: []int{3}},
		{Kind: "delete", ID: 9},
		{Kind: "delete", ID: 3, IDs: []int{0}},
	}
	for a := 0; a < 4; a++ {
		for b := 0; b < 4; b++ {
			db := [][]int{clauseMask(1, a), clauseMask(1, b)}
			add(differentialCase{Kind: "proof", Variables: 1, Database: db})
			for _, first := range operations {
				add(differentialCase{Kind: "proof", Variables: 1, Database: db, Commands: []commandCase{first}})
				for _, second := range operations {
					add(differentialCase{Kind: "proof", Variables: 1, Database: db, Commands: []commandCase{first, second}})
				}
			}
		}
	}
	add(differentialCase{Kind: "proof", Variables: 1, Database: [][]int{{1}, {-1}}, Commands: []commandCase{
		{Kind: "add", ID: 3, Hints: []int{1, 2}}, {Kind: "delete", ID: 3, IDs: []int{3}},
	}})
	add(differentialCase{Kind: "proof", Variables: 1, Database: [][]int{{1, 1}, {-1, -1}}, Commands: []commandCase{
		{Kind: "add", ID: 3, Clause: []int{1, 1}, Hints: []int{1}}, {Kind: "add", ID: 4, Hints: []int{3, 2}},
	}})
	checkTextCorpus(t, cases)
	accepted := 0
	for _, c := range cases {
		if c.Expected {
			accepted++
		}
	}
	if accepted == 0 || accepted == len(cases) {
		t.Fatal("corpus must cover both outcomes")
	}
	t.Logf("%d cases: %d accepted, %d rejected; all accepted decisions pass exhaustive truth tables", len(cases), accepted, len(cases)-accepted)
	if path := os.Getenv("OAK_LEAN_DIFFERENTIAL_OUT"); path != "" {
		data, err := json.Marshal(cases)
		if err != nil {
			t.Fatal(err)
		}
		if err = os.WriteFile(path, data, 0600); err != nil {
			t.Fatal(err)
		}
	}
}
