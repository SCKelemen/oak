package main

import (
	"encoding/json"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/experiments/verification-poc/internal/lrat"
)

type selfHostedRUPCase struct {
	Variables int `json:"variables"`
	Clauses [][]int `json:"clauses"`
	Target []int `json:"target"`
	Hints []int `json:"hints"`
	Accepted bool `json:"accepted"`
}

func selfHostedCases() []selfHostedRUPCase {
	cases := []selfHostedRUPCase{
		{2,[][]int{{1},{-1}},nil,[]int{1,2},false},
		{2,[][]int{{1}},[]int{1,-1},[]int{1},false},
		{2,[][]int{{}},nil,[]int{1},false},
		{2,[][]int{{1}},[]int{-1},[]int{1},false},
		{2,[][]int{{1}},nil,nil,false},
		{2,[][]int{{1}},[]int{1,-1},nil,false},
	}
	rng := rand.New(rand.NewSource(741921))
	literals := []int{-3,-2,-1,1,2,3}
	for len(cases) < 400 {
		variables := 3
		clauses := make([][]int, rng.Intn(3)+1)
		for i := range clauses {
			clauses[i] = make([]int, rng.Intn(5))
			for j := range clauses[i] { clauses[i][j] = literals[rng.Intn(len(literals))] }
		}
		target := make([]int, rng.Intn(5))
		for i := range target { target[i] = literals[rng.Intn(len(literals))] }
		hints := make([]int, rng.Intn(4))
		for i := range hints { hints[i] = rng.Intn(len(clauses)+2) }
		cases = append(cases, selfHostedRUPCase{Variables:variables,Clauses:clauses,Target:target,Hints:hints})
	}
	for i := range cases { cases[i].Accepted = lrat.CheckRUPDecoded(cases[i].Variables,cases[i].Clauses,cases[i].Target,cases[i].Hints) == nil }
	return cases
}

func oakLiteral(x int) uint32 {
	v:=x;if v<0 {v=-v}
	code:=uint32(2*(v-1));if x>0 {code++};return code
}

func emitOakRUPCase(out *strings.Builder, c selfHostedRUPCase) {
	fmt.Fprintln(out,"true ? {")
	fmt.Fprintln(out,"clause_literals: [12]u32")
	fmt.Fprintln(out,"clause_starts: [3]u32")
	fmt.Fprintln(out,"clause_lengths: [3]u32")
	fmt.Fprintln(out,"target: [4]u32")
	fmt.Fprintln(out,"hints: [3]u32")
	fmt.Fprintln(out,"assignments: [4]u8")
	at:=0
	for i,clause:=range c.Clauses {
		fmt.Fprintf(out,"clause_starts[%d] = u32(%d)\nclause_lengths[%d] = u32(%d)\n",i,at,i,len(clause))
		for _,lit:=range clause {fmt.Fprintf(out,"clause_literals[%d] = u32(%d)\n",at,oakLiteral(lit));at++}
	}
	for i,lit:=range c.Target {fmt.Fprintf(out,"target[%d] = u32(%d)\n",i,oakLiteral(lit))}
	for i,h:=range c.Hints {encoded:=uint32(4294967295);if h>0 {encoded=uint32(h-1)};fmt.Fprintf(out,"hints[%d] = u32(%d)\n",i,encoded)}
	fmt.Fprintf(out,"accepted: Bool = rup_check(view(&clause_literals), view(&clause_starts), view(&clause_lengths), u32(%d), view(&target), u32(%d), view(&hints), u32(%d), span(&assignments), u32(%d))\n",len(c.Clauses),len(c.Target),len(c.Hints),c.Variables)
	fmt.Fprintf(out,"assert(accepted == %t)\n",c.Accepted)
	fmt.Fprintln(out,"}")
}

func TestSelfHostedRUPKernel(t *testing.T) {
	cc,err:=exec.LookPath("cc");if err!=nil {t.Skip("no C compiler")}
	core,err:=os.ReadFile("self_hosted_rup.oak");if err!=nil {t.Fatal(err)}
	cases:=selfHostedCases()
	var source strings.Builder
	source.Write(core)
	source.WriteString("\nmain: (): i32 {\n")
	for _,c:=range cases {emitOakRUPCase(&source,c)}
	source.WriteString("42\n}\n")
	generated,err:=compiler.New().WithSource("self_hosted_rup_test.oak",source.String()).EmitC().Get();if err!=nil {t.Fatalf("Oak compile: %v",err)}
	for _,bad:=range []string{"malloc(","calloc(","realloc(","OAK_UNSUPPORTED"} {if strings.Contains(generated,bad){t.Fatalf("generated C contains %s",bad)}}
	dir:=t.TempDir();cpath:=filepath.Join(dir,"checker.c");bin:=filepath.Join(dir,"checker")
	if err:=os.WriteFile(cpath,[]byte(generated),0644);err!=nil {t.Fatal(err)}
	if output,err:=exec.Command(cc,"-std=c99","-O1","-o",bin,cpath).CombinedOutput();err!=nil {t.Fatalf("cc: %v\n%s",err,output)}
	run:=exec.Command(bin)
	output,err:=run.CombinedOutput()
	exitCode:=0
	if err!=nil {if e,ok:=err.(*exec.ExitError);ok {exitCode=e.ExitCode()} else {t.Fatalf("Oak checker: %v\n%s",err,output)}}
	if exitCode!=42 {t.Fatalf("Oak checker exit=%d, want 42\n%s",exitCode,output)}
	if path:=os.Getenv("OAK_SELF_HOSTED_RUP_CORPUS_OUT");path!="" {data,_:=json.MarshalIndent(cases,"","  ");if err:=os.WriteFile(path,append(data,'\n'),0644);err!=nil {t.Fatal(err)}}
	t.Logf("Oak RUP kernel agreed with Go on %d cases",len(cases))
}
