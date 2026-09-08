package main

import (
 "encoding/json"
 "fmt"
 "os"
 "strings"
 "testing"

 "github.com/SCKelemen/oak/experiments/verification-poc/internal/lrat"
)

type propagationCase struct {
 selfHostedRUPCase
 Trace []uint32 `json:"trace"`
}

// Logical assignments use signed variable names and Bool values, independently
// of Oak's three-valued byte representation. Only snapshot serialization encodes.
func propagationReference(c selfHostedRUPCase) []uint32 {
 values:=map[int]bool{};valid:=c.Variables>0&&c.Variables<=64
 reset:=valid;contradictory,conflict:=false,false
 for _,id:=range c.Hints {if id<=0||id>len(c.Clauses) {valid=false}}
 out:=[]uint32{};bit:=func(b bool) uint32 {if b {return 1};return 0}
 snapshot:=func(){out=append(out,bit(valid),bit(contradictory),bit(conflict));for v:=1;v<=64;v++ {n:=uint32(7);if reset&&v<=c.Variables {n=0};if b,ok:=values[v];ok {n=1+bit(b)};out=append(out,n)}}
 abs:=func(n int) int {if n<0 {return -n};return n}
 snapshot()
 for _,lit:=range c.Target {
  if !valid||contradictory {break};v:=abs(lit);valid=v>0&&v<=c.Variables
  if valid {wanted:=lit<0;prior,present:=values[v];contradictory=present&&prior!=wanted;if !present {values[v]=wanted}}
  snapshot()
 }
 for h,id:=range c.Hints {
  if !valid||contradictory||conflict {break}
  seen:=map[int]bool{};unknown:=[]int{};satisfied:=false
  for _,lit:=range c.Clauses[id-1] {
   if !valid||satisfied {break};v:=abs(lit);valid=v>0&&v<=c.Variables
   if valid&&!seen[lit] {b,present:=values[v];satisfied=present&&b==(lit>0);if !present {unknown=append(unknown,lit)}};seen[lit]=true
  }
  if valid&&!satisfied {
   switch len(unknown) {case 0:conflict=h==len(c.Hints)-1;valid=conflict;case 1:lit:=unknown[0];values[abs(lit)]=lit>0;default:valid=false}
  } else {valid=false}
  snapshot()
 }
 return out
}
func propagationCorpus(t *testing.T) []propagationCase {
 t.Helper();base:=selfHostedCases()
 for v:=1;v<=64;v++ {for _,sign:=range []int{-1,1} {lit:=v*sign;base=append(base,selfHostedRUPCase{Variables:v,Target:[]int{lit,lit,-lit},Clauses:[][]int{},Hints:[]int{}})}}
 literals:=[]int{-2,-1,1,2}
 var targets func([]int,int)
 targets=func(xs []int,left int){if len(xs)>0 {base=append(base,selfHostedRUPCase{Variables:2,Target:append([]int{},xs...),Clauses:[][]int{{1,1},{-1,-1}},Hints:[]int{1,2}})};if left>0 {for _,lit:=range literals {targets(append(append([]int{},xs...),lit),left-1)}}}
 targets(nil,3)
 base=append(base,
  selfHostedRUPCase{Variables:0},selfHostedRUPCase{Variables:65},
  selfHostedRUPCase{Variables:1,Target:[]int{2}},
  selfHostedRUPCase{Variables:1,Clauses:[][]int{{2}},Hints:[]int{1}},
  selfHostedRUPCase{Variables:1,Clauses:[][]int{{},{}},Hints:[]int{1,2}})
 out:=[]propagationCase{}
 for i,c:=range base {
  if c.Clauses==nil {c.Clauses=[][]int{}};if c.Target==nil {c.Target=[]int{}};if c.Hints==nil {c.Hints=[]int{}}
  c.Accepted=c.Variables<=64&&lrat.CheckRUPDecoded(c.Variables,c.Clauses,c.Target,c.Hints)==nil
  trace:=propagationReference(c);last:=trace[len(trace)-67:]
  if (last[0]==1&&(last[1]==1||last[2]==1))!=c.Accepted {t.Fatalf("propagation oracle acceptance differs at case %d",i)}
  out=append(out,propagationCase{c,trace})
 }
 return out
}
func propagationInstrument(t *testing.T,source string) string {
 t.Helper();replace:=func(old,next string){if strings.Count(source,old)!=1 {t.Fatalf("propagation observation seam changed: %q",old)};source=strings.Replace(source,old,next,1)}
 replace("  variables: u32\n): Bool {","  variables: u32,\n  expected: []u32,\n  expected_accepted: Bool\n): Bool {")
 observe:=func(conflict string) string {return "  trace_ok = propagation_observe(assignments, valid, contradictory, "+conflict+", expected, trace_cursor) && trace_ok\n  trace_cursor = trace_cursor + u32(67)\n"}
 replace("  contradictory: Bool = false\n","  contradictory: Bool = false\n  trace_ok: Bool = true\n  trace_cursor: u32 = 0\n"+observe("false"))
 replace("    i = i + u32(1)\n  }\n\n  conflict: Bool = false", "    i = i + u32(1)\n"+observe("false")+"  }\n\n  conflict: Bool = false")
 replace("    h = h + u32(1)\n","    h = h + u32(1)\n"+observe("conflict"))
 replace("  valid && (contradictory || conflict)\n}","  trace_ok && trace_cursor == len(expected) && (valid && (contradictory || conflict)) == expected_accepted\n}")
 return source+`
propagation_observe: (cells: [*]u8, valid: Bool, contradictory: Bool, conflict: Bool,
  expected: []u32, offset: u32): Bool {
  ok: Bool = offset <= len(expected) && u32(67) <= len(expected) - offset
  ok ? {
    ok = (expected[offset] == u32(1)) == valid && (expected[offset + u32(1)] == u32(1)) == contradictory && (expected[offset + u32(2)] == u32(1)) == conflict
    slot: u32 = 0
    while slot < u32(64) && ok {
      ok = u32(cells[slot]) == expected[offset + u32(3) + slot]
      slot = slot + u32(1)
    }
  }
  ok
}
`
}
func TestSelfHostedPropagationState(t *testing.T) {
 cases:=propagationCorpus(t);snapshots:=0;accepted:=0
 kernel,err:=os.ReadFile("self_hosted_rup.oak");if err!=nil {t.Fatal(err)}
 var source,main strings.Builder;source.WriteString(propagationInstrument(t,string(kernel)));main.WriteString("main: (): i32 {\n")
 emit:=func(i int,c propagationCase,want bool){
  fmt.Fprintf(&source,"propagation_case_%d: (): Bool {\n",i)
  pool,starts,sizes,target,hints:=[]uint32{},[]uint32{},[]uint32{},[]uint32{},[]uint32{}
  for _,clause:=range c.Clauses {starts=append(starts,uint32(len(pool)));sizes=append(sizes,uint32(len(clause)));for _,lit:=range clause {pool=append(pool,oakLiteral(lit))}}
  for _,lit:=range c.Target {target=append(target,oakLiteral(lit))};for _,id:=range c.Hints {n:=uint32(4294967295);if id>0 {n=uint32(id-1)};hints=append(hints,n)}
  for _,a:=range []struct{name string;items []uint32}{{"pool",pool},{"starts",starts},{"sizes",sizes},{"target",target},{"hints",hints},{"expected",c.Trace}} {emitBufferArray(&source,a.name,"u32",a.items)}
  source.WriteString("assignments: [64]u8\nslot: u32 = 0\nwhile slot < u32(64) { assignments[slot] = u8(7); slot = slot + u32(1) }\n")
  fmt.Fprintf(&source,"rup_check(pool_view, starts_view, sizes_view, u32(%d), target_view, u32(%d), hints_view, u32(%d), span(&assignments), u32(%d), expected_view, %t) == %t\n}\n",len(starts),len(target),len(hints),c.Variables,c.Accepted,want)
  fmt.Fprintf(&main,"assert(propagation_case_%d())\n",i)
 }
 for i,c:=range cases {emit(i,c,true);snapshots+=len(c.Trace)/67;if c.Accepted {accepted++}}
 for i,field:=range []int{0,1,2,3,66,-1} {c:=cases[0];c.Trace=append([]uint32{},c.Trace...);if field<0 {c.Trace=c.Trace[:len(c.Trace)-67]} else {c.Trace[field]^=1};emit(len(cases)+i,c,false)}
 main.WriteString("42\n}\n");source.WriteString(main.String());runOakStream(t,source.String())
 if path:=os.Getenv("OAK_PROPAGATION_CORPUS_OUT");path!="" {data,err:=json.MarshalIndent(cases,"","  ");if err!=nil {t.Fatal(err)};if err:=os.WriteFile(path,append(data,'\n'),0644);err!=nil {t.Fatal(err)}}
 t.Logf("Oak/Go propagation state: %d cases, %d complete 64-cell snapshots, %d accepted, 6 observer corruptions rejected",len(cases),snapshots,accepted)
}
