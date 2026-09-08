package main

import (
 "context"
 "encoding/json"
 "fmt"
 "math/rand"
 "os"
 "os/exec"
 "path/filepath"
 "strings"
 "testing"
 "time"

 "github.com/SCKelemen/oak/compiler"
 "github.com/SCKelemen/oak/experiments/verification-poc/internal/lrat"
)

type streamCommand struct {
 Kind string `json:"kind"`
 ID uint32 `json:"id"`
 Clause []int `json:"clause"`
 Hints []int `json:"hints"`
 IDs []uint32 `json:"ids"`
}
type streamCase struct {
 Name string `json:"name"`
 Kind string `json:"kind"`
 Variables int `json:"variables"`
 Database [][]int `json:"database"`
 Clause []int `json:"clause"`
 Hints []int `json:"hints"`
 Commands []streamCommand `json:"commands"`
 Expected bool `json:"expected"`
}
func streamAdd(id uint32, clause []int, hints ...int) streamCommand {return streamCommand{Kind:"add",ID:id,Clause:clause,Hints:hints}}
func streamDelete(stamp uint32, ids ...uint32) streamCommand {return streamCommand{Kind:"delete",ID:stamp,IDs:ids}}
func streamReference(c streamCase) bool {
 var cnf,proof strings.Builder
 fmt.Fprintf(&cnf,"p cnf %d %d\n",c.Variables,len(c.Database))
 for _,clause:=range c.Database {for _,lit:=range clause {fmt.Fprintf(&cnf,"%d ",lit)};cnf.WriteString("0\n")}
 for _,cmd:=range c.Commands {
  fmt.Fprintf(&proof,"%d ",cmd.ID)
  if cmd.Kind=="delete" {proof.WriteString("d ");for _,id:=range cmd.IDs {fmt.Fprintf(&proof,"%d ",id)}} else {
   for _,lit:=range cmd.Clause {fmt.Fprintf(&proof,"%d ",lit)};proof.WriteString("0 ")
   for _,id:=range cmd.Hints {fmt.Fprintf(&proof,"%d ",id)}
  };proof.WriteString("0\n")
 }
 _,err:=lrat.Check(cnf.String(),proof.String());return err==nil
}
func streamCorpus(t *testing.T) []streamCase {
 t.Helper()
 out:=[]streamCase{}
 add:=func(name string, db [][]int, expected bool, commands ...streamCommand) {
  c:=streamCase{Name:name,Variables:3,Database:db,Commands:commands}
  got:=streamReference(c);if got!=expected {t.Fatalf("reference disagrees with labelled %s: %v",name,got)}
  out=append(out,c)
 }
 db:=[][]int{{1},{-1}}
 add("derive-empty",db,true,streamAdd(3,nil,1,2))
 add("empty-initial",[][]int{{}},true)
 add("no-refutation",db,false)
 add("delete-derived-empty",db,true,streamAdd(3,nil,1,2),streamDelete(3,3))
 add("delete-initial-empty",[][]int{{}},true,streamDelete(1,1))
 add("invalid-suffix",db,false,streamAdd(3,nil,1,2),streamAdd(4,nil))
 add("valid-suffix",db,true,streamAdd(3,nil,1,2),streamAdd(4,[]int{1,-1}))
 add("reuse-deleted-id",db,false,streamAdd(3,[]int{1},1),streamDelete(3,3),streamAdd(3,nil,1,2))
 add("deleted-hint",db,false,streamDelete(2,1),streamAdd(3,nil,1,2))
 add("deleted-hint-tautology",db,false,streamDelete(2,1),streamAdd(3,[]int{1,-1},1))
 add("duplicate-deletion",db,false,streamAdd(3,nil,1,2),streamDelete(3,1,1))
 add("missing-deletion",db,false,streamAdd(3,nil,1,2),streamDelete(3,4))
 add("zero-deletion",db,false,streamAdd(3,nil,1,2),streamDelete(3,0))
 add("low-stamp",db,false,streamAdd(3,nil,1,2),streamDelete(2,1))
 add("stamp-does-not-advance",db,true,streamDelete(100),streamAdd(3,nil,1,2))
 add("sparse-addition",db,true,streamAdd(100,[]int{1},1),streamAdd(256,nil,100,2))
 add("zero-addition",db,false,streamAdd(0,nil,1,2))
 add("initial-id-reuse",db,false,streamAdd(2,nil,1,2))
 add("future-hint",db,false,streamAdd(3,nil,3))
 add("zero-hint",db,false,streamAdd(3,nil,0))
 add("RAT-hint",db,false,streamAdd(3,nil,-1))
 add("conflict-suffix",db,false,streamAdd(3,nil,1,2,1))
 add("satisfied-hint",db,false,streamAdd(3,nil,1,1,2))
 add("duplicates",[][]int{{1,1},{-1,-1}},true,streamAdd(3,nil,1,2))
 add("derived-chain",[][]int{{1},{-1,2},{-2,3},{-3}},true,streamAdd(5,[]int{2},1,2),streamAdd(6,[]int{3},5,3),streamDelete(6,1,2,3,5),streamAdd(7,nil,6,4),streamDelete(7,7,6,4))
 // Seeded mutation of previously valid streams exercises later instructions.
 rng:=rand.New(rand.NewSource(81043))
 for i:=0;i<200;i++ {
  id:=uint32(3+rng.Intn(100))
  commands:=[]streamCommand{streamAdd(id,[]int{1},1),streamAdd(id+1,nil,int(id),2),streamDelete(id+1,id+1)}
  switch i%8 {
  case 0: commands=append(commands,streamAdd(id+2,[]int{1,-1}))
  case 1: commands=append(commands,streamAdd(id+2,nil))
  case 2: commands[1].Hints=[]int{int(id+1)}
  case 3: commands[2]=streamDelete(id+1,id+1,id+1)
  case 4: commands[1].ID=id
  case 5: commands=append([]streamCommand{streamDelete(200)},commands...)
  case 6: commands[2]=streamDelete(id,1)
  }
  out=append(out,streamCase{Name:fmt.Sprintf("mutation-%d",i),Variables:3,Database:db,Commands:commands})
 }
 for i:=0;i<200;i++ {
  database:=make([][]int,1+rng.Intn(4))
  for j:=range database {database[j]=[]int{};for k:=rng.Intn(4);k>0;k-- {lit:=1+rng.Intn(3);if rng.Intn(2)==0 {lit=-lit};database[j]=append(database[j],lit)}}
  commands:=[]streamCommand{}
  for j:=0;j<rng.Intn(6);j++ {
   id:=uint32(rng.Intn(9))
   if rng.Intn(3)==0 {ids:=[]uint32{};for k:=rng.Intn(4);k>0;k-- {ids=append(ids,uint32(rng.Intn(9)))};commands=append(commands,streamDelete(id,ids...))} else {
    clause:=[]int{};for k:=rng.Intn(4);k>0;k-- {lit:=1+rng.Intn(3);if rng.Intn(2)==0 {lit=-lit};clause=append(clause,lit)}
    hints:=[]int{};for k:=rng.Intn(5);k>0;k-- {hints=append(hints,rng.Intn(10)-1)};commands=append(commands,streamAdd(id,clause,hints...))
   }
  }
  out=append(out,streamCase{Name:fmt.Sprintf("random-%d",i),Variables:3,Database:database,Commands:commands})
 }
 for i:=range out {
  c:=&out[i];c.Kind="proof";c.Clause=[]int{};c.Hints=[]int{};if c.Commands==nil {c.Commands=[]streamCommand{}}
  for j:=range c.Database {if c.Database[j]==nil {c.Database[j]=[]int{}}}
  for j:=range c.Commands {cmd:=&c.Commands[j];if cmd.Clause==nil {cmd.Clause=[]int{}};if cmd.Hints==nil {cmd.Hints=[]int{}};if cmd.IDs==nil {cmd.IDs=[]uint32{}}}
  c.Expected=streamReference(*c)
  // An independent truth table guards the reference's accepted decisions.
  if c.Expected {
   for mask:=0;mask<1<<c.Variables;mask++ {
    sat:=true;for _,clause:=range c.Database {holds:=false;for _,lit:=range clause {n:=lit;if n<0 {n=-n};value:=mask&(1<<(n-1))!=0;holds=holds || value==(lit>0)};sat=sat&&holds}
    if sat {t.Fatalf("reference accepted satisfiable %s",c.Name)}
   }
  }
 }
 return out
}

type streamLayout struct {lits,starts,lengths,refs []uint32; commands []string}
func layoutStream(c streamCase) streamLayout {
 r:=streamLayout{}
 for _,clause:=range c.Database {r.starts=append(r.starts,uint32(len(r.lits)));r.lengths=append(r.lengths,uint32(len(clause)));for _,lit:=range clause {r.lits=append(r.lits,oakLiteral(lit))}}
 for _,cmd:=range c.Commands {
  start,refstart:=len(r.lits),len(r.refs);count:=0;action:="true"
  if cmd.Kind=="delete" {action="false";r.refs=append(r.refs,cmd.IDs...)} else {
   count=len(cmd.Clause);for _,lit:=range cmd.Clause {r.lits=append(r.lits,oakLiteral(lit))}
   for _,hint:=range cmd.Hints {encoded:=uint32(0);if hint>0 {encoded=uint32(hint)};r.refs=append(r.refs,encoded)}
  }
  r.commands=append(r.commands,fmt.Sprintf("RUPCommand { addition: %s, id: u32(%d), start: u32(%d), count: u32(%d), refs_start: u32(%d), refs_count: u32(%d) }",action,cmd.ID,start,count,refstart,len(r.refs)-refstart))
 }
 return r
}
func emitStreamCase(b *strings.Builder,c streamCase,mutation string,expected bool) {
 r:=layoutStream(c)
 
 for _,a:=range []struct{name string; values []uint32}{{"pool",r.lits},{"initial",r.starts},{"sizes",r.lengths},{"refs",r.refs}} {
  capacity:=len(a.values);if capacity==0 {capacity=1}
  fmt.Fprintf(b,"%s: [%d]u32\n",a.name,capacity)
  for i,v:=range a.values {fmt.Fprintf(b,"%s[%d] = u32(%d)\n",a.name,i,v)}
 }
 capacity:=len(r.commands);if capacity==0 {capacity=1}
 fmt.Fprintf(b,"commands: [%d]RUPCommand\n",capacity)
 for i,cmd:=range r.commands {fmt.Fprintf(b,"commands[%d] = %s\n",i,cmd)}
 fmt.Fprintf(b,"nvars: u32 = %d\n",c.Variables)
 b.WriteString(mutation)
 fmt.Fprintf(b,"pool_view: []u32 = pool[0:%d]\ninitial_view: []u32 = initial[0:%d]\nsizes_view: []u32 = sizes[0:%d]\nrefs_view: []u32 = refs[0:%d]\ncommands_view: []RUPCommand = commands[0:%d]\n",len(r.lits),len(r.starts),len(r.lengths),len(r.refs),len(r.commands))
 fmt.Fprintln(b,"result: Bool = rup_stream_check(pool_view, initial_view, sizes_view, refs_view, commands_view, nvars)")
 fmt.Fprintf(b,"assert(result == %t)\n",expected)
}
func runOakStream(t *testing.T,source string) {
 t.Helper();cc,err:=exec.LookPath("cc");if err!=nil {t.Fatal("C compiler required for Oak stream checks")}
 generated,err:=compiler.New().WithSource("self_hosted_stream_test.oak",source).EmitC().Get();if err!=nil {t.Fatalf("Oak stream compile: %v",err)}
 for _,bad:=range []string{"malloc(","calloc(","realloc(","OAK_UNSUPPORTED"} {if at:=strings.Index(generated,bad);at>=0 {start:=at-180;if start<0 {start=0};end:=at+400;if end>len(generated) {end=len(generated)};t.Fatalf("unexpected %s in generated checker: %s",bad,generated[start:end])}}
 // Trace text-case entry in the native harness so traps identify their input.
 // This instrumentation is outside the Oak checker and does not alter decisions.
 if strings.Contains(source,"text_case_") {
  var traced strings.Builder;traced.WriteString("#include <stdio.h>\nstatic int oak_text_trace_left = 80;\n")
  for _,line:=range strings.Split(generated,"\n") {
   if strings.Contains(line,"return") && strings.Contains(line,"kind") {traced.WriteString("if (oak_text_trace_left-- > 0) fprintf(stderr, \"token kind=%u begin=%u end=%u magnitude=%u sign=%u\\n\", kind, begin, pos, magnitude, sign);\n")}
   if strings.Contains(line,"return") && strings.Contains(line,"accepted") {traced.WriteString("if (oak_text_trace_left-- > 0) fprintf(stderr, \"decoded valid=%d accepted=%d stage=%u vars=%u clauses=%u expected=%u literals=%u commands=%u refs=%u\\n\", valid, accepted, stage, variables, clauses, expected, literals, count, references);\n")}
   traced.WriteString(line);traced.WriteByte('\n')
   if at:=strings.Index(line,"text_case_");at>=0 && strings.HasSuffix(strings.TrimSpace(line),"{") {
    end:=at;for end<len(line)&&line[end]!='(' {end++}
    fmt.Fprintf(&traced,"fprintf(stderr, \"enter %s\\n\");\n",strings.TrimSpace(line[at:end]))
   }
  };generated=traced.String()
  start:=strings.Index(generated,"rup_space( u8 b ) {");end:=strings.LastIndex(generated,"text_case_0( void ) {");if start>=0&&end>start {t.Logf("decoder C:\n%s",generated[start:end])}
 }
 dir:=t.TempDir();cpath:=filepath.Join(dir,"stream.c");bin:=filepath.Join(dir,"stream")
 if err:=os.WriteFile(cpath,[]byte(generated),0644);err!=nil {t.Fatal(err)}
 ctx,cancel:=context.WithTimeout(context.Background(),90*time.Second);defer cancel()
 if output,err:=exec.CommandContext(ctx,cc,"-std=c99","-O1",cpath,"-o",bin).CombinedOutput();err!=nil {t.Fatalf("C compile: %v\n%s",err,output)}
 runctx,stop:=context.WithTimeout(context.Background(),15*time.Second);defer stop()
 output,err:=exec.CommandContext(runctx,bin).CombinedOutput()
 code:=0;if err!=nil {if e,ok:=err.(*exec.ExitError);ok {code=e.ExitCode()} else {t.Fatal(err)}}
 if runctx.Err()!=nil || code!=42 {t.Fatalf("Oak stream exit %d, want 42: %v\n%s",code,runctx.Err(),output)}
}
func TestSelfHostedProofStreams(t *testing.T) {
 rup,err:=os.ReadFile("self_hosted_rup.oak");if err!=nil {t.Fatal(err)}
 stream,err:=os.ReadFile("self_hosted_stream.oak");if err!=nil {t.Fatal(err)}
 corpus:=streamCorpus(t);accepted:=0
 var source, main strings.Builder;source.Write(rup);source.Write(stream);main.WriteString("\nmain: (): i32 {\n")
 caseIndex:=0
 emit:=func(c streamCase,mutation string,expected bool) {fmt.Fprintf(&source,"\nstream_case_%d: (): Bool {\n",caseIndex);emitStreamCase(&source,c,mutation,expected);source.WriteString("true\n}\n");fmt.Fprintf(&main,"assert(stream_case_%d())\n",caseIndex);caseIndex++}
 for _,c:=range corpus {emit(c,"",c.Expected);if c.Expected {accepted++}}
 // Raw representation and resource failures are separate from semantic parity.
 base:=corpus[0]
 mutations:=[]string{"nvars = u32(0)\n","nvars = u32(65)\n","initial[0] = u32(4294967295)\n","sizes[0] = u32(4294967295)\n","commands[0].start = u32(4294967295)\n","commands[0].count = u32(4294967295)\n","commands[0].refs_start = u32(4294967295)\n","commands[0].refs_count = u32(4294967295)\n","commands[0].id = u32(257)\n","pool[0] = u32(4294967295)\n","refs[0] = u32(257)\n"}
 for _,mutation:=range mutations {emit(base,mutation,false)}
 main.WriteString("42\n}\n");source.WriteString(main.String());runOakStream(t,source.String())
 if path:=os.Getenv("OAK_SELF_HOSTED_STREAM_CORPUS_OUT");path!="" {data,err:=json.MarshalIndent(corpus,"","  ");if err!=nil {t.Fatal(err)};if err:=os.WriteFile(path,append(data,'\n'),0644);err!=nil {t.Fatal(err)}}
 t.Logf("Oak/Go proof-stream agreement: %d cases (%d accepted, %d rejected); %d malformed/resource cases rejected",len(corpus),accepted,len(corpus)-accepted,len(mutations))
}
