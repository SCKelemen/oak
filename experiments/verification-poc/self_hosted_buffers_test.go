package main

import (
 "encoding/json"
 "fmt"
 "math/rand"
 "os"
 "strconv"
 "strings"
 "testing"
)

type bufferCommand struct { Deletion bool `json:"deletion"`; Clause string `json:"clause"`; Hints string `json:"hints"` }
type bufferCase struct {
 Name string `json:"name"`
 Variables uint32 `json:"variables"`
 Initial []string `json:"initial"`
 Commands []bufferCommand `json:"commands"`
 Accepted bool `json:"accepted"`
 Layout []uint32 `json:"layout"`
}
func bufferSegment(text string, mode int, variables uint32) ([]uint32,bool) {
 out:=[]uint32{};words:=strings.Fields(text)
 for i,w:=range words {
  n,err:=strconv.ParseInt(w,10,64);if err!=nil||n < -2147483647||n>2147483647 {return nil,false}
  if n==0 {return out,i==len(words)-1&&(mode!=2||w=="0")}
  if mode!=0 {if n<0 {return nil,false};out=append(out,uint32(n))} else {
   negative:=n<0;if negative {n=-n};if n>int64(variables) {return nil,false}
   v:=uint32(n-1)*2;if !negative {v++};out=append(out,v)
  }
 }
 return nil,false
}
func bufferReference(c bufferCase) ([]uint32,bool) {
 pool,starts,sizes,refs,commands:=[]uint32{},[]uint32{},[]uint32{},[]uint32{},[]uint32{}
 if c.Variables==0||c.Variables>64||len(c.Initial)>256||len(c.Commands)>256 {return nil,false}
 for _,body:=range c.Initial {items,ok:=bufferSegment(body,0,c.Variables);if !ok||len(pool)+len(items)>4096 {return nil,false};starts=append(starts,uint32(len(pool)));sizes=append(sizes,uint32(len(items)));pool=append(pool,items...)}
 for i,cmd:=range c.Commands {
  start:=uint32(len(pool));count:=uint32(0);addition:=uint32(1);mode:=1
  if cmd.Deletion {addition=0;mode=2} else {items,ok:=bufferSegment(cmd.Clause,0,c.Variables);if !ok||len(pool)+len(items)>4096 {return nil,false};count=uint32(len(items));pool=append(pool,items...)}
  items,ok:=bufferSegment(cmd.Hints,mode,c.Variables);if !ok||len(refs)+len(items)>4096 {return nil,false}
  commands=append(commands,addition,uint32(len(c.Initial)+i+1),start,count,uint32(len(refs)),uint32(len(items)));refs=append(refs,items...)
 }
 flat:=[]uint32{c.Variables,uint32(len(pool)),uint32(len(starts)),uint32(len(refs)),uint32(len(c.Commands))}
 for _,items:=range [][]uint32{pool,starts,sizes,refs,commands} {flat=append(flat,items...)}
 return flat,true
}
func bufferTexts(c bufferCase) (string,string) {
 var cnf,proof strings.Builder;fmt.Fprintf(&cnf,"p cnf %d %d\n",c.Variables,len(c.Initial))
 for _,s:=range c.Initial {cnf.WriteString(s);cnf.WriteByte('\n')}
 for i,cmd:=range c.Commands {fmt.Fprintf(&proof,"%d ",len(c.Initial)+i+1);if cmd.Deletion {proof.WriteString("d ")} else {proof.WriteString(cmd.Clause);proof.WriteByte(' ')};proof.WriteString(cmd.Hints);proof.WriteByte('\n')}
 return cnf.String(),proof.String()
}
func bufferCorpus() []bufferCase {
 out:=[]bufferCase{}
 add:=func(name string,initial []string,commands ...bufferCommand) {if initial==nil {initial=[]string{}};if commands==nil {commands=[]bufferCommand{}};c:=bufferCase{Name:name,Variables:64,Initial:initial,Commands:commands};c.Layout,c.Accepted=bufferReference(c);if c.Layout==nil {c.Layout=[]uint32{}};out=append(out,c)}
 add("empty",nil)
 add("empty-ranges",[]string{"0","-0","+0"},bufferCommand{Clause:"0",Hints:"0"},bufferCommand{Deletion:true,Hints:"0"})
 add("mixed",[]string{"1 -64 0","0","-1 2 -0"},bufferCommand{Clause:"64 -2 +0",Hints:"1 2 2147483647 -0"},bufferCommand{Deletion:true,Hints:"2 2 0"})
 for _,bad:=range []string{"1","1 x 0","65 0","2147483648 0","+ 0","0 1"} {add("literal-"+bad,[]string{bad})}
 for _,bad:=range []string{"-1 0","1","1 x 0","2147483648 0","0 1"} {add("hint-"+bad,[]string{"0"},bufferCommand{Clause:"0",Hints:bad})}
 for _,zero:=range []string{"0","+0","-0","00"} {add("delete-zero-"+zero,[]string{"0"},bufferCommand{Deletion:true,Hints:"1 "+zero})}
 for _,n:=range []int{4095,4096,4097} {
  add(fmt.Sprintf("literal-capacity-%d",n),[]string{strings.Repeat("1 ",n)+"0"})
  add(fmt.Sprintf("hint-capacity-%d",n),[]string{"0"},bufferCommand{Clause:"0",Hints:strings.Repeat("1 ",n)+"0"})
 }
 add("shared-literal-full",[]string{strings.Repeat("1 ",4095)+"0"},bufferCommand{Clause:"-64 0",Hints:"0"},bufferCommand{Clause:"0",Hints:"0"})
 add("shared-literal-overflow",[]string{strings.Repeat("1 ",4095)+"0"},bufferCommand{Clause:"-64 1 0",Hints:"0"})
 add("shared-hints-full",[]string{"0"},bufferCommand{Clause:"0",Hints:strings.Repeat("1 ",4095)+"0"},bufferCommand{Deletion:true,Hints:"2 0"})
 add("shared-hints-overflow",[]string{"0"},bufferCommand{Clause:"0",Hints:strings.Repeat("1 ",4095)+"0"},bufferCommand{Deletion:true,Hints:"2 3 0"})
 for _,n:=range []int{256,257} {initial:=make([]string,n);cmds:=make([]bufferCommand,n);for i:=range initial {initial[i]="0";cmds[i]=bufferCommand{Deletion:true,Hints:"0"}};add(fmt.Sprintf("clause-count-%d",n),initial);add(fmt.Sprintf("command-count-%d",n),nil,cmds...)}
 rng:=rand.New(rand.NewSource(88412))
 body:=func(hints bool) string {var s strings.Builder;for j:=rng.Intn(8);j>0;j-- {n:=1+rng.Intn(64);if !hints&&rng.Intn(2)==0 {n=-n};fmt.Fprintf(&s,"%d\t",n)};s.WriteString("0");return s.String()}
 for i:=0;i<40;i++ {initial:=[]string{};for j:=rng.Intn(5);j>0;j-- {initial=append(initial,body(false))};cmds:=[]bufferCommand{};for j:=rng.Intn(5);j>0;j-- {cmds=append(cmds,bufferCommand{Deletion:rng.Intn(3)==0,Clause:body(false),Hints:body(true)})};add(fmt.Sprintf("random-%d",i),initial,cmds...)}
 return out
}

// Periodic initialization keeps the capacity regressions small in generated Oak.
func emitBufferArray(out *strings.Builder,name,typ string,values []uint32) {
 capacity:=len(values);if capacity==0 {capacity=1};fmt.Fprintf(out,"%s: [%d]%s\n",name,capacity,typ)
 for i:=0;i<len(values); {
  bestPeriod,bestEnd:=1,i+1
  for p:=1;p<=16&&i+p<=len(values);p++ {end:=i+p;for end<len(values)&&values[end]==values[i+(end-i)%p] {end++};end=i+(end-i)/p*p;if end-i>=p*4&&end>bestEnd {bestPeriod,bestEnd=p,end}}
  if bestEnd-i>8 {
   fmt.Fprintf(out,"%s_i_%d: u32 = %d\nwhile %s_i_%d < u32(%d) {\n",name,i,i,name,i,bestEnd)
   for k:=0;k<bestPeriod;k++ {fmt.Fprintf(out,"%s[%s_i_%d + u32(%d)] = %s(%d)\n",name,name,i,k,typ,values[i+k])}
   fmt.Fprintf(out,"%s_i_%d = %s_i_%d + u32(%d)\n}\n",name,i,name,i,bestPeriod);i=bestEnd
  } else {fmt.Fprintf(out,"%s[%d] = %s(%d)\n",name,i,typ,values[i]);i++}
 }
 fmt.Fprintf(out,"%s_view: []%s = %s[0:%d]\n",name,typ,name,len(values))
}
// One decoder observation: the texts fed to the actual Oak decoder and the
// flat layout the oracle expects it to publish, or a decoder rejection.
type layoutObservation struct { CNF,Proof string; Layout []uint32; Accepted bool }

// Instrument only the decoder's entry signature and final handoff, then compare
// every published pool item, range, and command field in compiled Oak.
func observeDecoderLayouts(t *testing.T,prefix string,cases []layoutObservation) {
 t.Helper()
 var source,main strings.Builder
 for _,path:=range []string{"self_hosted_rup.oak","self_hosted_stream.oak"} {data,err:=os.ReadFile(path);if err!=nil {t.Fatal(err)};source.Write(data);source.WriteByte('\n')}
 data,err:=os.ReadFile("self_hosted_text.oak");if err!=nil {t.Fatal(err)};decoder:=string(data)
 replacements:=[][2]string{
  {"rup_text_check: (cnf: []u8, proof: []u8): Bool {","rup_text_check: (cnf: []u8, proof: []u8, expected_layout: []u32): u32 {"},
  {"  accepted: Bool = false\n  valid ? { accepted = rup_stream_check(pool_view, initial_view, sizes_view, refs_view, commands_view, variables) }\n  accepted", "  status: u32 = 0\n  valid ? {\n    status = u32(1)\n    buffer_observe(pool_view, initial_view, sizes_view, refs_view, commands_view, variables, expected_layout) ? { status = u32(2) }\n  }\n  status"},
 }
 for _,r:=range replacements {if strings.Count(decoder,r[0])!=1 {t.Fatal("decoder observation seam changed")};decoder=strings.Replace(decoder,r[0],r[1],1)}
 source.WriteString(decoder);source.WriteString(`
buffer_observe: (pool: []u32, starts: []u32, sizes: []u32, refs: []u32, commands: []RUPCommand, variables: u32, expected: []u32): Bool {
 good: Bool = len(expected) == u32(5) + len(pool) + len(starts) + len(sizes) + len(refs) + len(commands) * u32(6)
 good ? {
  good = expected[0] == variables && expected[1] == len(pool) && expected[2] == len(starts) && expected[3] == len(refs) && expected[4] == len(commands)
  at: u32 = 5
  i: u32 = 0
  while i < len(pool) { good = good && expected[at] == pool[i]; i = i + u32(1); at = at + u32(1) }
  i = u32(0)
  while i < len(starts) { good = good && expected[at] == starts[i]; i = i + u32(1); at = at + u32(1) }
  i = u32(0)
  while i < len(sizes) { good = good && expected[at] == sizes[i]; i = i + u32(1); at = at + u32(1) }
  i = u32(0)
  while i < len(refs) { good = good && expected[at] == refs[i]; i = i + u32(1); at = at + u32(1) }
  i = u32(0)
  while i < len(commands) {
   addition: u32 = 0
   commands[i].addition ? { addition = u32(1) }
   good = good && expected[at] == addition && expected[at + u32(1)] == commands[i].id && expected[at + u32(2)] == commands[i].start && expected[at + u32(3)] == commands[i].count && expected[at + u32(4)] == commands[i].refs_start && expected[at + u32(5)] == commands[i].refs_count
   i = i + u32(1); at = at + u32(6)
  }
 }
 good
}
`)
 main.WriteString("main: (): i32 {\n")
 for i,c:=range cases {
  fmt.Fprintf(&source,"%s_case_%d: (): Bool {\n",prefix,i)
  for _,a:=range []struct{name,text string}{{"cnf",c.CNF},{"proof",c.Proof}} {values:=[]uint32{};for _,b:=range []byte(a.text) {values=append(values,uint32(b))};emitBufferArray(&source,a.name,"u8",values)}
  emitBufferArray(&source,"expected","u32",c.Layout);status:=0;if c.Accepted {status=2}
  fmt.Fprintf(&source,"rup_text_check(cnf_view, proof_view, expected_view) == u32(%d)\n}\n",status);fmt.Fprintf(&main,"assert(%s_case_%d())\n",prefix,i)
 }
 main.WriteString("42\n}\n");source.WriteString(main.String());runOakStream(t,source.String())
}
func TestSelfHostedBufferLayouts(t *testing.T) {
 cases:=bufferCorpus();accepted:=0;observations:=[]layoutObservation{}
 for _,c:=range cases {cnf,proof:=bufferTexts(c);observations=append(observations,layoutObservation{cnf,proof,c.Layout,c.Accepted});if c.Accepted {accepted++}}
 observeDecoderLayouts(t,"buffer",observations)
 if path:=os.Getenv("OAK_BUFFER_CORPUS_OUT");path!="" {data,err:=json.MarshalIndent(cases,"","  ");if err!=nil {t.Fatal(err)};if err:=os.WriteFile(path,append(data,'\n'),0644);err!=nil {t.Fatal(err)}}
 t.Logf("Oak/Go buffer layouts: %d cases (%d decoded, %d rejected)",len(cases),accepted,len(cases)-accepted)
}
