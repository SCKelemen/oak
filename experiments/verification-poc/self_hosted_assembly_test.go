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

// Command assembly with explicit identifier words. Unlike the buffer corpus,
// addition IDs and deletion stamps are arbitrary spellings taken from the text.
type assemblyCommand struct { ID string `json:"id"`; Deletion bool `json:"deletion"`; Clause string `json:"clause"`; Hints string `json:"hints"` }
type assemblyCase struct {
 Name string `json:"name"`
 Variables uint32 `json:"variables"`
 Initial []string `json:"initial"`
 Commands []assemblyCommand `json:"commands"`
 Accepted bool `json:"accepted"`
 Layout []uint32 `json:"layout"`
}
// The decoder accepts one numeric word with a valid sign that is nonnegative or
// a spelling of zero. Go's parser is the independent oracle for that rule.
func assemblyIdentifier(word string) (uint32,bool) {
 fields:=strings.Fields(word);if len(fields)!=1 {return 0,false}
 n,err:=strconv.ParseInt(fields[0],10,64);if err!=nil||n<0||n>2147483647 {return 0,false}
 return uint32(n),true
}
func assemblyReference(c assemblyCase) ([]uint32,bool) {
 pool,starts,sizes,refs,commands:=[]uint32{},[]uint32{},[]uint32{},[]uint32{},[]uint32{}
 if c.Variables==0||c.Variables>64||len(c.Initial)>256||len(c.Commands)>256 {return nil,false}
 for _,body:=range c.Initial {items,ok:=bufferSegment(body,0,c.Variables);if !ok||len(pool)+len(items)>4096 {return nil,false};starts=append(starts,uint32(len(pool)));sizes=append(sizes,uint32(len(items)));pool=append(pool,items...)}
 for _,cmd:=range c.Commands {
  id,ok:=assemblyIdentifier(cmd.ID);if !ok {return nil,false}
  // Deletions publish no literals but record the current literal offset.
  start:=uint32(len(pool));count:=uint32(0);addition:=uint32(1);mode:=1
  if cmd.Deletion {addition=0;mode=2} else {items,ok:=bufferSegment(cmd.Clause,0,c.Variables);if !ok||len(pool)+len(items)>4096 {return nil,false};count=uint32(len(items));pool=append(pool,items...)}
  items,ok:=bufferSegment(cmd.Hints,mode,c.Variables);if !ok||len(refs)+len(items)>4096 {return nil,false}
  commands=append(commands,addition,id,start,count,uint32(len(refs)),uint32(len(items)));refs=append(refs,items...)
 }
 flat:=[]uint32{c.Variables,uint32(len(pool)),uint32(len(starts)),uint32(len(refs)),uint32(len(c.Commands))}
 for _,items:=range [][]uint32{pool,starts,sizes,refs,commands} {flat=append(flat,items...)}
 return flat,true
}
func assemblyTexts(c assemblyCase) (string,string) {
 var cnf,proof strings.Builder;fmt.Fprintf(&cnf,"p cnf %d %d\n",c.Variables,len(c.Initial))
 for _,s:=range c.Initial {cnf.WriteString(s);cnf.WriteByte('\n')}
 for _,cmd:=range c.Commands {proof.WriteString(cmd.ID);proof.WriteByte(' ');if cmd.Deletion {proof.WriteString("d ")} else {proof.WriteString(cmd.Clause);proof.WriteByte(' ')};proof.WriteString(cmd.Hints);proof.WriteByte('\n')}
 return cnf.String(),proof.String()
}
func assemblyCorpus() []assemblyCase {
 out:=[]assemblyCase{}
 add:=func(name string,initial []string,commands ...assemblyCommand) {if initial==nil {initial=[]string{}};if commands==nil {commands=[]assemblyCommand{}};c:=assemblyCase{Name:name,Variables:64,Initial:initial,Commands:commands};c.Layout,c.Accepted=assemblyReference(c);if c.Layout==nil {c.Layout=[]uint32{}};out=append(out,c)}
 db:=[]string{"1 0","-1 0"}
 addition:=func(id string) assemblyCommand {return assemblyCommand{ID:id,Clause:"0",Hints:"1 2 0"}}
 deletion:=func(id string) assemblyCommand {return assemblyCommand{ID:id,Deletion:true,Hints:"1 0"}}
 add("sequential",db,addition("3"))
 // Identifier spellings: signs, zero, leading zeros, whitespace, and limits.
 for _,id:=range []string{"3","+3","0","-0","+0","-00","007","\t7","7\t","1","9","256","257","2147483647","-1","-3","2147483648","4294967295","4294967296","x","3x","d","+","-","1e3","3.0"} {
  add("addition-id-"+strconv.Quote(id),db,addition(id))
  add("deletion-stamp-"+strconv.Quote(id),db,deletion(id))
 }
 // Non-sequential and repeated identifiers are decoded; validity is checked later.
 add("repeated-ids",db,addition("3"),addition("3"),deletion("3"),addition("1"))
 add("descending-ids",db,addition("9"),addition("8"),deletion("0"))
 // Deletions after additions record the literal offset at that point.
 add("deletion-offset",db,assemblyCommand{ID:"3",Clause:"1 2 0",Hints:"0"},deletion("4"),assemblyCommand{ID:"5",Clause:"-2 0",Hints:"3 0"},deletion("6"))
 add("empty-clauses-and-hints",db,assemblyCommand{ID:"3",Clause:"0",Hints:"0"},assemblyCommand{ID:"4",Deletion:true,Hints:"0"})
 add("mixed-spellings",[]string{"1 -64 0","0"},assemblyCommand{ID:"+3",Clause:"64 -2 +0",Hints:"1 2 2147483647 -0"},assemblyCommand{ID:"-0",Deletion:true,Hints:"2 2 0"},assemblyCommand{ID:"2147483647",Clause:"-1 0",Hints:"0"})
 // Malformed segments after a valid identifier still reject the whole layout.
 add("bad-clause-after-id",db,assemblyCommand{ID:"3",Clause:"65 0",Hints:"0"})
 add("bad-hint-after-id",db,assemblyCommand{ID:"3",Clause:"0",Hints:"-1 0"})
 add("bad-deletion-zero-after-stamp",db,assemblyCommand{ID:"3",Deletion:true,Hints:"1 +0"})
 for _,n:=range []int{256,257} {cmds:=make([]assemblyCommand,n);for i:=range cmds {cmds[i]=deletion(strconv.Itoa(i))};add(fmt.Sprintf("command-count-%d",n),nil,cmds...)}
 rng:=rand.New(rand.NewSource(51907))
 body:=func(hints bool) string {var s strings.Builder;for j:=rng.Intn(6);j>0;j-- {n:=1+rng.Intn(64);if !hints&&rng.Intn(2)==0 {n=-n};fmt.Fprintf(&s,"%d ",n)};s.WriteString("0");return s.String()}
 spellings:=[]string{"%d","+%d","%03d","-0","%d\t","2147483647","-%d","%dq"}
 for i:=0;i<32;i++ {
  initial:=[]string{};for j:=rng.Intn(4);j>0;j-- {initial=append(initial,body(false))}
  cmds:=[]assemblyCommand{};next:=len(initial)
  for j:=rng.Intn(6);j>0;j-- {next++;id:=fmt.Sprintf(spellings[rng.Intn(len(spellings))],next);cmds=append(cmds,assemblyCommand{ID:id,Deletion:rng.Intn(3)==0,Clause:body(false),Hints:body(true)})}
  add(fmt.Sprintf("random-%d",i),initial,cmds...)
 }
 return out
}
func TestSelfHostedCommandAssembly(t *testing.T) {
 cases:=assemblyCorpus();accepted:=0;observations:=[]layoutObservation{}
 for _,c:=range cases {cnf,proof:=assemblyTexts(c);observations=append(observations,layoutObservation{cnf,proof,c.Layout,c.Accepted});if c.Accepted {accepted++}}
 if accepted==0||accepted==len(cases) {t.Fatal("assembly corpus must contain decoded and rejected layouts")}
 observeDecoderLayouts(t,"assembly",observations)
 if path:=os.Getenv("OAK_ASSEMBLY_CORPUS_OUT");path!="" {data,err:=json.MarshalIndent(cases,"","  ");if err!=nil {t.Fatal(err)};if err:=os.WriteFile(path,append(data,'\n'),0644);err!=nil {t.Fatal(err)}}
 t.Logf("Oak/Go command assembly: %d cases (%d decoded, %d rejected)",len(cases),accepted,len(cases)-accepted)
}
