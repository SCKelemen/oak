package main

import (
 "encoding/json"
 "fmt"
 "os"
 "strings"
 "testing"
)

func certifiedStreamCorpus(t *testing.T) []rangeCase {
 t.Helper();cases:=rangeCorpus(t)
 add:=func(name string,s streamCase,want bool){c:=rangeFromStream(s);c.Name=name;decoded,meaning,ok:=rangeDecode(c);if !ok {t.Fatal("constructed stream did not decode",name)};c.Decoded=true;c.Meaning=meaning;c.Accepted=streamReference(decoded);if c.Accepted!=want {t.Fatal("constructed stream reference differs",name)};cases=append(cases,c)}
 for n:=1;n<=64;n++ {
  db:=[][]int{{1}};for v:=1;v<n;v++ {db=append(db,[]int{-v,v+1})};db=append(db,[]int{-n})
  commands:=[]streamCommand{};previous:=uint32(1);id:=uint32(n+2)
  for v:=2;v<=n;v++ {commands=append(commands,streamAdd(id,[]int{v},int(previous),v),streamDelete(id,previous));previous=id;id++}
  emptyID:=id;commands=append(commands,streamAdd(id,nil,int(previous),n+1),streamDelete(id,id));id++
  commands=append(commands,streamAdd(id,[]int{1,-1}))
  s:=streamCase{Variables:n,Database:db,Commands:commands}
  add(fmt.Sprintf("certified-live-chain-%d",n),s,true)
  s.Commands=append(append([]streamCommand{},commands...),streamAdd(id,[]int{1,-1}));add(fmt.Sprintf("reused-id-after-refutation-%d",n),s,false)
  s.Commands=append(append([]streamCommand{},commands...),streamAdd(id+1,[]int{1,-1},int(emptyID)));add(fmt.Sprintf("deleted-empty-hint-%d",n),s,false)
  s.Commands=append(append([]streamCommand{},commands...),streamDelete(id,uint32(n+1),uint32(n+1)));add(fmt.Sprintf("duplicate-delete-after-refutation-%d",n),s,false)
 }
 return cases
}
func TestSelfHostedCertifiedStream(t *testing.T) {
 cases:=certifiedStreamCorpus(t);accepted:=0
 var source,main strings.Builder
 for _,path:=range []string{"self_hosted_rup.oak","self_hosted_stream.oak"} {data,err:=os.ReadFile(path);if err!=nil {t.Fatal(err)};source.Write(data);source.WriteByte('\n')}
 main.WriteString("main: (): i32 {\n")
 for i,c:=range cases {
  fmt.Fprintf(&source,"certified_stream_case_%d: (): Bool {\n",i)
  for _,a:=range []struct{name string;items []uint32}{{"pool",c.Pool},{"starts",c.Starts},{"sizes",c.Sizes},{"refs",c.Refs}} {emitBufferArray(&source,a.name,"u32",a.items)}
  capacity:=len(c.Commands);if capacity==0 {capacity=1};fmt.Fprintf(&source,"commands: [%d]RUPCommand\n",capacity)
  for j,r:=range c.Commands {fmt.Fprintf(&source,"commands[%d] = RUPCommand { addition: %t, id: u32(%d), start: u32(%d), count: u32(%d), refs_start: u32(%d), refs_count: u32(%d) }\n",j,r.Addition,r.ID,r.Start,r.Count,r.RefsStart,r.RefsCount)}
  fmt.Fprintf(&source,"command_view: []RUPCommand = commands[0:%d]\nrup_stream_check(pool_view, starts_view, sizes_view, refs_view, command_view, u32(%d)) == %t\n}\n",len(c.Commands),c.Variables,c.Accepted)
  fmt.Fprintf(&main,"assert(certified_stream_case_%d())\n",i);if c.Accepted {accepted++}
 }
 main.WriteString("42\n}\n");source.WriteString(main.String());runOakStream(t,source.String())
 if path:=os.Getenv("OAK_CERTIFIED_STREAM_CORPUS_OUT");path!="" {data,err:=json.MarshalIndent(cases,"","  ");if err!=nil {t.Fatal(err)};if err:=os.WriteFile(path,append(data,'\n'),0644);err!=nil {t.Fatal(err)}}
 t.Logf("Oak/Go certified stream: %d layouts (%d accepted, %d rejected), 256 constructed live-chain/suffix cases",len(cases),accepted,len(cases)-accepted)
}
