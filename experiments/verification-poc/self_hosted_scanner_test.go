package main

import (
 "encoding/json"
 "fmt"
 "math/rand"
 "os"
 "strings"
 "testing"
)

type scannerToken struct {
 Kind uint32 `json:"kind"`
 Next uint32 `json:"next"`
 Start uint32 `json:"start"`
 Stop uint32 `json:"stop"`
 Magnitude uint32 `json:"magnitude"`
 Sign uint32 `json:"sign"`
}
type scannerCase struct {
 Name string `json:"name"`
 Bytes []uint32 `json:"bytes"`
 Cursor uint32 `json:"cursor"`
 Tokens []scannerToken `json:"tokens"`
}
func scannerSpace(b byte) bool {return b==' '||b=='\t'||b=='\r'||b=='\v'||b=='\f'}
// Mathematical uint64 arithmetic, followed by a bound check. This deliberately
// does not copy Oak's pre-multiplication threshold guard.
func scannerOracle(input []byte, cursor uint32) scannerToken {
 pos:=int(cursor)
 for pos<len(input)&&scannerSpace(input[pos]) {pos++}
 r:=scannerToken{Next:uint32(pos),Start:uint32(pos),Stop:uint32(pos),Sign:1}
 if pos==len(input) {return r}
 if input[pos]=='\n' {r.Kind=1;r.Next++;r.Stop++;return r}
 r.Kind=2
 for pos<len(input)&&input[pos]!='\n'&&!scannerSpace(input[pos]) {pos++}
 r.Next=uint32(pos);r.Stop=uint32(pos)
 word:=input[r.Start:r.Stop]
 if word[0]=='+'||word[0]=='-' {if word[0]=='-' {r.Sign=2};word=word[1:]}
 if len(word)==0 {r.Sign=0;return r}
 for _,b:=range word {
  if b<'0'||b>'9' {r.Sign=0;break}
  next:=uint64(r.Magnitude)*10+uint64(b-'0')
  if next>2147483647 {r.Sign=0;break}
  r.Magnitude=uint32(next)
 }
 return r
}
func TestScannerOracle(t *testing.T) {
 cases:=[]struct{input string;cursor uint32;want scannerToken}{
  {" \t",0,scannerToken{0,2,2,2,0,1}},
  {" \n9",0,scannerToken{1,2,1,2,0,1}},
  {"x -0!9 tail",2,scannerToken{2,6,2,6,0,0}},
  {"2147483648suffix",0,scannerToken{2,16,0,16,214748364,0}},
  {"skip -0",5,scannerToken{2,7,5,7,0,2}},
  {"+ -",0,scannerToken{2,1,0,1,0,0}},
 }
 for _,c:=range cases {if got:=scannerOracle([]byte(c.input),c.cursor);got!=c.want {t.Fatalf("%q @ %d: got %+v want %+v",c.input,c.cursor,got,c.want)}}
}
func scannerCorpus() []scannerCase {
 out:=[]scannerCase{}
 add:=func(input string,cursor uint32,steps int) {
  c:=scannerCase{Name:fmt.Sprintf("scanner-%d",len(out)),Bytes:[]uint32{},Cursor:cursor,Tokens:[]scannerToken{}}
  for _,b:=range []byte(input) {c.Bytes=append(c.Bytes,uint32(b))}
  for i:=0;i<steps;i++ {r:=scannerOracle([]byte(input),cursor);c.Tokens=append(c.Tokens,r);cursor=r.Next}
  out=append(out,c)
 }
 for _,input:=range []string{""," \t\r\v\f","\n\n","  + - -0 +0 00\n","12x999 2147483648suffix -2147483647\n9","c comment\np cnf 2 1\n1 -2 0\n"} {
  for cursor:=0;cursor<=len(input);cursor++ {add(input,uint32(cursor),8)}
 }
 for b:=0;b<256;b++ {add(string([]byte{byte(b)}),0,3);add(" \t12"+string([]byte{byte(b)})+"34\n-0",1,5)}
 for i,c:=range decimalCorpus() {if i%4!=0 {continue};var s strings.Builder;s.WriteString("\t ");for _,b:=range c.Bytes {s.WriteByte(byte(b))};s.WriteString(" tail\n");add(s.String(),0,4)}
 rng:=rand.New(rand.NewSource(20260908));alphabet:=[]byte("0123456789+-xyz \t\n\r\v\f")
 for i:=0;i<300;i++ {input:=make([]byte,rng.Intn(65));for j:=range input {input[j]=alphabet[rng.Intn(len(alphabet))]};add(string(input),uint32(rng.Intn(len(input)+1)),8)}
 add(strings.Repeat(" ",65535)+"0",0,3)
 add(strings.Repeat("0",65536),0,3)
 add(strings.Repeat("9",65536),65535,3)
 return out
}
func TestSelfHostedScanner(t *testing.T) {
 cases:=scannerCorpus();transitions:=0
 var source,main strings.Builder
 for _,path:=range []string{"self_hosted_rup.oak","self_hosted_stream.oak","self_hosted_text.oak"} {data,err:=os.ReadFile(path);if err!=nil {t.Fatal(err)};source.Write(data);source.WriteByte('\n')}
 source.WriteString(`scanner_expect: (bytes: []u8, state: [*]u32, want_kind: u32, want_next: u32, want_start: u32, want_stop: u32, want_magnitude: u32, want_sign: u32): Bool {
 kind: u32 = rup_token(bytes, state)
 kind == want_kind && state[0] == want_next && state[1] == want_start && state[2] == want_stop && state[3] == want_magnitude && state[4] == want_sign
}
`)
 main.WriteString("main: (): i32 {\n")
 for i,c:=range cases {
  fmt.Fprintf(&source,"scanner_case_%d: (): Bool {\n",i)
  capacity:=len(c.Bytes);if capacity==0 {capacity=1}
  fmt.Fprintf(&source,"input: [%d]u8\n",capacity)
  for begin:=0;begin<len(c.Bytes); {
   end:=begin+1;for end<len(c.Bytes)&&c.Bytes[end]==c.Bytes[begin] {end++}
   if end-begin>8 {fmt.Fprintf(&source,"i_%d: u32 = %d\nwhile i_%d < u32(%d) { input[i_%d] = u8(%d); i_%d = i_%d + u32(1) }\n",begin,begin,begin,end,begin,c.Bytes[begin],begin,begin)} else {for j:=begin;j<end;j++ {fmt.Fprintf(&source,"input[%d] = u8(%d)\n",j,c.Bytes[j])}}
   begin=end
  }
  fmt.Fprintf(&source,"bytes: []u8 = input[0:%d]\nstate: [5]u32\nstate[0] = u32(%d)\n",len(c.Bytes),c.Cursor)
  // Poison fields the scanner must overwrite, then preserve state across calls.
  source.WriteString("state[1] = u32(999)\nstate[2] = u32(998)\nstate[3] = u32(997)\nstate[4] = u32(996)\nok: Bool = true\n")
  for _,r:=range c.Tokens {
   transitions++
   fmt.Fprintf(&source,"ok = scanner_expect(bytes, span(&state), u32(%d), u32(%d), u32(%d), u32(%d), u32(%d), u32(%d)) && ok\n",r.Kind,r.Next,r.Start,r.Stop,r.Magnitude,r.Sign)
  }
  source.WriteString("ok\n}\n");fmt.Fprintf(&main,"assert(scanner_case_%d())\n",i)
 }
 main.WriteString("42\n}\n");source.WriteString(main.String());runOakStream(t,source.String())
 if path:=os.Getenv("OAK_SCANNER_CORPUS_OUT");path!="" {data,err:=json.MarshalIndent(cases,"","  ");if err!=nil {t.Fatal(err)};if err:=os.WriteFile(path,append(data,'\n'),0644);err!=nil {t.Fatal(err)}}
 t.Logf("Oak/Go scanner agreement: %d cases, %d transitions",len(cases),transitions)
}
