package main

import (
 "encoding/json"
 "fmt"
 "os"
 "strings"
 "testing"

 "github.com/SCKelemen/oak/experiments/verification-poc/internal/lrat"
)

type oakTextCase struct {
 Name string `json:"name"`
 CNF string `json:"cnf"`
 Proof string `json:"proof"`
 Expected bool `json:"expected"`
}
func streamText(c streamCase) (string,string) {
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
 return cnf.String(),proof.String()
}
func oakTextCorpus(t *testing.T) []oakTextCase {
 t.Helper();out:=[]oakTextCase{}
 add:=func(name,cnf,proof string) {_,err:=lrat.Check(cnf,proof);out=append(out,oakTextCase{name,cnf,proof,err==nil})}
 for _,c:=range streamCorpus(t) {cnf,proof:=streamText(c);add("stream-"+c.Name,cnf,proof)}
 cnf,proof:="p cnf 1 2\n1 0\n-1 0\n","3 0 1 2 0\n"
 for i,input:=range []string{
  "", "1 0\n", "p cnf 1 2", "p cnf 1 1\n1 0 -1 0", "p cnf 1 2\n1 0 -1", "p cnf 1 2\n1 0 -2 0",
  "p cnf 1 2 extra\n1 0 -1 0", "p cnf\n1 2\n1 0 -1 0", cnf+"p cnf 1 2\n", cnf+"garbage",
  "p cnf -1 2\n1 0 -1 0", "p cnf 2147483648 2\n1 0 -1 0", "p cnf 1 -2\n1 0 -1 0",
  "p cnf +1 +2\n+1 -0\n-1 +0", " c comment\r\np\tcnf\v1\f2\r\n1\n c between clause tokens\n0 -1 0",
  "p cnf 1 2\n1 c inline\n0 -1 0", "p cnf 1 2\n1 0 -1 0\x00", "p cnf 1 2\n1 0 -1 0\ncomment",
  "p cnf 1 2\n1 0 -1 0\nc final", "p cnf 1 2\n0001 00 -01 000", "p cnf 1 2\n+ 0 -1 0",
 } {add(fmt.Sprintf("cnf-%d",i),input,proof)}
 for i,input:=range []string{
  "", "3", "3 0", "3 0 1 2", "3 0 1 2 0 extra", "3 0 1 2 0 0", "3 0 1\n2 0", "3 0 1 2 0\n4 0 0",
  "3 0 -1 2 0", "3 0 2147483648 2 0", "2147483648 0 1 2 0", "-3 0 1 2 0", "3 0 1 2 0\x00",
  "+3 -0 +1 02 +0", "\tc ignored\r\n3\t0\v1\f2\t0\r\nc final", "3 0 1 2 0\n3 d 3 0",
  "3 0 1 2 0\n3 d 3 +0", "3 0 1 2 0\n3 d 3 -0", "3 0 1 2 0\n3 d 3 00", "3 0 1 2 0\n3 d 3 0 0",
  "3 0 1 2 0\n3 d 0", "3 0 1 2 0\n3 d 3 3 0", "3 0 1 2 0\n3 d -1 0", "3 0 1 2 0\n3 d",
  "3 0 1 2 0\n3 d 0 1 0", "3 0 1 2 0\n2147483647 d 0", "3 0 1 2 0\n4 1 -1 2147483648 0 0",
 } {add(fmt.Sprintf("proof-%d",i),cnf,input)}
 // Every byte class appears in a numeric token and as a token separator.
 for b:=0;b<128;b++ {
  add(fmt.Sprintf("byte-token-%d",b),cnf,"3 0 1 "+string(byte(b))+" 0")
  add(fmt.Sprintf("byte-space-%d",b),cnf,"3"+string(byte(b))+"0 1 2 0")
 }
 return out
}
func runOakTextCases(t *testing.T,cases []oakTextCase) {
 t.Helper()
 var source,main strings.Builder
 for _,path:=range []string{"self_hosted_rup.oak","self_hosted_stream.oak","self_hosted_text.oak"} {data,err:=os.ReadFile(path);if err!=nil {t.Fatal(err)};source.Write(data);source.WriteByte('\n')}
 main.WriteString("main: (): i32 {\n")
 for i,c:=range cases {
  fmt.Fprintf(&source,"text_case_%d: (): Bool {\n",i)
  for _,a:=range []struct{name,text string}{{"cnf",c.CNF},{"proof",c.Proof}} {
   capacity:=len(a.text);if capacity==0 {capacity=1}
   fmt.Fprintf(&source,"%s: [%d]u8\n",a.name,capacity)
   // Compress repeated bytes (including resource-limit inputs) into loops.
   for begin:=0;begin<len(a.text); {
    end:=begin+1;for end<len(a.text)&&a.text[end]==a.text[begin] {end++}
    if end-begin>8 {fmt.Fprintf(&source,"%s_i_%d: u32 = %d\nwhile %s_i_%d < u32(%d) { %s[%s_i_%d] = u8(%d); %s_i_%d = %s_i_%d + u32(1) }\n",a.name,begin,begin,a.name,begin,end,a.name,a.name,begin,a.text[begin],a.name,begin,a.name,begin)} else {for j:=begin;j<end;j++ {fmt.Fprintf(&source,"%s[%d] = u8(%d)\n",a.name,j,a.text[j])}}
    begin=end
   }
   fmt.Fprintf(&source,"%s_view: []u8 = %s[0:%d]\n",a.name,a.name,len(a.text))
  }
  fmt.Fprintf(&source,"rup_text_check(cnf_view, proof_view) == %t\n}\n",c.Expected)
  // C assertion diagnostics retain the generated case function number.
  fmt.Fprintf(&main,"assert(text_case_%d())\n",i)
 }
 main.WriteString("42\n}\n");source.WriteString(main.String());runOakStream(t,source.String())
}
func TestSelfHostedText(t *testing.T) {
 cases:=oakTextCorpus(t);accepted:=0
 for _,c:=range cases {if c.Expected {accepted++}}
 runOakTextCases(t,cases)
 if path:=os.Getenv("OAK_SELF_HOSTED_TEXT_CORPUS_OUT");path!="" {data,err:=json.MarshalIndent(cases,"","  ");if err!=nil {t.Fatal(err)};if err:=os.WriteFile(path,append(data,'\n'),0644);err!=nil {t.Fatal(err)}}
 t.Logf("Oak/Go ASCII agreement: %d cases (%d accepted, %d rejected)",len(cases),accepted,len(cases)-accepted)
}
func TestSelfHostedTextProfile(t *testing.T) {
 cnf,proof:="p cnf 1 2\n1 0 -1 0\n","3 0 1 2 0\n"
 cases:=[]oakTextCase{
  {"zero-variables","p cnf 0 1\n0","",false},
  {"too-many-variables","p cnf 65 1\n0","",false},
  {"too-many-clauses","p cnf 1 257\n"+strings.Repeat("0 ",257),"",false},
  {"large-addition-id",cnf,"257 0 1 2 0",false},
  {"cnf-byte-limit",cnf+"c"+strings.Repeat(" ",65536),proof,false},
  {"proof-byte-limit",cnf,proof+"c"+strings.Repeat(" ",65536),false},
  {"non-ascii-comment",cnf+"c café",proof,false},
  {"literal-pool-limit","p cnf 1 2\n"+strings.Repeat("1 ",4096)+"0 -1 0",proof,false},
  {"command-limit",cnf,proof+strings.Repeat("3 d 0\n",256),false},
  {"reference-pool-limit",cnf,proof+"3 d "+strings.Repeat("1 ",4097)+"0",false},
  {"max-variable","p cnf 64 2\n64 0 -64 0",proof,true},
  {"max-initial-clauses","p cnf 1 256\n"+strings.Repeat("0 ",256),"",true},
  {"max-commands",cnf,proof+strings.Repeat("3 d 0\n",255),true},
  {"max-literal-pool","p cnf 1 2\n"+strings.Repeat("1 ",4095)+"0 -1 0",proof,true},
 }
 runOakTextCases(t,cases);t.Logf("Oak ASCII profile: %d boundary cases passed",len(cases))
}
func TestSelfHostedTextCertificate(t *testing.T) {
 cnfPath,proofPath:=os.Getenv("OAK_SELF_HOSTED_TEXT_CNF"),os.Getenv("OAK_SELF_HOSTED_TEXT_PROOF")
 if cnfPath==""&&proofPath=="" {t.Skip("actual certificate replay runs in the opt-in solver gate")}
 cnf,err:=os.ReadFile(cnfPath);if err!=nil {t.Fatal(err)}
 proof,err:=os.ReadFile(proofPath);if err!=nil {t.Fatal(err)}
 if _,err:=lrat.Check(string(cnf),string(proof));err!=nil {t.Fatal(err)}
 cases:=[]oakTextCase{{"actual-certificate",string(cnf),string(proof),true},{"invalid-suffix",string(cnf),string(proof)+"\n2147483647 0 0\n",false},{"wrong-formula","p cnf 1 1\n1 0\n",string(proof),false}}
 runOakTextCases(t,cases)
 if path:=os.Getenv("OAK_SELF_HOSTED_TEXT_CORPUS_OUT");path!="" {data,err:=json.MarshalIndent(cases,"","  ");if err!=nil {t.Fatal(err)};if err:=os.WriteFile(path,append(data,'\n'),0644);err!=nil {t.Fatal(err)}}
 t.Log("Oak ASCII certificate replay: 1 accepted certificate, 2 rejected corruptions")
}
