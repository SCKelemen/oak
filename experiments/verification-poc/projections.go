package main

import (
    "fmt"
    "os"
    "path/filepath"
    "strconv"
    "strings"
)
func term(m *Model,n *Node,backend string)string{
    switch n.Op{
    case "bool":s:=strconv.FormatBool(n.B);if backend=="tla"{s=strings.ToUpper(s)};return s
    case "byte":if backend=="tla"{return strconv.Itoa(n.N)};if backend=="lean"{return fmt.Sprintf("(BitVec.ofNat 8 %d)",n.N)};return fmt.Sprintf("(_ bv%d 8)",n.N)
    case "enum":if backend=="tla"{return strconv.Quote(n.Type+"."+n.Data)};if backend=="lean"{return "E_"+n.Type+".c_"+n.Data};index:=0;for i,s:=range m.Enums[n.Type]{if s==n.Data{index=i;break}};return fmt.Sprintf("(_ bv%d %d)",index,m.width(n.Type))
    case "var":if backend=="smt"{return n.State+"_f_"+n.Field};return n.State+".f_"+n.Field
    }
    args:=[]string{};for _,a:=range n.Args{args=append(args,term(m,a,backend))};op:=n.Op
    if backend=="smt"{symbol:=map[string]string{"ite":"ite","!":"not","&&":"and","||":"or","==":"=","!=":"distinct","+":"bvadd","-":"bvsub","<":"bvult",">":"bvugt","<=":"bvule",">=":"bvuge"}[op];return "("+symbol+" "+strings.Join(args," ")+")"}
    if op=="ite"{if backend=="tla"{return "(IF "+args[0]+" THEN "+args[1]+" ELSE "+args[2]+")"};return "(bif "+args[0]+" then "+args[1]+" else "+args[2]+")"}
    if op=="!"{prefix:="!";if backend=="tla"{prefix="~"};return "("+prefix+args[0]+")"}
    if backend=="tla"{symbol:=map[string]string{"&&":"/\\","||":"\\/","==":"=","!=":"#","+":"+","-":"-","<":"<",">":">","<=":"<=",">=":">="}[op];result:="("+args[0]+" "+symbol+" "+args[1]+")";if op=="-"{result="("+args[0]+" + 256 - "+args[1]+")"};if op=="+"||op=="-"{result="("+result+" % 256)"};return result}
    if contains([]string{"==","!=","<",">","<=",">="},op){symbol:=op;if op=="=="{symbol="="};if op=="!="{symbol="≠"};return "(decide ("+args[0]+" "+symbol+" "+args[1]+"))"}
    return "("+args[0]+" "+op+" "+args[1]+")"
}
func smtDomain(m *Model,p string)string{guards:=[]string{};for _,f:=range m.Fields{if cases:=m.Enums[f.Type];cases!=nil&&len(cases)<1<<m.width(f.Type){guards=append(guards,fmt.Sprintf("(bvult %s_f_%s (_ bv%d %d))",p,f.Name,len(cases),m.width(f.Type)))}};return "(and true "+strings.Join(guards," ")+")"}
func declarations(m *Model,names []string)string{lines:=[]string{};for _,p:=range names{for _,f:=range m.Fields{t:="Bool";if f.Type!="Bool"{t=fmt.Sprintf("(_ BitVec %d)",m.width(f.Type))};lines=append(lines,"(declare-const "+p+"_f_"+f.Name+" "+t+")")}};return strings.Join(lines,"\n")}
func bmc(m *Model,bound int,values bool)(string,error){
    if bound<0||bound>64{return "",fmt.Errorf("BMC bound must be 0..64")};ps:=[]string{};for i:=0;i<=bound;i++{ps=append(ps,fmt.Sprintf("s%d",i))}
    lines:=[]string{"(set-logic QF_BV)",declarations(m,ps)};for _,p:=range ps{lines=append(lines,"(assert "+smtDomain(m,p)+")")};lines=append(lines,"(assert "+term(m,rename(m.Terms["initial"],"s0"),"smt")+")")
    for i:=0;i<bound;i++{
        var rewrite func(*Node)*Node;rewrite=func(n *Node)*Node{r:=*n;r.Args=nil;if n.Op=="var"{r.State=ps[i];if n.State=="t"{r.State=ps[i+1]}};for _,a:=range n.Args{r.Args=append(r.Args,rewrite(a))};return &r}
        same:=[]string{};for _,f:=range m.Fields{same=append(same,fmt.Sprintf("(= %s_f_%s %s_f_%s)",ps[i],f.Name,ps[i+1],f.Name))};lines=append(lines,"(assert (or (and "+strings.Join(same," ")+") "+term(m,rewrite(m.Terms["step"]),"smt")+"))")
    }
    bad:=[]string{};names:=[]string{};for _,p:=range ps{bad=append(bad,"(not "+term(m,rename(m.Terms["invariant"],p),"smt")+")");for _,f:=range m.Fields{names=append(names,p+"_f_"+f.Name)}}
    lines=append(lines,"(assert (or "+strings.Join(bad," ")+"))","(check-sat)");if values{lines=append(lines,"(get-value ("+strings.Join(names," ")+"))")};return strings.Join(lines,"\n")+"\n",nil
}
func project(m *Model)map[string]string{
    files:=map[string]string{};obligations:=map[string]any{}
    for _,role:=range []string{"initial","base","step"}{c,r:=encode(m,role);text:=c.dimacs(r);files[role+".cnf"]=text;obligations[role]=map[string]any{"sha256":digest(text),"variables":c.Count,"inputs":c.Inputs}}
    ini,inv,nxt,invt:=term(m,m.Terms["initial"],"smt"),term(m,m.Terms["invariant"],"smt"),term(m,m.Terms["step"],"smt"),term(m,rename(m.Terms["invariant"],"t"),"smt")
    assertions:=map[string]string{"initial":"(and "+smtDomain(m,"s")+" "+ini+")","base":"(and "+smtDomain(m,"s")+" "+ini+" (not "+inv+"))","step":"(and "+smtDomain(m,"s")+" "+smtDomain(m,"t")+" "+inv+" "+nxt+" (not "+invt+"))"}
    for role,a:=range assertions{files[role+".smt2"]="(set-logic QF_BV)\n"+declarations(m,[]string{"s","t"})+"\n(assert "+a+")\n(check-sat)\n"}
    lines:=[]string{"import Std.Tactic.BVDecide","namespace OakFinite"}
    for _,name:=range sortedKeys(m.Enums){lines=append(lines,"inductive E_"+name+" where");for _,v:=range m.Enums[name]{lines=append(lines,"  | c_"+v)};lines=append(lines,"  deriving DecidableEq")}
    lines=append(lines,"structure State where");for _,f:=range m.Fields{t:=f.Type;if t=="u8"{t="BitVec 8"}else if t!="Bool"{t="E_"+t};lines=append(lines,"  f_"+f.Name+" : "+t)};lines=append(lines,"  deriving DecidableEq")
    for _,r:=range []struct{role,name string}{{"initial","oakInitial"},{"invariant","oakInvariant"},{"step","oakStep"}}{params:="s";if r.role=="step"{params="s t"};lines=append(lines,"def "+r.name+" ("+params+" : State) : Bool := "+term(m,m.Terms[r.role],"lean"))}
    for _,r:=range []struct{name,claim string;params []string}{{"base","oakInitial s = true → oakInvariant s = true",[]string{"s"}},{"step","oakInvariant s = true → oakStep s t = true → oakInvariant t = true",[]string{"s","t"}}}{
        lines=append(lines,"theorem "+r.name+" ("+strings.Join(r.params," ")+" : State) : "+r.claim+" := by")
        split:=[]string{};for _,p:=range r.params{vars:=[]string{};for i,f:=range m.Fields{v:=fmt.Sprintf("%s%d",p,i);vars=append(vars,v);if m.Enums[f.Type]!=nil{split=append(split,"cases "+v)}};lines=append(lines,"  rcases "+p+" with ⟨"+strings.Join(vars,", ")+"⟩")}
        split=append(split,"simp_all only [oakInitial, oakInvariant, oakStep]","bv_decide");lines=append(lines,"  "+strings.Join(split," <;> "))
    };lines=append(lines,"end OakFinite","");files["Model.lean"]=strings.Join(lines,"\n")
    fields:=[]string{};for _,f:=range m.Fields{domain:="BOOLEAN";if f.Type=="u8"{domain="0..255"}else if m.Enums[f.Type]!=nil{vs:=[]string{};for _,v:=range m.Enums[f.Type]{vs=append(vs,strconv.Quote(f.Type+"."+v))};domain="{"+strings.Join(vs,", ")+"}"};fields=append(fields,"f_"+f.Name+" : "+domain)}
    lines=[]string{"---- MODULE Model ----","EXTENDS Integers, TLC","VARIABLE state","StateSpace == ["+strings.Join(fields,", ")+"]"}
    for _,r:=range []struct{role,name string}{{"initial","OakInitial"},{"invariant","OakInvariant"},{"step","OakStep"}}{params:="s";if r.role=="step"{params="s, t"};lines=append(lines,r.name+"("+params+") == "+term(m,m.Terms[r.role],"tla"))}
    lines=append(lines,"Init == state \\in StateSpace /\\ OakInitial(state)","Next == \\E target \\in StateSpace : state' = target /\\ OakStep(state, target)","Spec == Init /\\ [][Next]_state","TypeOK == state \\in StateSpace","Safe == OakInvariant(state)","====","")
    files["Model.tla"]=strings.Join(lines,"\n");files["Model.cfg"]="SPECIFICATION Spec\nINVARIANT TypeOK\nINVARIANT Safe\nCHECK_DEADLOCK FALSE\n"
    files["manifest.json"]=jsonText(map[string]any{"format":"oak-go-projection-1","semantic_digest":m.Digest,"frontend":"oak","translation_trusted":true,"obligations":obligations});return files
}
func emit(m *Model,out string)error{
    if e:=os.MkdirAll(out,0755);e!=nil{return e}
    if e:=os.Remove(filepath.Join(out,"report.json"));e!=nil&&!os.IsNotExist(e){return e}
    for name,text:=range project(m){if e:=os.WriteFile(filepath.Join(out,name),[]byte(text),0644);e!=nil{return e}};return nil
}
