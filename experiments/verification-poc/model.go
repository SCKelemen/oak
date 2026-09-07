package main

import (
    "encoding/json"
    "fmt"
    "os"
    "path/filepath"
    "sort"
    "strings"

    "github.com/SCKelemen/oak/experiments/verification-poc/frontend"
)

type Config struct {
    Source string `json:"source"`
    Initial string `json:"initial"`
    Step string `json:"step"`
    Invariant string `json:"invariant"`
    Arithmetic string `json:"arithmetic,omitempty"`
}
type Field struct { Name,Type string }
type Node struct { Op,Type,State,Field,Data string; B bool; N int; Args []*Node }
type State map[string]any
type Model struct {
    Document *frontend.Document
    Config Config
    Fields []Field
    Enums map[string][]string
    Terms map[string]*Node
    Digest string
}
func demand(ok bool,why string){if !ok{panic(fmt.Errorf("%s",why))}}
func array(v any) []any {a,ok:=v.([]any);demand(ok,"expected expression array");return a}
func str(v any) string {s,ok:=v.(string);demand(ok,"expected name");return s}
func contains(xs []string,s string)bool{for _,x:=range xs{if x==s{return true}};return false}
func sortedKeys[V any](m map[string]V) []string {keys:=[]string{};for k:=range m{keys=append(keys,k)};sort.Strings(keys);return keys}
func (m *Model) width(t string) int {if t=="Bool"{return 1};if t=="u8"{return 8};w:=1;for 1<<w<len(m.Enums[t]){w++};return w}
func (m *Model) domain(t string) []any {
    if t=="Bool"{return []any{false,true}}
    out:=[]any{};if t=="u8"{for i:=0;i<256;i++{out=append(out,i)}}else{for _,v:=range m.Enums[t]{out=append(out,v)}};return out
}
func (m *Model) valid(s State) error {
    if len(s)!=len(m.Fields){return fmt.Errorf("state fields mismatch")}
    for _,f:=range m.Fields{
        v,ok:=s[f.Name];if !ok{return fmt.Errorf("missing field %s",f.Name)}
        if f.Type=="Bool"{if _,ok:=v.(bool);!ok{return fmt.Errorf("expected Boolean %s",f.Name)}} else if f.Type=="u8"{
            n,e:=number(v);if e!=nil||n<0||n>255{return fmt.Errorf("invalid u8 %s",f.Name)}
        }else{v,ok:=v.(string);if !ok||!contains(m.Enums[f.Type],v){return fmt.Errorf("invalid nominal enum %s",f.Name)}}
    };return nil
}
func (m *Model) states() ([]State,error) {
    count:=1;for _,f:=range m.Fields{count*=len(m.domain(f.Type))};if count>1024{return nil,fmt.Errorf("local enumeration limit: 1024 states")}
    result:=[]State{{}}
    for _,f:=range m.Fields{next:=[]State{};for _,s:=range result{for _,v:=range m.domain(f.Type){t:=State{};for k,x:=range s{t[k]=x};t[f.Name]=v;next=append(next,t)}};result=next};return result,nil
}
func stateKey(s State) string{b,e:=json.Marshal(s);if e!=nil{panic(e)};return string(b)}
func constantBool(b bool)*Node{return &Node{Op:"bool",Type:"Bool",B:b}}
func expression(op,t string,args ...*Node)*Node{return &Node{Op:op,Type:t,Args:args}}
func rename(n *Node,p string)*Node{
    r:=*n;r.Args=nil;if n.Op=="var"{r.State=p};for _,a:=range n.Args{r.Args=append(r.Args,rename(a,p))};return &r
}
func newModel(doc *frontend.Document,cfg Config)(m *Model,err error){
    defer func(){if e:=recover();e!=nil{m=nil;err=fmt.Errorf("invalid finite model: %v",e)}}()
    demand(doc.Format=="oak-finite-1","unsupported frontend format")
    demand(cfg.Source!=""&&cfg.Initial!=""&&cfg.Step!=""&&cfg.Invariant!="","missing project role")
    demand(cfg.Arithmetic==""||cfg.Arithmetic=="u8-wrap","unsupported arithmetic profile")
    // Normalize interface-valued AST arrays and integer representation.
    data,e:=json.Marshal(doc);demand(e==nil,"invalid frontend document");var normalized frontend.Document
    demand(decode(data,&normalized)==nil,"invalid frontend document");doc=&normalized
    m=&Model{Document:doc,Config:cfg,Enums:doc.Enums,Terms:map[string]*Node{}}
    demand(doc.State!=""&&doc.Enums[doc.State]==nil,"invalid state record")
    fields:=map[string]string{};total:=0
    for _,name:=range sortedKeys(doc.Enums){cases:=doc.Enums[name];seen:=map[string]bool{};demand(name!="Bool"&&name!="u8"&&len(cases)>0&&len(cases)<=16,"invalid enum");for _,c:=range cases{demand(!seen[c],"duplicate enum case");seen[c]=true}}
    for _,f:=range doc.Fields{demand(fields[f[0]]=="","duplicate field");t:=f[1];demand(t=="Bool"||t=="u8"||doc.Enums[t]!=nil,"unsupported field type");fields[f[0]]=t;m.Fields=append(m.Fields,Field{f[0],t});total+=m.width(t)}
    demand(len(fields)>0&&len(fields)<=6&&total<=16,"finite record limit: 1..6 fields and 16 state bits")
    var expand func(string,[]string,map[string]bool)*Node
    expand=func(name string,args []string,active map[string]bool)*Node{
        fn,ok:=doc.Functions[name];demand(ok&&!active[name],"unknown or recursive function");demand(len(fn.Params)==len(args),"argument count mismatch")
        nested:=map[string]bool{};for k,v:=range active{nested[k]=v};nested[name]=true
        env:=map[string]string{}
        for i,p:=range fn.Params{_,shadow:=doc.Functions[p];demand(env[p]==""&&!shadow&&doc.Enums[p]==nil,"duplicate/shadowed parameter");env[p]=args[i]}
        var walk func(any)*Node
        walk=func(raw any)*Node{
            a:=array(raw);demand(len(a)>0,"empty expression");op:=str(a[0])
            switch op {
            case "bool": demand(len(a)==2,"invalid Boolean");v,ok:=a[1].(bool);demand(ok,"invalid Boolean");return constantBool(v)
            case "member":
                demand(len(a)==3,"invalid member");name,field:=str(a[1]),str(a[2])
                if p:=env[name];p!=""{t:=fields[field];demand(t!="","unknown state field");return &Node{Op:"var",Type:t,State:p,Field:field}}
                demand(contains(doc.Enums[name],field),"unknown enum constructor");return &Node{Op:"enum",Type:name,Data:field}
            case "call":
                demand(len(a)==3,"invalid call");name:=str(a[1]);actual:=array(a[2])
                if name=="u8"{demand(len(actual)==1,"u8 needs one literal");lit:=array(actual[0]);demand(len(lit)==2&&str(lit[0])=="integer","u8 requires literal");n,e:=number(lit[1]);demand(e==nil&&n>=0&&n<256,"u8 literal outside 0..255");return &Node{Op:"byte",Type:"u8",N:n}}
                ps:=[]string{};for _,arg:=range actual{v:=array(arg);demand(len(v)==2&&str(v[0])=="ref","state argument required");p:=env[str(v[1])];demand(p!="","unknown state parameter");ps=append(ps,p)};return expand(name,ps,nested)
            case "match":
                demand(len(a)==3,"invalid match");scrutinee:=walk(a[1]);arms:=array(a[2]);demand(len(arms)>0,"empty match")
                seen:=map[string]bool{};var conditions,bodies []*Node;var fallback *Node;resultType:=""
                for i,rawArm:=range arms{
                    arm:=array(rawArm);demand(len(arm)==2,"invalid match arm");pattern:=array(arm[0]);demand(len(pattern)>0,"empty pattern");body:=walk(arm[1]);demand(resultType==""||resultType==body.Type,"match result type mismatch");resultType=body.Type
                    if str(pattern[0])=="wildcard"{demand(len(pattern)==1&&i==len(arms)-1,"wildcard must be last");fallback=body;continue}
                    var pat *Node;key:=""
                    if str(pattern[0])=="integer"{demand(len(pattern)==2&&scrutinee.Type=="u8","integer pattern type mismatch");n,e:=number(pattern[1]);demand(e==nil&&n>=0&&n<256,"invalid integer pattern");pat=&Node{Op:"byte",Type:"u8",N:n};key=fmt.Sprint(n)}else{
                        pat=walk(pattern);demand(pat.Op=="bool"||pat.Op=="enum","nonconstant pattern");key=pat.Data;if pat.Op=="bool"{key=fmt.Sprint(pat.B)}
                    }
                    demand(pat.Type==scrutinee.Type&&!seen[key],"mismatched or duplicate pattern");seen[key]=true
                    conditions=append(conditions,expression("==","Bool",scrutinee,pat));bodies=append(bodies,body)
                }
                if fallback==nil{for _,v:=range m.domain(scrutinee.Type){demand(seen[fmt.Sprint(v)],"nonexhaustive match")};fallback=bodies[len(bodies)-1];bodies=bodies[:len(bodies)-1];conditions=conditions[:len(conditions)-1]}
                for i:=len(bodies)-1;i>=0;i--{fallback=expression("ite",resultType,conditions[i],bodies[i],fallback)};return fallback
            }
            arity:=map[string]int{"!":1,"&&":2,"||":2,"==":2,"!=":2,"+":2,"-":2,"<":2,">":2,"<=":2,">=":2,"ite":3}[op]
            demand(arity>0&&len(a)==arity+1,"unsupported expression");children:=[]*Node{};for _,v:=range a[1:]{children=append(children,walk(v))};t:="Bool"
            if op=="!"||op=="&&"||op=="||"{for _,n:=range children{demand(n.Type=="Bool","Boolean type mismatch")}}else if op=="ite"{demand(children[0].Type=="Bool"&&children[1].Type==children[2].Type,"match type mismatch");t=children[1].Type}else if op=="=="||op=="!="{demand(children[0].Type==children[1].Type,"nominal equality mismatch")}else{
                demand(children[0].Type=="u8"&&children[1].Type=="u8","explicit u8 operands required")
                if op=="+"||op=="-"{demand(cfg.Arithmetic=="u8-wrap","arithmetic requires explicit experimental u8-wrap profile");t="u8"}
            };return expression(op,t,children...)
        }
        n:=walk(fn.Body);demand(n.Type=="Bool","predicate must return Bool");return n
    }
    for _,name:=range sortedKeys(doc.Functions){args:=[]string{};for i:=range doc.Functions[name].Params{args=append(args,fmt.Sprintf("p%d",i))};expand(name,args,map[string]bool{})}
    for _,role:=range []struct{role,name string;arity int}{{"initial",cfg.Initial,1},{"invariant",cfg.Invariant,1},{"step",cfg.Step,2}}{
        fn,ok:=doc.Functions[role.name];demand(ok&&len(fn.Params)==role.arity,"invalid role signature");args:=[]string{"s","t"};m.Terms[role.role]=expand(role.name,args[:role.arity],map[string]bool{})
    }
    identity:=struct{Format string;Config Config;Document *frontend.Document}{"oak-go-finite-1",cfg,doc}
    b,e:=json.Marshal(identity);demand(e==nil,"invalid identity");m.Digest=digest(string(b));return m,nil
}
func loadModel(path string)(*Model,error){
    path,e:=filepath.Abs(path);if e!=nil{return nil,e};path,e=filepath.EvalSymlinks(path);if e!=nil{return nil,e}
    var cfg Config;if e:=readJSON(path,&cfg);e!=nil{return nil,e}
    sourcePath,e:=filepath.EvalSymlinks(filepath.Join(filepath.Dir(path),cfg.Source));if e!=nil{return nil,e}
    rel,e:=filepath.Rel(filepath.Dir(path),sourcePath);if e!=nil||rel==".."||strings.HasPrefix(rel,".."+string(filepath.Separator)){return nil,fmt.Errorf("source must remain inside project directory")}
    source,e:=os.ReadFile(sourcePath);if e!=nil{return nil,e};if len(source)>2_000_000{return nil,fmt.Errorf("source limit")}
    doc,e:=frontend.Export(sourcePath,source);if e!=nil{return nil,e};if doc.SourceHash!=digest(string(source)){return nil,fmt.Errorf("frontend source mismatch")};return newModel(doc,cfg)
}
func value(n *Node,env map[string]State)any{
    switch n.Op{
    case "bool":return n.B
    case "byte":return n.N
    case "enum":return n.Type+"."+n.Data
    case "var":v:=env[n.State][n.Field];if n.Type=="u8"{x,e:=number(v);if e!=nil{panic(e)};return x};if n.Type!="Bool"{return n.Type+"."+v.(string)};return v
    case "!":return !value(n.Args[0],env).(bool)
    case "ite":if value(n.Args[0],env).(bool){return value(n.Args[1],env)};return value(n.Args[2],env)
    }
    a,b:=value(n.Args[0],env),value(n.Args[1],env)
    switch n.Op{case "&&":return a.(bool)&&b.(bool);case "||":return a.(bool)||b.(bool);case "==":return a==b;case "!=":return a!=b;case "+":return (a.(int)+b.(int))&255;case "-":return (a.(int)-b.(int))&255;case "<":return a.(int)<b.(int);case ">":return a.(int)>b.(int);case "<=":return a.(int)<=b.(int);case ">=":return a.(int)>=b.(int)};panic("unknown checked operator")
}
func truth(n *Node,s State,t State)bool{return value(n,map[string]State{"s":s,"t":t}).(bool)}
