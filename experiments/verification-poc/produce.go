// Proof search is untrusted. Only evidence.go and internal/lrat accept claims.
package main

import (
    "fmt"
    "sort"
    "strings"
    "github.com/SCKelemen/oak/experiments/verification-poc/internal/lrat"
)
func absolute(x int)int{if x<0{return -x};return x}
func localLRAT(text string,priority []int)(string,error){
    f,e:=lrat.Parse(text);if e!=nil{return "",e};db:=map[int]lrat.Clause{};for i,c:=range f.Clauses{db[i+1]=c}
    last:=len(db);nodes:=0;var output strings.Builder
    propagate:=func(decisions []int)(bool,[]int,lrat.Clause){
        assigned:=lrat.Clause{};for _,x:=range decisions{assigned[x]=true};hints:=[]int{}
        ids:=[]int{};for id:=range db{ids=append(ids,id)};sort.Ints(ids)
        for {changed:=false
            for _,id:=range ids{clause:=db[id];satisfied:=false;left:=0;unit:=0
                for x:=range clause{if assigned[x]{satisfied=true;break};if !assigned[-x]{left++;unit=x}}
                if satisfied{continue};if left==0{return true,append(hints,id),assigned};if left==1{assigned[unit]=true;hints=append(hints,id);changed=true}
            };if !changed{return false,hints,assigned}
        }
    }
    var search func([]int)error
    search=func(decisions []int)error{
        nodes++;if nodes>4096{return fmt.Errorf("local proof search limit: 4096 nodes")}
        conflict,hints,assigned:=propagate(decisions)
        if !conflict{
            variable:=0;order:=append([]int{},priority...);for v:=1;v<=f.Variables;v++{order=append(order,v)}
            for _,v:=range order{if !assigned[v]&&!assigned[-v]{variable=v;break}}
            if variable==0{return fmt.Errorf("SAT: no refutation")}
            for _,v:=range []int{variable,-variable}{ds:=append(append([]int{},decisions...),v);if e:=search(ds);e!=nil{return e}}
            conflict,hints,_=propagate(decisions);if !conflict{return fmt.Errorf("producer failed to derive parent")}
        }
        last++;clause:=lrat.Clause{};fmt.Fprintf(&output,"%d ",last)
        for _,x:=range decisions{clause[-x]=true;fmt.Fprintf(&output,"%d ",-x)};output.WriteString("0 ");for _,id:=range hints{fmt.Fprintf(&output,"%d ",id)};output.WriteString("0\n");db[last]=clause;return nil
    }
    if e:=search(nil);e!=nil{return "",e};return output.String(),nil
}
func localProof(m *Model)(*Certificate,error){
    states,e:=m.states();if e!=nil{return nil,e};var witness State;for _,s:=range states{if truth(m.Terms["initial"],s,nil){witness=s;break}};if witness==nil{return nil,fmt.Errorf("empty initial set")}
    cert:=&Certificate{Format:evidenceFormat,Digest:m.Digest,Kind:"lrat",Initial:witness,Proofs:map[string]Proof{}}
    for _,role:=range []string{"base","step"}{c,r:=encode(m,role);cnf:=c.dimacs(r);proof,e:=localLRAT(cnf,c.priority());if e!=nil{return nil,e};cert.Proofs[role]=Proof{digest(cnf),proof}}
    return cert,nil
}
func findTrace(m *Model)(*Certificate,error){
    states,e:=m.states();if e!=nil{return nil,e};paths:=[][]State{};seen:=map[string]bool{}
    for _,s:=range states{if truth(m.Terms["initial"],s,nil){paths=append(paths,[]State{s});seen[stateKey(s)]=true}}
    if len(paths)==0{return nil,fmt.Errorf("empty initial set")}
    for head:=0;head<len(paths);head++{path:=paths[head];s:=path[len(path)-1]
        if !truth(m.Terms["invariant"],s,nil){return &Certificate{Format:evidenceFormat,Digest:m.Digest,Kind:"trace",States:path},nil}
        for _,t:=range states{key:=stateKey(t);if !seen[key]&&truth(m.Terms["step"],s,t){seen[key]=true;next:=append(append([]State{},path...),t);paths=append(paths,next)}}
    };return nil,fmt.Errorf("no counterexample in exhaustively explored finite model")
}
