package main

import (
    "fmt"
    "github.com/SCKelemen/oak/experiments/verification-poc/internal/lrat"
)
const evidenceFormat="oak-evidence-3"
type Proof struct{ SHA string `json:"cnf_sha256"`; LRAT string `json:"lrat"` }
type Certificate struct{
    Format string `json:"format"`
    Digest string `json:"semantic_digest"`
    Kind string `json:"kind"`
    Initial State `json:"initial_witness,omitempty"`
    Proofs map[string]Proof `json:"proofs,omitempty"`
    States []State `json:"states,omitempty"`
}
func verify(m *Model,c *Certificate)(map[string]any,error){
    if c.Format!=evidenceFormat||c.Digest!=m.Digest{return nil,fmt.Errorf("wrong evidence format or source/model identity")}
    if c.Kind=="closed-set" {
        if c.Initial!=nil||c.Proofs!=nil||len(c.States)==0||len(c.States)>1024{return nil,fmt.Errorf("invalid closed-set evidence")}
        members:=map[string]bool{}
        for _,s:=range c.States{if e:=m.valid(s);e!=nil{return nil,e};key:=stateKey(s);if members[key]{return nil,fmt.Errorf("duplicate closed-set state")};members[key]=true;if !truth(m.Terms["invariant"],s,nil){return nil,fmt.Errorf("unsafe closed-set member")}}
        all,e:=m.states();if e!=nil{return nil,e};initials:=0
        for _,s:=range all{if truth(m.Terms["initial"],s,nil){initials++;if !members[stateKey(s)]{return nil,fmt.Errorf("closed set omits an initial state")}}}
        if initials==0{return nil,fmt.Errorf("empty initial set")}
        for _,s:=range c.States{for _,target:=range all{if truth(m.Terms["step"],s,target)&&!members[stateKey(target)]{return nil,fmt.Errorf("closed set omits a successor")}}}
        return map[string]any{"accepted":true,"claim":"nonvacuous reachable safety","evidence":"checked finite closed set","states":len(c.States),"translation_trusted":true},nil
    }
    if c.Kind=="trace"{
        if c.Initial!=nil||c.Proofs!=nil{return nil,fmt.Errorf("unexpected trace fields")}
        if e:=replay(m,c.States);e!=nil{return nil,e}
        if truth(m.Terms["invariant"],c.States[len(c.States)-1],nil){return nil,fmt.Errorf("trace does not end in safety violation")}
        return map[string]any{"accepted":true,"claim":"reachable safety counterexample","states":len(c.States)},nil
    }
    if c.Kind!="lrat"||c.States!=nil||len(c.Proofs)!=2{return nil,fmt.Errorf("invalid proof evidence")}
    if e:=m.valid(c.Initial);e!=nil{return nil,e};if !truth(m.Terms["initial"],c.Initial,nil){return nil,fmt.Errorf("invalid initial witness")}
    checks:=map[string]lrat.Result{}
    for _,role:=range []string{"base","step"}{proof,ok:=c.Proofs[role];if !ok{return nil,fmt.Errorf("missing %s proof",role)};circuit,r:=encode(m,role);cnf:=circuit.dimacs(r);if proof.SHA!=digest(cnf){return nil,fmt.Errorf("proof CNF differs from reconstructed %s obligation",role)};result,e:=lrat.Check(cnf,proof.LRAT);if e!=nil{return nil,fmt.Errorf("%s: %w",role,e)};checks[role]=result}
    return map[string]any{"accepted":true,"claim":"nonvacuous inductive safety","evidence":"independently checked LRAT","frontend":"oak","translation_trusted":true,"obligations":checks},nil
}
func replay(m *Model,states []State)error{
    if len(states)==0||len(states)>4096{return fmt.Errorf("invalid trace length")}
    for _,s:=range states{if e:=m.valid(s);e!=nil{return e}}
    if !truth(m.Terms["initial"],states[0],nil){return fmt.Errorf("invalid initial state")}
    for i:=1;i<len(states);i++{s,t:=states[i-1],states[i];if stateKey(s)!=stateKey(t)&&!truth(m.Terms["step"],s,t){return fmt.Errorf("illegal transition at %d",i)}};return nil
}
