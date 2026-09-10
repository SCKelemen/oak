package main

import (
    "fmt"
    "github.com/SCKelemen/oak/experiments/verification-poc/frontend"
    "github.com/SCKelemen/oak/experiments/verification-poc/internal/lrat"
)
const evidenceFormat="oak-evidence-3"

// Verdict is the evidence contract (roadmap step 4): every accepted result
// states exactly what was established, under which assumptions, and through
// which trust path. Nothing in a verdict is inferred from the evidence itself;
// each field is fixed by the kind of evidence checked and by the checker's own
// recorded trust boundary (README, "Go packages and trust").
type Verdict struct {
    Accepted bool `json:"accepted"`
    // Claim is the property the evidence supports, about the identified
    // Oak declarations (roadmap step 3): the claim names the state record and
    // the initial, step, and invariant predicates by name and position in the
    // source the verdict binds by hash and semantic digest.
    Claim Claim `json:"claim"`
    // Established is the fact this checker verified about the evidence.
    Established string `json:"established"`
    // Assumptions are trusted, not checked, by this verdict.
    Assumptions []string `json:"assumptions"`
    // TrustPath lists the components the result passed through, in order.
    TrustPath []string `json:"trust_path"`
    // Unsupported names what the checker rejects rather than trusts.
    Unsupported []string `json:"unsupported,omitempty"`
    // Details carries the evidence-specific numbers and sub-results.
    Details map[string]any `json:"details,omitempty"`
}

// Claim is a property about identified Oak source declarations.
type Claim struct {
    Property string `json:"property"`
    Source string `json:"source"`
    SourceHash string `json:"source_sha256"`
    SemanticDigest string `json:"semantic_digest"`
    State frontend.Declaration `json:"state"`
    Initial frontend.Declaration `json:"initial"`
    Step frontend.Declaration `json:"step"`
    Invariant frontend.Declaration `json:"invariant"`
}

// claimFor names the declarations a property is about. A declaration the
// frontend did not locate keeps its name with no position.
func claimFor(m *Model,property string) Claim {
    locate:=func(name string) frontend.Declaration {
        if d,ok:=m.Declarations[name];ok{return d}
        return frontend.Declaration{Name:name}
    }
    return Claim{
        Property:property,
        Source:m.Config.Source,
        SourceHash:m.Document.SourceHash,
        SemanticDigest:m.Digest,
        State:locate(m.Document.State),
        Initial:locate(m.Config.Initial),
        Step:locate(m.Config.Step),
        Invariant:locate(m.Config.Invariant),
    }
}

// The recorded trust boundary shared by every verdict: the model is exported
// by Oak's frontend and evaluated by the Go typed-model adapter; the source
// and settings are bound by the semantic digest, not re-derived.
var sharedAssumptions=[]string{
    "Oak's frontend exports the narrow model faithfully from the checked program",
    "the Go typed-model adapter (truth, states, valid) implements the model's semantics",
    "the source bytes and project settings bound by the semantic digest are the ones reviewed",
    "Go and the execution environment",
}
var sharedTrustPath=[]string{
    "semantic digest binding (" + evidenceFormat + ")",
    "frontend/ model export",
}

func closedSetVerdict(m *Model,states int) *Verdict {
    return &Verdict{
        Accepted:true,
        Claim:claimFor(m,"nonvacuous reachable safety"),
        Established:"a finite set of states that contains every initial state (at least one), is closed under the step relation, and satisfies the invariant in every member",
        Assumptions:sharedAssumptions,
        TrustPath:append(append([]string{},sharedTrustPath...),"Go closed-set checker (evidence.go)"),
        Details:map[string]any{"states":states},
    }
}

func traceVerdict(m *Model,states int) *Verdict {
    return &Verdict{
        Accepted:true,
        Claim:claimFor(m,"reachable safety counterexample"),
        Established:"a trace that starts in an initial state, follows legal transitions or stutters, and ends in a state violating the invariant",
        Assumptions:sharedAssumptions,
        TrustPath:append(append([]string{},sharedTrustPath...),"Go trace replay (evidence.go)"),
        Details:map[string]any{"states":states},
    }
}

func lratVerdict(m *Model,checks map[string]lrat.Result) *Verdict {
    return &Verdict{
        Accepted:true,
        Claim:claimFor(m,"nonvacuous inductive safety"),
        Established:"an initial-state witness, and LRAT refutations of the initialization and preservation counterexample formulas reconstructed from the source (their SHA-256 matched)",
        Assumptions:append(append([]string{},sharedAssumptions...),
            "the Go CNF translation (encode) is faithful to the model; it is compared, not proved"),
        TrustPath:append(append([]string{},sharedTrustPath...),
            "Go CNF encoder (circuit.go)",
            "internal/lrat checker: its decisions agree with compiled Oak rup_text_check and the Lean file model CertificateFile.check on every corpus case; the Lean model is proved sound (check_sound) and the transliterated Oak decoder proved to refine it (OakTextRefinement.check_refines)"),
        Unsupported:[]string{"RAT hints","binary LRAT","extension variables","SMT proof formats"},
        Details:map[string]any{"obligations":checks},
    }
}
type Proof struct{ SHA string `json:"cnf_sha256"`; LRAT string `json:"lrat"` }
type Certificate struct{
    Format string `json:"format"`
    Digest string `json:"semantic_digest"`
    Kind string `json:"kind"`
    Initial State `json:"initial_witness,omitempty"`
    Proofs map[string]Proof `json:"proofs,omitempty"`
    States []State `json:"states,omitempty"`
}
func verify(m *Model,c *Certificate)(*Verdict,error){
    if c.Format!=evidenceFormat||c.Digest!=m.Digest{return nil,fmt.Errorf("wrong evidence format or source/model identity")}
    if c.Kind=="closed-set" {
        if c.Initial!=nil||c.Proofs!=nil||len(c.States)==0||len(c.States)>1024{return nil,fmt.Errorf("invalid closed-set evidence")}
        members:=map[string]bool{}
        for _,s:=range c.States{if e:=m.valid(s);e!=nil{return nil,e};key:=stateKey(s);if members[key]{return nil,fmt.Errorf("duplicate closed-set state")};members[key]=true;if !truth(m.Terms["invariant"],s,nil){return nil,fmt.Errorf("unsafe closed-set member")}}
        all,e:=m.states();if e!=nil{return nil,e};initials:=0
        for _,s:=range all{if truth(m.Terms["initial"],s,nil){initials++;if !members[stateKey(s)]{return nil,fmt.Errorf("closed set omits an initial state")}}}
        if initials==0{return nil,fmt.Errorf("empty initial set")}
        for _,s:=range c.States{for _,target:=range all{if truth(m.Terms["step"],s,target)&&!members[stateKey(target)]{return nil,fmt.Errorf("closed set omits a successor")}}}
        return closedSetVerdict(m,len(c.States)),nil
    }
    if c.Kind=="trace"{
        if c.Initial!=nil||c.Proofs!=nil{return nil,fmt.Errorf("unexpected trace fields")}
        if e:=replay(m,c.States);e!=nil{return nil,e}
        if truth(m.Terms["invariant"],c.States[len(c.States)-1],nil){return nil,fmt.Errorf("trace does not end in safety violation")}
        return traceVerdict(m,len(c.States)),nil
    }
    if c.Kind!="lrat"||c.States!=nil||len(c.Proofs)!=2{return nil,fmt.Errorf("invalid proof evidence")}
    if e:=m.valid(c.Initial);e!=nil{return nil,e};if !truth(m.Terms["initial"],c.Initial,nil){return nil,fmt.Errorf("invalid initial witness")}
    checks:=map[string]lrat.Result{}
    for _,role:=range []string{"base","step"}{proof,ok:=c.Proofs[role];if !ok{return nil,fmt.Errorf("missing %s proof",role)};circuit,r:=encode(m,role);cnf:=circuit.dimacs(r);if proof.SHA!=digest(cnf){return nil,fmt.Errorf("proof CNF differs from reconstructed %s obligation",role)};result,e:=lrat.Check(cnf,proof.LRAT);if e!=nil{return nil,fmt.Errorf("%s: %w",role,e)};checks[role]=result}
    return lratVerdict(m,checks),nil
}
func replay(m *Model,states []State)error{
    if len(states)==0||len(states)>4096{return fmt.Errorf("invalid trace length")}
    for _,s:=range states{if e:=m.valid(s);e!=nil{return e}}
    if !truth(m.Terms["initial"],states[0],nil){return fmt.Errorf("invalid initial state")}
    for i:=1;i<len(states);i++{s,t:=states[i-1],states[i];if stateKey(s)!=stateKey(t)&&!truth(m.Terms["step"],s,t){return fmt.Errorf("illegal transition at %d",i)}};return nil
}
