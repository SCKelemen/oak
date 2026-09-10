package main

import (
    "bytes"
    "context"
    _ "embed"
    "encoding/json"
    "fmt"
    "os"
    "os/exec"
    "path/filepath"
    "regexp"
    "runtime"
    "strings"
    "time"

    "github.com/SCKelemen/oak/experiments/verification-poc/internal/lrat"
)
//go:embed tools.lock.json
var lockData []byte
type ToolPin struct{Version string `json:"version"`;SHA string `json:"sha256"`}
var pins=func()map[string]ToolPin{p:=map[string]ToolPin{};if e:=json.Unmarshal(lockData,&p);e!=nil{panic(e)};return p}()
type Execution struct{
    Command []string `json:"command"`
    ExitCode *int `json:"exit_code"`
    Stdout string `json:"stdout"`
    Stderr string `json:"stderr"`
    Error string `json:"error,omitempty"`
}
type limitedBuffer struct{bytes.Buffer}
func (b *limitedBuffer)Write(p []byte)(int,error){if b.Len()+len(p)>20_000_000{return 0,fmt.Errorf("tool output limit")};return b.Buffer.Write(p)}
func execute(command []string,folder string,timeout time.Duration)Execution{
    r:=Execution{Command:command};ctx,cancel:=context.WithTimeout(context.Background(),timeout);defer cancel()
    cmd:=exec.CommandContext(ctx,command[0],command[1:]...);cmd.Dir=folder;cmd.WaitDelay=time.Second
    stdout,stderr:=&limitedBuffer{},&limitedBuffer{};cmd.Stdout=stdout;cmd.Stderr=stderr;err:=cmd.Run();r.Stdout=stdout.String();r.Stderr=stderr.String()
    if ctx.Err()!=nil{r.Error=ctx.Err().Error();return r}
    if err==nil{code:=0;r.ExitCode=&code;return r}
    if exit,ok:=err.(*exec.ExitError);ok{code:=exit.ExitCode();r.ExitCode=&code}else{r.Error=err.Error()};return r
}
type ToolStatus struct{Available bool `json:"available"`;Reason string `json:"reason,omitempty"`;Probe *Execution `json:"probe,omitempty"`;SHA string `json:"sha256,omitempty"`}
func versionMatches(name,banner string)bool{pattern:=`(^|[^0-9.])`+regexp.QuoteMeta(pins[name].Version)+`([^0-9.]|$)`;return regexp.MustCompile(pattern).MatchString(banner)}
func probe(name,folder,jar string,timeout time.Duration)ToolStatus{
    fail:=func(s string)ToolStatus{return ToolStatus{Reason:s}}
    if name=="go"{if !versionMatches(name,runtime.Version()){return fail("binary built with unpinned Go: "+runtime.Version())};code:=0;r:=Execution{Command:[]string{"runtime.Version"},ExitCode:&code,Stdout:runtime.Version()};return ToolStatus{Available:true,Probe:&r}}
    if name=="tlc"{
        if jar==""{return fail("TLC jar unavailable; pass --tla-jar")};b,e:=os.ReadFile(jar);if e!=nil{return fail(e.Error())};sha:=digest(string(b));if sha!=pins[name].SHA{return fail("TLC jar digest mismatch")}
        r:=execute([]string{"java","-version"},folder,timeout);if r.ExitCode==nil||*r.ExitCode!=0{return fail("Java unavailable")}
        match:=regexp.MustCompile(`version "([0-9]+)`).FindStringSubmatch(r.Stdout+r.Stderr);major:=0;if len(match)==2{fmt.Sscan(match[1],&major)};if major<17{return fail("Java 17+ required")};return ToolStatus{Available:true,Probe:&r,SHA:sha}
    }
    exe,e:=exec.LookPath(name);if e!=nil{return fail(name+" unavailable")};arg:="--version";if name=="z3"{arg="-version"};r:=execute([]string{exe,arg},folder,timeout)
    if r.ExitCode==nil||*r.ExitCode!=0{return fail("version probe failed")};if !versionMatches(name,r.Stdout+"\n"+r.Stderr){return ToolStatus{Reason:"version mismatch",Probe:&r}};return ToolStatus{Available:true,Probe:&r}
}
type BackendResult struct{Passed bool `json:"passed"`;ExpectedSafety bool `json:"expected_safety"`;Reason string `json:"reason,omitempty"`;Claim *Claim `json:"claim,omitempty"`;Established string `json:"established,omitempty"`;Assumptions []string `json:"assumptions,omitempty"`;TrustPath []string `json:"trust_path,omitempty"`;Verdict *Verdict `json:"verdict,omitempty"`;Logs []Execution `json:"logs,omitempty"`}
func runBackend(m *Model,name,out string,safe bool,bound int,timeout time.Duration,jar string,run func([]string,string,time.Duration)Execution)(result BackendResult){
    result.ExpectedSafety=safe
    defer func(){if e:=recover();e!=nil{result.Passed=false;result.Reason=fmt.Sprint(e)}}()
    call:=func(args ...string)Execution{r:=run(args,out,timeout);result.Logs=append(result.Logs,r);demand(r.ExitCode!=nil,"execution failed: "+r.Error);return r}
    write:=func(name,text string){demand(os.WriteFile(filepath.Join(out,name),[]byte(text),0644)==nil,"cannot write generated file")}
    read:=func(name string)string{b,e:=os.ReadFile(filepath.Join(out,name));demand(e==nil,"cannot read generated file: "+name);return string(b)}
    saveTrace:=func(backend,query,raw string,k *int){r:=receipt(m,backend,query,raw,k);c,e:=importTrace(m,backend,query,raw,r,k);demand(e==nil,fmt.Sprintf("trace rejected: %v",e));write(backend+"-output.txt",raw);write(backend+"-receipt.json",jsonText(r));write(backend+"-evidence.json",jsonText(c))}
    switch name{
    case "z3":
        step:="unsat";if !safe{step="sat"};for _,pair:=range [][2]string{{"initial","sat"},{"base","unsat"},{"step",step}}{r:=call("z3","-smt2",filepath.Join(out,pair[0]+".smt2"));demand(*r.ExitCode==0&&strings.TrimSpace(r.Stdout)==pair[1],"unexpected Z3 "+pair[0]+" result")}
        query,e:=bmc(m,bound,false);demand(e==nil,"invalid BMC bound");write("bmc.smt2",query);r:=call("z3","-smt2",filepath.Join(out,"bmc.smt2"));expected:="unsat";if !safe{expected="sat"};demand(*r.ExitCode==0&&strings.TrimSpace(r.Stdout)==expected,"unexpected BMC result")
        if !safe{query,_=bmc(m,bound,true);write("bmc-values.smt2",query);r=call("z3","-smt2",filepath.Join(out,"bmc-values.smt2"));demand(*r.ExitCode==0,"get-value failed");saveTrace("z3",query,r.Stdout,&bound)}
    case "tlc":
        tracePath:=filepath.Join(out,"tlc-trace.json");r:=call("java","-cp",jar,"tlc2.TLC","-workers","1","-dumpTrace","json",tracePath,"-metadir",filepath.Join(out,"states"),"-config","Model.cfg","Model.tla");log:=r.Stdout+r.Stderr
        if safe{demand(*r.ExitCode==0&&strings.Contains(log,"Model checking completed. No error has been found."),"TLC did not report completed safety") }else{demand(*r.ExitCode!=0&&strings.Contains(log,"Invariant Safe is violated"),"TLC did not report expected invariant violation");saveTrace("tlc",read("Model.tla")+"\n"+read("Model.cfg"),read("tlc-trace.json"),nil)}
    case "lean":
        code:=read("Model.lean");defs:=strings.SplitN(code,"theorem base (",2)[0]+"end OakFinite\n";write("Definitions.lean",defs)
        r:=call("lean",filepath.Join(out,"Definitions.lean"));demand(*r.ExitCode==0,"Lean definition projection failed");r=call("lean",filepath.Join(out,"Model.lean"));demand((*r.ExitCode==0)==safe,"unexpected Lean theorem outcome")
    case "cadical":
        proofs:=map[string]Proof{};step:=20;if !safe{step=10}
        for _,pair:=range []struct{role string;code int}{{"initial",10},{"base",20},{"step",step}}{r:=call("cadical","--lrat","--no-binary",filepath.Join(out,pair.role+".cnf"),filepath.Join(out,pair.role+".cadical.lrat"));demand(*r.ExitCode==pair.code,"unexpected CaDiCaL "+pair.role+" outcome");if pair.code==20{cnf,proof:=read(pair.role+".cnf"),read(pair.role+".cadical.lrat");_,e:=lrat.Check(cnf,proof);demand(e==nil,fmt.Sprintf("LRAT rejected: %v",e));proofs[pair.role]=Proof{digest(cnf),proof}}}
        if safe{states,e:=m.states();demand(e==nil,"initial witness enumeration limit");var initial State;for _,s:=range states{if truth(m.Terms["initial"],s,nil){initial=s;break}};c:=&Certificate{Format:evidenceFormat,Digest:m.Digest,Kind:"lrat",Initial:initial,Proofs:proofs};verdict,e:=verify(m,c);result.Verdict=verdict;demand(e==nil,fmt.Sprintf("evidence rejected: %v",e));write("cadical-evidence.json",jsonText(c))}
    default:panic("unsupported backend")
    };result.Passed=true;result.contract(m,name,safe,bound);return result
}

// contract states, for a passed backend row, what the tool established, what
// the row trusts, and the path the result took (roadmap step 4). External
// answers are the tools' claims: only CaDiCaL's LRAT refutations are checked
// independently, and that row carries the checker's verdict.
func (result *BackendResult) contract(m *Model,name string,safe bool,bound int){
    property:="nonvacuous inductive safety";if !safe{property="reachable safety counterexample"}
    claim:=claimFor(m,property);result.Claim=&claim
    path:=append([]string{},sharedTrustPath...)
    switch name{
    case "z3":
        if safe{result.Established=fmt.Sprintf("Z3 answered sat for the initial query, unsat for the base and step obligations, and unsat for the bounded model check to bound %d",bound)}else{result.Established=fmt.Sprintf("Z3 answered sat for the initial query and unsat for the base obligation, sat for the step obligation and for the bounded model check to bound %d, and its violating values replayed as a legal trace",bound)}
        result.Assumptions=append(append([]string{},sharedAssumptions...),"Z3's answers are solver claims, not independently checked proofs","the SMT projection of the model is compared, not proved","a bounded unsat covers only its bound")
        result.TrustPath=append(path,"Go SMT projection (projections.go)","Z3","Go trace replay of counterexample values (import_trace.go)")
    case "tlc":
        if safe{result.Established="TLC completed exhaustive model checking of the projected TLA+ model and found no error"}else{result.Established="TLC reported the expected invariant violation and its trace replayed as a legal trace"}
        result.Assumptions=append(append([]string{},sharedAssumptions...),"TLC's exploration is a tool claim over the projected TLA+ model","the TLA+ projection of the model is compared, not proved")
        result.TrustPath=append(path,"Go TLA+ projection (projections.go)","TLC (pinned tla2tools.jar)","Go trace replay (import_trace.go)")
    case "lean":
        if safe{result.Established="the projected Lean definitions compile and the theorems base and step check"}else{result.Established="the projected Lean definitions compile and the theorems base and step fail to check, as the violation requires"}
        result.Assumptions=append(append([]string{},sharedAssumptions...),"the Lean projection of the model and its theorem statements are compared, not proved","Lean's kernel")
        result.TrustPath=append(path,"Go Lean projection (projections.go)","Lean")
    case "cadical":
        if safe{result.Established="CaDiCaL answered sat for the initial query and produced LRAT refutations of the base and step obligations, which the evidence checker accepted as LRAT evidence: the attached verdict is the claim"}else{result.Established="CaDiCaL answered sat for the initial query, produced an LRAT refutation of the base obligation, and answered sat for the step obligation"}
        result.Assumptions=append(append([]string{},sharedAssumptions...),"CaDiCaL is untrusted search; only its LRAT refutations are checked, by internal/lrat","the Go CNF translation (encode) is compared, not proved")
        result.TrustPath=append(path,"Go CNF encoder (circuit.go)","CaDiCaL (untrusted search)","internal/lrat checker and its corpus gates (compiled Oak, the Lean file model, check_sound, check_refines)")
    }
}
type SuiteResult struct{Format string `json:"format"`;Passed bool `json:"passed"`;Attempt string `json:"attempt"`;Tools map[string]ToolStatus `json:"tools"`;Models map[string]map[string]BackendResult `json:"models"`}
func runSuite(examples,out,jar string,timeout time.Duration)(*SuiteResult,error){
    var e error;out,e=filepath.Abs(out);if e!=nil{return nil,e};if jar!=""{jar,e=filepath.Abs(jar);if e!=nil{return nil,e}}
    if e:=os.MkdirAll(out,0755);e!=nil{return nil,e};attempt,e:=os.MkdirTemp(out,"attempt-");if e!=nil{return nil,e}
    r:=&SuiteResult{Format:"oak-go-integration-1",Passed:true,Attempt:attempt,Tools:map[string]ToolStatus{},Models:map[string]map[string]BackendResult{}}
    for _,name:=range []string{"go","lean","z3","cadical","tlc"}{r.Tools[name]=probe(name,attempt,jar,timeout);r.Passed=r.Passed&&r.Tools[name].Available}
    for _,test:=range []struct{name string;safe bool;bound int}{{"enum",true,3},{"enum-broken",false,3},{"counter",true,5},{"counter-broken",false,5},{"wrap",true,3},{"publication",true,3},{"publication-relaxed",false,3}}{
        results:=map[string]BackendResult{};r.Models[test.name]=results;m,e:=loadModel(filepath.Join(examples,test.name+".json"));if e!=nil{results["frontend"]=BackendResult{Reason:e.Error()};r.Passed=false;continue}
        folder:=filepath.Join(attempt,test.name);if e:=emit(m,folder);e!=nil{return nil,e}
        for _,tool:=range []string{"lean","z3","cadical","tlc"}{if !r.Tools[tool].Available{results[tool]=BackendResult{ExpectedSafety:test.safe,Reason:r.Tools[tool].Reason};r.Passed=false;continue};result:=runBackend(m,tool,folder,test.safe,test.bound,timeout,jar,execute);results[tool]=result;r.Passed=r.Passed&&result.Passed}
    }
    if e:=os.WriteFile(filepath.Join(out,"report.json"),[]byte(jsonText(r)),0644);e!=nil{return nil,e};return r,nil
}
