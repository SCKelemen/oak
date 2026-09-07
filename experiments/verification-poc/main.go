// The verification experiment is a standalone command with no production hooks.
package main

import (
    "flag"
    "fmt"
    "os"
    "path/filepath"
    "time"
    "github.com/SCKelemen/oak/experiments/verification-poc/internal/lrat"
)
func usage()string{return `usage:
  go run . export-boolean --out MODEL.json PROJECT.json
  go run . emit --out DIR PROJECT.json
  go run . prove-local --out CERT.json PROJECT.json
  go run . trace --out CERT.json PROJECT.json
  go run . closed-set --out CERT.json PROJECT.json
  go run . verify PROJECT.json CERT.json
  go run . lrat FORMULA.cnf PROOF.lrat
  go run . suite [--tla-jar FILE] [--out DIR] [--timeout SECONDS]
  go run . import-trace --backend z3|tlc --query FILE --receipt FILE --out CERT.json [--bound N] PROJECT.json RAW_OUTPUT
Options precede positional arguments. All model commands use Oak's native frontend.
`}
func writeArtifact(path,text string)error{if path==""{return fmt.Errorf("--out is required")};if e:=os.MkdirAll(filepath.Dir(path),0755);e!=nil{return e};return os.WriteFile(path,[]byte(text),0644)}
func command(args []string)(any,error){
    if len(args)==0{return nil,fmt.Errorf("%s",usage())};action:=args[0];fs:=flag.NewFlagSet(action,flag.ContinueOnError)
    out:=fs.String("out","","output file or directory");jar:=fs.String("tla-jar","","pinned TLC jar");timeout:=fs.Float64("timeout",60,"external tool timeout in seconds");examples:=fs.String("examples","examples/native","suite projects directory")
    backend:=fs.String("backend","","trace backend");queryFile:=fs.String("query","","original query file (TLC: Model.tla newline Model.cfg)");receiptFile:=fs.String("receipt","","trace receipt");bound:=fs.Int("bound",-1,"BMC bound")
    if e:=fs.Parse(args[1:]);e!=nil{return nil,e};pos:=fs.Args()
    if action=="suite"{if len(pos)!=0||*timeout<=0{return nil,fmt.Errorf("invalid suite arguments")};if *out==""{*out="build/integration"};return runSuite(*examples,*out,*jar,time.Duration(*timeout*float64(time.Second)))}
    if action=="lrat"{if len(pos)!=2{return nil,fmt.Errorf("lrat requires CNF and proof")};a,e:=os.ReadFile(pos[0]);if e!=nil{return nil,e};b,e:=os.ReadFile(pos[1]);if e!=nil{return nil,e};return lrat.Check(string(a),string(b))}
    need:=1;if action=="verify"||action=="import-trace"{need=2};if len(pos)!=need{return nil,fmt.Errorf("%s",usage())}
    if action!="export-boolean"&&action!="emit"&&action!="prove-local"&&action!="trace"&&action!="closed-set"&&action!="verify"&&action!="import-trace"{return nil,fmt.Errorf("unknown action: %s",action)}
    m,e:=loadModel(pos[0]);if e!=nil{return nil,e}
    if action=="export-boolean"{b,e:=exportBoolean(m);if e!=nil{return nil,e};if e:=writeArtifact(*out,jsonText(b));e!=nil{return nil,e};return map[string]any{"generated":true,"format":b.Format,"semantic_digest":m.Digest,"verification_claim":false},nil}
    if action=="emit"{if *out==""{return nil,fmt.Errorf("--out required")};if e:=emit(m,*out);e!=nil{return nil,e};return map[string]any{"generated":true,"semantic_digest":m.Digest,"verification_claim":false},nil}
    var c *Certificate
    switch action{
    case "verify":c=&Certificate{};e=readJSON(pos[1],c)
    case "prove-local":c,e=localProof(m)
    case "trace":c,e=findTrace(m)
    case "closed-set":c,e=closedSet(m)
    case "import-trace":
        var r Receipt;if e:=readJSON(*receiptFile,&r);e!=nil{return nil,e};q,e:=os.ReadFile(*queryFile);if e!=nil{return nil,e};raw,e:=os.ReadFile(pos[1]);if e!=nil{return nil,e};var k *int;if *bound>=0{k=bound};c,e=importTrace(m,*backend,string(q),string(raw),r,k);if e!=nil{return nil,e}
    }
    if e!=nil{return nil,e};result,e:=verify(m,c);if e!=nil{return nil,e};if action!="verify"{if e:=writeArtifact(*out,jsonText(c));e!=nil{return nil,e}};return result,nil
}
func main(){r,e:=command(os.Args[1:]);if e!=nil{fmt.Print(jsonText(map[string]any{"accepted":false,"reason":e.Error()}));os.Exit(1)};fmt.Print(jsonText(r));if suite,ok:=r.(*SuiteResult);ok&&!suite.Passed{os.Exit(2)}}
