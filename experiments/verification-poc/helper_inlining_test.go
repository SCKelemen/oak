package main

import (
 "os"
 "os/exec"
 "path/filepath"
 "regexp"
 "testing"
)

// The decoder names its small operations (rup_space, rup_word, rup_encoded)
// instead of expanding them by hand. The compiler marks such private leaf
// helpers forced-inline, so at the CI optimization level no call to them
// survives in the machine code of the actual checker sources.
func TestCheckerHelpersInline(t *testing.T) {
 cc,err:=exec.LookPath("cc");if err!=nil {t.Skip("C compiler required")}
 generated:=emitChecker(t,"checker_inline.oak",checkerSources(t))
 dir:=t.TempDir();cpath:=filepath.Join(dir,"checker.c");spath:=filepath.Join(dir,"checker.s")
 if err:=os.WriteFile(cpath,[]byte(generated),0644);err!=nil {t.Fatal(err)}
 for _,opt:=range []string{"-O0","-O1"} {
  if output,err:=exec.Command(cc,"-std=c99","-w",opt,"-S","-o",spath,cpath).CombinedOutput();err!=nil {t.Fatalf("cc %s: %v\n%s",opt,err,output)}
  asm,err:=os.ReadFile(spath);if err!=nil {t.Fatal(err)}
  for _,helper:=range []string{"oak_rup_space","oak_rup_word","oak_rup_encoded"} {
   calls:=regexp.MustCompile(`(?m)^\s*(call|callq|bl)\s+_?`+helper+`\b`).FindAllIndex(asm,-1)
   if len(calls)!=0 {t.Fatalf("%s: %d call(s) to %s remain",opt,len(calls),helper)}
  }
 }
 t.Log("checker helpers rup_space, rup_word, rup_encoded: no calls remain at -O0 and -O1")
}
