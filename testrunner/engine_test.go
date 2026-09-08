package testrunner

import (
 "bytes"
 "context"
 "testing"
)

func TestRandomKnownVector(t *testing.T) {
 r:=random{}
 if got:=r.next();got!=0xe220a8397b1dcdaf {t.Fatalf("splitmix64 changed: %x",got)}
 a,b:=randomFor(42,"PropertyA",7),randomFor(42,"PropertyA",7)
 for i:=0;i<100;i++{if a.next()!=b.next(){t.Fatal("replay drift")}}
}
func TestMinimizePreservesFailure(t *testing.T){
 predicate:=func(input []byte)bool{for _,v:=range input{if v>=7{return true}};return false}
 input:=[]byte{1,2,255,4,5}
 best:=Minimize(context.Background(),input,200,predicate)
 if !bytes.Equal(best,[]byte{7}){t.Fatalf("got %v, want [7]",best)}
 if !bytes.Equal(input,[]byte{1,2,255,4,5}){t.Fatal("mutated original")}
}
func TestMinimizeBudgetAndCancellation(t *testing.T){
 calls:=0
 predicate:=func([]byte)bool{calls++;return false}
 Minimize(context.Background(),[]byte{255,255},3,predicate)
 if calls!=3{t.Fatalf("calls %d",calls)}
 ctx,cancel:=context.WithCancel(context.Background());cancel()
 Minimize(ctx,[]byte{255},100,predicate)
 if calls!=3{t.Fatal("ignored cancellation")}
}
func FuzzMinimize(t *testing.F){
 t.Add([]byte{0,1,7,255})
 t.Fuzz(func(t *testing.T,input []byte){
  if len(input)>256{t.Skip()}
  original:=append([]byte(nil),input...)
  predicate:=func(data []byte)bool{return bytes.Contains(data,[]byte{7})}
  best:=Minimize(context.Background(),input,100,predicate)
  if predicate(input) && !predicate(best){t.Fatal("lost failure")}
  if len(best)>len(input) || !bytes.Equal(input,original){t.Fatal("invalid shrink")}
 })
}
func FuzzMutationBounds(t *testing.F){
 t.Add(uint64(1),[]byte{0,255})
 t.Fuzz(func(t *testing.T,seed uint64,input []byte){
  if len(input)>256{t.Skip()}
  original:=append([]byte(nil),input...)
  r:=random{state:seed}
  for i:=0;i<20;i++{out:=mutate(&r,[][]byte{input},256);if len(out)>256{t.Fatal("unbounded mutation")}}
  if !bytes.Equal(input,original){t.Fatal("mutated corpus")}
 })
}
