package main

import (
    "testing"
    "github.com/SCKelemen/oak/semir"
)

// This is a bounded correspondence test, not a compiler-refinement theorem.
// The model's observation specifically reads from event 1, not an equal value
// from another write or the implicit initial flag value.
func publicationExecution(s State, release, acquire bool) semir.MemoryExecution {
    x := semir.MemoryExecution{}
    if s["written"].(bool) {
        x.Events = append(x.Events, semir.MemoryEvent{Thread:0, Sequence:0, Location:1, Access:semir.MemoryAccessWrite})
    }
    if s["published"].(bool) {
        order := semir.MemoryOrderRelaxed
        if release { order = semir.MemoryOrderRelease }
        x.Events = append(x.Events, semir.MemoryEvent{Thread:0, Sequence:1, Location:2, Access:semir.MemoryAccessWrite, Atomic:true, Order:order, HasModification:true, Modification:0})
    }
    if s["observed"].(bool) {
        order := semir.MemoryOrderRelaxed
        if acquire { order = semir.MemoryOrderAcquire }
        x.Events = append(x.Events, semir.MemoryEvent{Thread:1, Sequence:0, Location:2, Access:semir.MemoryAccessRead, Atomic:true, Order:order, HasReadsFrom:true, ReadsFrom:1})
        if release && acquire { x.Synchronizes = []semir.MemorySyncEdge{{From:1, To:2, Kind:semir.MemorySyncReleaseAcquire}} }
    }
    return x
}
func publicationWorkspace(n int) semir.MemoryWorkspace {
    return semir.MemoryWorkspace{Visited:make([]bool,n), Stack:make([]semir.MemoryEventID,n)}
}
func TestPublicationMatchesMemoryExecution(t *testing.T) {
    for _,orders := range []struct{release,acquire bool}{{true,true},{true,false},{false,true},{false,false}} {
        synchronized := orders.release && orders.acquire
        name := "publication-relaxed"
        if synchronized { name = "publication" }
        m := fixture(t,name)
        // Enumerate reachable states without stopping at the first violation.
        all,e := m.states(); if e != nil { t.Fatal(e) }
        reachable := []State{}; seen := map[string]bool{}
        for _,s := range all { if truth(m.Terms["initial"],s,nil) { reachable=append(reachable,s);seen[stateKey(s)]=true } }
        for head:=0;head<len(reachable);head++ {
            s:=reachable[head]
            for _,target:=range all { if !seen[stateKey(target)] && truth(m.Terms["step"],s,target) { seen[stateKey(target)]=true;reachable=append(reachable,target) } }
            x:=publicationExecution(s,orders.release,orders.acquire)
            if e:=x.Validate();e!=nil { t.Fatal(e) }
            if s["observed"].(bool) {
                hb,e:=x.HappensBefore(0,2,publicationWorkspace(len(x.Events)));if e!=nil { t.Fatal(e) }
                if hb!=s["ordered"].(bool)||hb!=synchronized { t.Fatal("model/API publication disagreement",orders,s) }
                x.Events=append(x.Events,semir.MemoryEvent{Thread:1,Sequence:1,Location:1,Access:semir.MemoryAccessRead})
                if e:=x.Validate();e!=nil { t.Fatal(e) }
                race,e:=x.IsDataRace(0,3,publicationWorkspace(4));if e!=nil||race==synchronized { t.Fatal("payload-race corollary disagrees",race,e) }
            } else if s["ordered"].(bool) { t.Fatal("HB recorded before observation") }
        }
        if len(reachable)!=4 { t.Fatal("unexpected publication state space",len(reachable)) }
        if synchronized { cert,e:=localProof(m);if e!=nil { t.Fatal(e) };if _,e:=verify(m,cert);e!=nil { t.Fatal(e) } } else {
            cert,e:=findTrace(m);if e!=nil { t.Fatal(e) };if len(cert.States)!=4 { t.Fatal("expected write/publish/observe trace") };if _,e:=verify(m,cert);e!=nil { t.Fatal(e) }
        }
    }
}
func TestPublicationRequiresTheReadsFromWitness(t *testing.T) {
    s:=State{"written":true,"published":true,"observed":true,"ordered":true}
    x:=publicationExecution(s,true,true);x.Events[2].HasReadsFrom=false
    if e:=x.Validate();e==nil { t.Fatal("SW accepted without reads-from") }
    x=publicationExecution(s,true,false);x.Synchronizes=[]semir.MemorySyncEdge{{From:1,To:2,Kind:semir.MemorySyncReleaseAcquire}}
    if e:=x.Validate();e==nil { t.Fatal("SW accepted for relaxed observation") }
}
