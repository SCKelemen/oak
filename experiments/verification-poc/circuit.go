package main

import (
    "fmt"
    "sort"
    "strings"
)

type Gate struct { ID int; Op string; Args []int }
type Circuit struct { Count,One int; Clauses [][]int; Inputs map[string]int; Gates []Gate; cache map[string]int }
func newCircuit()*Circuit{c:=&Circuit{Inputs:map[string]int{},cache:map[string]int{}};c.One=c.new();c.Clauses=append(c.Clauses,[]int{c.One});return c}
func (c *Circuit)new()int{c.Count++;return c.Count}
func (c *Circuit)input(name string)int{if c.Inputs[name]==0{c.Inputs[name]=c.new()};return c.Inputs[name]}
func (c *Circuit)gate(op string,x,y int)int{
    switch op{
    case "and":if x==-c.One||y==-c.One||x==-y{return -c.One};if x==c.One||x==y{return y};if y==c.One{return x}
    case "or":if x==c.One||y==c.One||x==-y{return c.One};if x==-c.One||x==y{return y};if y==-c.One{return x}
    case "xor":if x==y{return -c.One};if x==-y{return c.One};if x==c.One{return -y};if y==c.One{return -x};if x==-c.One{return y};if y==-c.One{return x}
    default:panic("unsupported gate")
    }
    a,b:=x,y;if a>b{a,b=b,a};key:=fmt.Sprintf("%s:%d:%d",op,a,b);if z:=c.cache[key];z!=0{return z}
    z:=c.new();c.cache[key]=z
    if op=="and"{c.Clauses=append(c.Clauses,[]int{-z,x},[]int{-z,y},[]int{z,-x,-y})}else if op=="or"{c.Clauses=append(c.Clauses,[]int{z,-x},[]int{z,-y},[]int{-z,x,y})}else{
        for i:=0;i<4;i++{a,b:=x,y;out:=-z;if i&2!=0{a=-a};if i&1!=0{b=-b};if (i&2!=0)!=(i&1!=0){out=z};c.Clauses=append(c.Clauses,[]int{a,b,out})}
    }
    c.Gates=append(c.Gates,Gate{z,op,[]int{x,y}});return z
}
func (c *Circuit)and(args ...int)int{r:=c.One;for _,x:=range args{r=c.gate("and",r,x)};return r}
func (c *Circuit)or(args ...int)int{r:=-c.One;for _,x:=range args{r=c.gate("or",r,x)};return r}
func (c *Circuit)equal(a,b []int)int{xs:=[]int{};for i,x:=range a{xs=append(xs,-c.gate("xor",x,b[i]))};return c.and(xs...)}
func (c *Circuit)add(a,b []int)[]int{
    carry:=-c.One;out:=[]int{}
    for i,x:=range a{y:=b[i];xy:=c.gate("xor",x,y);out=append(out,c.gate("xor",xy,carry));carry=c.or(c.and(x,y),c.and(carry,xy))};return out
}
func (c *Circuit)less(a,b []int)int{r:=-c.One;for i,x:=range a{y:=b[i];r=c.or(c.and(-x,y),c.and(-c.gate("xor",x,y),r))};return r}
func (c *Circuit)constant(n,width int)[]int{xs:=[]int{};for i:=0;i<width;i++{x:=-c.One;if n&(1<<i)!=0{x=c.One};xs=append(xs,x)};return xs}
func (c *Circuit)dimacs(root int)string{
    var out strings.Builder;fmt.Fprintf(&out,"p cnf %d %d\n",c.Count,len(c.Clauses)+1)
    emit:=func(clause []int){seen:=map[int]bool{};for _,x:=range clause{if !seen[x]{fmt.Fprintf(&out,"%d ",x);seen[x]=true}};out.WriteString("0\n")}
    for _,clause:=range c.Clauses{emit(clause)};emit([]int{root});return out.String()
}
func (c *Circuit)priority()[]int{xs:=[]int{};for _,id:=range c.Inputs{xs=append(xs,id)};sort.Ints(xs);return xs}
func encode(m *Model,role string)(*Circuit,int){
    c:=newCircuit()
    var bits func(*Node)[]int
    bits=func(n *Node)[]int{
        switch n.Op{
        case "bool":v:=0;if n.B{v=1};return c.constant(v,1)
        case "byte":return c.constant(n.N,8)
        case "enum":index:=0;for i,s:=range m.Enums[n.Type]{if s==n.Data{index=i;break}};return c.constant(index,m.width(n.Type))
        case "var":r:=[]int{};for i:=0;i<m.width(n.Type);i++{r=append(r,c.input(fmt.Sprintf("%s.%s.%d",n.State,n.Field,i)))};return r
        }
        a:=bits(n.Args[0]);if n.Op=="!"{return []int{-a[0]}};b:=bits(n.Args[1])
        switch n.Op{
        case "ite":d:=bits(n.Args[2]);out:=[]int{};for i,x:=range b{out=append(out,c.or(c.and(a[0],x),c.and(-a[0],d[i])))};return out
        case "&&":return []int{c.and(a[0],b[0])}
        case "||":return []int{c.or(a[0],b[0])}
        case "+":return c.add(a,b)
        case "-":neg:=[]int{};for _,x:=range b{neg=append(neg,-x)};return c.add(c.add(a,neg),c.constant(1,8))
        case "==":return []int{c.equal(a,b)}
        case "!=":return []int{-c.equal(a,b)}
        case "<":return []int{c.less(a,b)}
        case ">":return []int{c.less(b,a)}
        case "<=":return []int{-c.less(b,a)}
        case ">=":return []int{-c.less(a,b)}
        };panic("unknown checked operator")
    }
    domain:=func(p string)int{guards:=[]int{};for _,f:=range m.Fields{v:=bits(&Node{Op:"var",Type:f.Type,State:p,Field:f.Name});if cases:=m.Enums[f.Type];cases!=nil&&len(cases)<1<<len(v){guards=append(guards,c.less(v,c.constant(len(cases),len(v))))}};return c.and(guards...)}
    var root int
    switch role{case "initial":root=c.and(domain("s"),bits(m.Terms["initial"])[0]);case "base":root=c.and(domain("s"),bits(m.Terms["initial"])[0],-bits(m.Terms["invariant"])[0]);case "step":root=c.and(domain("s"),domain("t"),bits(m.Terms["invariant"])[0],bits(m.Terms["step"])[0],-bits(rename(m.Terms["invariant"],"t"))[0]);default:panic("unknown obligation")};return c,root
}
