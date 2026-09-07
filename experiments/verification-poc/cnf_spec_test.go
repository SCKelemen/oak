package main

import (
    "encoding/json"
    "fmt"
    "os"
    "testing"

    "github.com/SCKelemen/oak/experiments/verification-poc/internal/lrat"
)

type cnfInstruction struct {
    Op string `json:"op"`
    Value bool `json:"value"`
    Index int `json:"index"`
    Left int `json:"left"`
    Right int `json:"right"`
}
type cnfRow struct {
    X bool `json:"x"`
    Y bool `json:"y"`
    Value bool `json:"value"`
    GoSAT bool `json:"go_sat"`
}
type cnfCase struct {
    Name string `json:"name"`
    Program []cnfInstruction `json:"program"`
    Rows []cnfRow `json:"rows"`
}
func cnfLeaf(name string)*Node {return &Node{Op:"var",Type:"Bool",State:"s",Field:name}}
func cnfExpressions(depth int)[]*Node {
    result:=[]*Node{constantBool(false),constantBool(true),cnfLeaf("x"),cnfLeaf("y")}
    if depth==0{return result}
    children:=cnfExpressions(depth-1)
    for _,x:=range children {result=append(result,expression("!","Bool",x))}
    for _,op:=range []string{"&&","||"} {for _,x:=range children {for _,y:=range children {
        result=append(result,expression(op,"Bool",x,y))
    }}}
    return result
}
// Independent source evaluator: no circuit nodes, CNF clauses, or solver calls.
func cnfValue(n *Node,x,y bool)bool {
    switch n.Op {
    case "bool":return n.B
    case "var":if n.Field=="x"{return x};return y
    case "!":return !cnfValue(n.Args[0],x,y)
    case "&&":return cnfValue(n.Args[0],x,y)&&cnfValue(n.Args[1],x,y)
    case "||":return cnfValue(n.Args[0],x,y)||cnfValue(n.Args[1],x,y)
    default:panic("not a Boolean corpus expression")
    }
}
func cnfProgram(n *Node,out *[]cnfInstruction)int {
    instruction:=cnfInstruction{Op:n.Op,Value:n.B}
    if n.Field=="y"{instruction.Index=1}
    if len(n.Args)>0{instruction.Left=cnfProgram(n.Args[0],out)}
    if len(n.Args)>1{instruction.Right=cnfProgram(n.Args[1],out)}
    *out=append(*out,instruction);return len(*out)-1
}
func cnfExtensionExists(f lrat.Formula,inputs map[string]int,x,y bool)bool {
    // Enumerate arbitrary auxiliary values; checking only the circuit's own
    // computed extension would miss clauses that allow spurious solutions.
    for mask:=0;mask<1<<f.Variables;mask++ {
        bit:=func(id int)bool{return mask&(1<<(id-1))!=0}
        if bit(inputs["s.x.0"])!=x || bit(inputs["s.y.0"])!=y {continue}
        satisfied:=true
        for _,clause:=range f.Clauses {
            yes:=false
            for literal:=range clause {
                id:=literal;if id<0{id=-id}
                if bit(id)==(literal>0){yes=true;break}
            }
            if !yes{satisfied=false;break}
        }
        if satisfied{return true}
    }
    return false
}
func TestBooleanCNFSpecification(t *testing.T) {
    expressions:=cnfExpressions(2)
    if len(expressions)!=3244{t.Fatal("unexpected exhaustive domain size")}
    x,y:=cnfLeaf("x"),cnfLeaf("y")
    shared:=expression("&&","Bool",x,y)
    // Deeper examples exercise caching, commutative reuse, and complements.
    expressions=append(expressions,
        expression("||","Bool",shared,expression("&&","Bool",y,x)),
        expression("&&","Bool",shared,expression("!","Bool",shared)),
        expression("||","Bool",shared,expression("!","Bool",shared)),
        expression("!","Bool",expression("!","Bool",expression("!","Bool",shared))),
        expression("&&","Bool",expression("||","Bool",x,y),expression("||","Bool",expression("!","Bool",x),expression("!","Bool",y))),
    )
    cases:=[]cnfCase{}
    accepted:=0
    for i,n:=range expressions {
        m:=&Model{Fields:[]Field{{Name:"x",Type:"Bool"},{Name:"y",Type:"Bool"}},Enums:map[string][]string{},Terms:map[string]*Node{"initial":n}}
        circuit,root:=encode(m,"initial")
        formula,err:=lrat.Parse(circuit.dimacs(root));if err!=nil{t.Fatal(err)}
        if formula.Variables>12{t.Fatal("exhaustive assignment bound exceeded")}
        if circuit.Inputs["s.x.0"]<=0 || circuit.Inputs["s.y.0"]<=0{t.Fatal("missing inputs")}
        c:=cnfCase{Name:fmt.Sprintf("bool-%04d",i),Program:[]cnfInstruction{},Rows:[]cnfRow{}}
        cnfProgram(n,&c.Program)
        for assignment:=0;assignment<4;assignment++ {
            xv,yv:=assignment&1!=0,assignment&2!=0
            want:=cnfValue(n,xv,yv)
            sat:=cnfExtensionExists(formula,circuit.Inputs,xv,yv)
            if sat!=want{t.Fatalf("%s input %d: CNF=%t expression=%t",c.Name,assignment,sat,want)}
            c.Rows=append(c.Rows,cnfRow{X:xv,Y:yv,Value:want,GoSAT:sat})
            if sat{accepted++}
        }
        cases=append(cases,c)
    }
    t.Logf("Boolean CNF corpus: %d expressions, %d valuations (%d satisfiable, %d unsatisfiable)",len(cases),len(cases)*4,accepted,len(cases)*4-accepted)
    if path:=os.Getenv("OAK_BOOLEAN_CNF_CORPUS_OUT");path!="" {
        data,err:=json.Marshal(cases);if err!=nil{t.Fatal(err)}
        if err=os.WriteFile(path,data,0600);err!=nil{t.Fatal(err)}
    }
}
