default Order dec
$include <prelude.sail>
val probe : (bool, int) -> int
function probe(early, n) = {
 x : int = 5;
 if early then return(31) else {
  match n {
   ? if ? == 1 => { x = 10 },
   _ => { x = 17; let x = 99; assert(x == 99) }
  }
 };
 x
}
val main : unit -> unit
function main() = { print_int("probe(false,0)=",probe(false,0)) }
