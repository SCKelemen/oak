default Order dec
$include <prelude.sail>
val probe : (bool, int) -> int
function probe(early, n) = {
 x : int = 5;
 if early then return(31) else {
  match n {
   ? if ? == 1 => { x = 10 },
   _ => { let (x, y) = (99, 7); assert(x == 99 & y == 7) }
  }
 };
 x
}
val main : unit -> unit
function main() = { print_int("probe(false,0)=",probe(false,0)) }
