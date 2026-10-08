default Order dec
$include <prelude.sail>
val probe : (bool, int) -> int
function probe(early, n) = {
 x : int = 5;
 let r : int = if early then return(31) else {
  match n {
   ? if ? == 1 => { x = 10; 7 },
   _ => { x = 20; 9 }
  }
 };
 x * 100 + r
}
val main : unit -> unit
function main() = {
 print_int("normal=",probe(false,1));
 print_int("fallback=",probe(false,0));
 print_int("early=",probe(true,1))
}
