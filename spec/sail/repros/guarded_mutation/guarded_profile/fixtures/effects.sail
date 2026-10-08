default Order dec
$include <prelude.sail>
register OBS : int
val probe : (bool, bool, int) -> int
function probe(early, fail, n) = {
 x : int = 5;
 OBS = 1;
 if early then return(31) else {
  match n {
   ? if ? == 1 => { x = 10; OBS = 2; assert(not_bool(fail)) },
   _ => { OBS = 3 }
  }
 };
 x
}
val main : unit -> unit
function main() = {
 print_int("normal=",probe(false,false,1)); print_int("state=",OBS);
 print_int("early=",probe(true,false,1)); print_int("state=",OBS);
 print_int("fallback=",probe(false,false,0)); print_int("state=",OBS)
}
