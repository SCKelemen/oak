default Order dec
$include <prelude.sail>
val nested : (bool, int) -> int
function nested(early, n) = {
 x : int = 3; y : int = 7;
 if early then return(31) else {
  match n {
   ? if ? == 1 => {
    match n { ? if ? == 1 => { x = 11; y = 13 }, _ => { y = 17 } }
   },
   ? if ? == 2 => { x = 19 },
   _ => { y = 23 }
  }
 };
 x * 100 + y
}
val shadow_case : (bool, int) -> int
function shadow_case(early, n) = {
 x : int = 5;
 if early then return(31) else {
  match n {
   ? if ? == 1 => { let tempval = 9; x = tempval + 1 },
   _ => { let x = 99; assert(x == 99) }
  }
 };
 x
}
val main : unit -> unit
function main() = {
 print_int("nested false1=",nested(false,1));
 print_int("nested false2=",nested(false,2));
 print_int("nested false0=",nested(false,0));
 print_int("nested true1=",nested(true,1));
 print_int("shadow_case false1=",shadow_case(false,1));
 print_int("shadow_case false0=",shadow_case(false,0))
}
