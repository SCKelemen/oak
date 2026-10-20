default Order dec
$include <prelude.sail>
val repro : (bool, int) -> int
function repro(early, regime) = {
 value : int = 0;
 if early then { return(31) } else {
   match regime {
    ? if ? == 1 => { value = 55 },
    _ => { value = 63 }
   }
 };
 if value == 55 then 55 else 63
}
val main : unit -> unit
function main() = { print_int("repro(false,1) -> ",repro(false,1)) }
