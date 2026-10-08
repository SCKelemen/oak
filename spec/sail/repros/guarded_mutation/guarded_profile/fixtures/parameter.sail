default Order dec
$include <prelude.sail>
val probe : int -> int
function probe(x) = { let x = 99; x }
val main : unit -> unit
function main() = { print_int("parameter=",probe(5)) }
