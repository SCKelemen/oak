(* Executable observations of Arm's unmodified aarch64_extras.lem, translated
   by Lem and linked against Sail's prompt runtime. This is NOT a Lean proof,
   an architectural memory interpreter, or an ASL-to-CAT refinement. *)
open Sail2_instr_kinds
open Sail2_values
open Sail2_prompt_monad

let checks = ref 0
let check name condition =
  incr checks;
  if not condition then failwith ("RAM trace check failed: " ^ name)

let eq_unit = {
  Lem_basic_classes.isEqual_method = (fun () () -> true);
  Lem_basic_classes.isInequal_method = (fun () () -> false);
}
let run events program = runTrace eq_unit events program
let has_trace events program = hasTrace eq_unit events program
let done_unit = function Some (Done ()) -> true | _ -> false
let failed = function Some (Fail _) -> true | _ -> false
let rejected = function None -> true | _ -> false

(* Independent expected bit/byte layout; do not ask mem_bytes_of_bits for the
   expected result of the conversion under test. Lists put the MSB first. *)
let bits width value =
  List.init width (fun i -> if value land (1 lsl (width - 1 - i)) = 0 then B0 else B1)
let bytes = List.map (bits 8) [0xef; 0xcd; 0xab; 0x89; 0x67; 0x45; 0x23; 0x01]
let value = List.concat (List.rev bytes)
let ram ?(selector = bits 56 0) ?(width = 56) size address data =
  (Aarch64_extras.write_ram (Nat_big_num.of_int width) (Nat_big_num.of_int size)
    selector address data : (unit, unit, unit) monad)
let ea address size = E_write_ea (Write_plain, address, size)
let data address size payload ack = E_write_mem (Write_plain, address, size, payload, ack)

let () =
  List.iter (fun address ->
    let program = ram 8 (bits 56 address) value in
    let first = ea address 8 in
    let last = data address 8 bytes true in
    check "empty prefix is pending" (not (has_trace [] program));
    check "EA prefix is pending" (not (has_trace [first] program));
    check "EA exposes exact plain payload request"
      (match run [first] program with
       | Some (Write_mem (Write_plain, a, 8, v, _)) -> a = address && v = bytes
       | _ -> false);
    List.iter (fun ack ->
      let events = [first; data address 8 bytes ack] in
      check "both acknowledgements return normally" (done_unit (run events program));
      check "normal return is a trace" (has_trace events program)
    ) [true; false];
    List.iter (fun (name, events) -> check name (rejected (run events program))) [
      "data cannot precede EA", [last; first];
      "data alone cannot run", [last];
      "duplicate EA rejected", [first; first; last];
      "extra data after Done rejected", [first; last; last];
      "wrong EA address rejected", [ea (address + 1) 8; last];
      "wrong EA size rejected", [ea address 4; last];
      "wrong EA kind rejected", [E_write_ea (Write_release, address, 8); last];
      "wrong data address rejected", [first; data (address + 1) 8 bytes true];
      "wrong data size rejected", [first; data address 4 bytes true];
      "wrong data kind rejected", [first; E_write_mem (Write_release, address, 8, bytes, true)];
      "wrong data bytes rejected", [first; data address 8 (List.rev bytes) true];
      "truncated data rejected", [first; data address 8 (List.tl bytes) true];
    ];
    check "selector is ignored"
      (done_unit (run [first; last] (ram ~selector:[BU] 8 (bits 56 address) value)));
    check "address width parameter is ignored"
      (done_unit (run [first; last] (ram ~width:1 8 (bits 56 address) value)))
  ) [0; 0x1000; (1 lsl 52) - 1];

  let unknown_address = ram 8 [BU] value in
  check "unknown address fails before EA" (failed (run [] unknown_address));
  check "hasTrace includes failure" (has_trace [] unknown_address);
  check "failure is not normal return" (not (done_unit (run [] unknown_address)));
  check "no event follows address failure" (rejected (run [ea 0 8] unknown_address));

  let malformed = ram 8 (bits 56 0) [B1] in
  check "malformed byte payload still requests EA" (not (has_trace [] malformed));
  check "malformed byte payload fails after EA" (failed (run [ea 0 8] malformed));
  check "failed EA prefix counts as hasTrace" (has_trace [ea 0 8] malformed);
  check "failed EA prefix is not normal return" (not (done_unit (run [ea 0 8] malformed)));
  check "no data request after malformed value"
    (rejected (run [ea 0 8; data 0 8 bytes true] malformed));

  (* These are properties/limits of this external interface, not legal Sail
     calls: Sail's dependent widths and a future architectural interpretation
     must supply stronger premises. The wrapper itself does not supply them. *)
  let unknown_byte = List.init 8 (fun _ -> BU) in
  check "undefined data bits survive in a byte request"
    (done_unit (run [ea 0 1; data 0 1 [unknown_byte] true] (ram 1 (bits 56 0) unknown_byte)));
  check "declared size need not equal payload byte count"
    (done_unit (run [ea 0 8; data 0 8 [bits 8 1] true] (ram 8 (bits 56 0) (bits 8 1))));

  let first_bytes = List.init 8 (fun _ -> bits 8 0) in
  let first_call = ram 8 (bits 56 0x1000) (List.concat first_bytes) in
  let last_call = ram 8 (bits 56 0x1000) value in
  let both = bind first_call (fun () -> last_call) in
  let first_events = [ea 0x1000 8; data 0x1000 8 first_bytes true] in
  let last_events = [ea 0x1000 8; data 0x1000 8 bytes true] in
  check "two calls retain both request pairs" (done_unit (run (first_events @ last_events) both));
  check "first call alone leaves second pending" (not (has_trace first_events both));
  check "last write cannot replace two-call trace" (rejected (run last_events both));
  check "two-call request order matters" (rejected (run (last_events @ first_events) both));
  check "exception also counts as hasTrace" (has_trace [] (Exception ()));
  check "exception is not normal return" (not (done_unit (run [] (Exception ()))));
  Printf.printf "Arm Lem RAM traces: %d checks passed\n" !checks
