(* Sail generates Oak_memory and Oak_memory_types from the source-audited
   memory declarations, retaining __defaultRAM and all three wrapper bodies.
   This tests request production, not a state interpreter or a kernel proof. *)
open Sail2_instr_kinds
open Sail2_values
open Sail2_prompt_monad
open Oak_memory_types

let checks = ref 0
let check name condition =
  incr checks;
  if not condition then failwith ("WriteMemory trace check failed: " ^ name)

let eq_regval = {
  Lem_basic_classes.isEqual_method = ( = );
  Lem_basic_classes.isInequal_method = ( <> );
}
let run events program = runTrace eq_regval events program
let has_trace events program = hasTrace eq_regval events program
let done_unit = function Some (Done ()) -> true | _ -> false
let failed = function Some (Fail _) -> true | _ -> false
let rejected = function None -> true | _ -> false
let pending_read = function Some (Read_reg ("__defaultRAM", _)) -> true | _ -> false

let bits width value =
  List.init width (fun i -> if value land (1 lsl (width - 1 - i)) = 0 then B0 else B1)
let bytes = List.map (bits 8) [0xef; 0xcd; 0xab; 0x89; 0x67; 0x45; 0x23; 0x01]
let value = List.concat (List.rev bytes)
let memory size address payload = Oak_memory.__WriteMemory (Nat_big_num.of_int size) address payload
let read selector = E_read_reg ("__defaultRAM", Regval_bitvector_56 selector)
let zero_read = read (bits 56 0)
let ea address = E_write_ea (Write_plain, address, 8)
let data address payload ack = E_write_mem (Write_plain, address, 8, payload, ack)

let () =
  List.iter (fun address ->
    let program = memory 8 (bits 56 address) value in
    check "first request is the actual RAM-selector read" (pending_read (run [] program));
    check "an unanswered read is pending, not a failure or success" (not (has_trace [] program));
    check "memory cannot precede selector read" (rejected (run [ea address] program));
    List.iter (fun selector ->
      let first = read selector in
      check "selector response alone is pending" (not (has_trace [first] program));
      check "selector response exposes exact EA"
        (match run [first] program with
         | Some (Write_ea (Write_plain, a, 8, _)) -> a = address
         | _ -> false);
      check "selector plus EA remains pending" (not (has_trace [first; ea address] program));
      List.iter (fun ack ->
        check "normal return after exact selector/EA/data, either acknowledgement"
          (done_unit (run [first; ea address; data address bytes ack] program))
      ) [true; false]
    ) [bits 56 0; bits 56 0x1234; List.init 56 (fun _ -> BU)];
    List.iter (fun (name, events) -> check name (rejected (run events program))) [
      "wrong register name rejected", [E_read_reg ("__otherRAM", Regval_bitvector_56 (bits 56 0))];
      "data cannot skip EA", [zero_read; data address bytes true];
      "duplicate read rejected", [zero_read; zero_read; ea address; data address bytes true];
      "selector cannot move after memory", [ea address; data address bytes true; zero_read];
      "wrong effective address rejected", [zero_read; ea (address + 1); data address bytes true];
      "wrong size rejected", [zero_read; E_write_ea (Write_plain, address, 4)];
      "release data cannot substitute for plain", [zero_read; ea address; E_write_mem (Write_release, address, 8, bytes, true)];
      "no hidden request after normal return", [zero_read; ea address; data address bytes true; zero_read];
    ]
  ) [0; 0x1000; (1 lsl 52) - 1];

  let program = memory 8 (bits 56 0) value in
  List.iter (fun wrong_type ->
    let events = [E_read_reg ("__defaultRAM", wrong_type)] in
    check "wrong register-value constructor fails the read" (failed (run events program));
    check "wrong constructor emits no memory request" (rejected (run (events @ [ea 0]) program))
  ) [Regval_bool false; Regval_int (Nat_big_num.of_int 0); Regval_vector []];
  (* The generated of_regval checks the constructor, NOT the bit-list length.
     A future trace interpreter must validate width and state provenance. *)
  check "tagged but malformed selector payload is not width-checked"
    (done_unit (run [read [BU]; ea 0; data 0 bytes true] program));

  let unknown_address = memory 8 (BU :: bits 55 0) value in
  check "bad address still waits for selector" (pending_read (run [] unknown_address));
  check "address conversion fails after selector" (failed (run [zero_read] unknown_address));
  check "failed selector prefix counts as hasTrace" (has_trace [zero_read] unknown_address);
  check "failed selector prefix is not normal return" (not (done_unit (run [zero_read] unknown_address)));
  check "no EA after address failure" (rejected (run [zero_read; ea 0] unknown_address));

  let malformed_data = memory 8 (bits 56 0) [B1] in
  check "malformed data still waits for selector" (pending_read (run [] malformed_data));
  check "malformed data still requests EA after selector" (not (has_trace [zero_read] malformed_data));
  check "malformed data fails only after selector and EA" (failed (run [zero_read; ea 0] malformed_data));

  let zero_bytes = List.init 8 (fun _ -> bits 8 0) in
  let first = memory 8 (bits 56 0x1000) (List.concat zero_bytes) in
  let last = memory 8 (bits 56 0x1000) value in
  let both = bind first (fun () -> last) in
  let first_events = [zero_read; ea 0x1000; data 0x1000 zero_bytes true] in
  let last_events = [read (bits 56 0x1234); ea 0x1000; data 0x1000 bytes false] in
  check "two calls retain both reads and both request pairs"
    (done_unit (run (first_events @ last_events) both));
  check "first call leaves a new selector read" (pending_read (run first_events both));
  check "second read cannot be eliminated"
    (rejected (run (first_events @ List.tl last_events) both));
  check "last call alone cannot replace two calls" (rejected (run last_events both));
  check "two-call order cannot be swapped" (rejected (run (last_events @ first_events) both));
  check "bad second read fails after first request pair"
    (failed (run (first_events @ [E_read_reg ("__defaultRAM", Regval_bool false)]) both));
  Printf.printf "Arm Lem WriteMemory traces: %d checks passed\n" !checks
