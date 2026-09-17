(* Execute Sail's original trace-state replayer with the generated register
   accessors. The imported prompt harness runs its 99 checks first. Neither
   replayer implements Arm concurrency, and their conjunction is only a test
   predicate, never compiler admission or proof of architectural execution. *)
open Sail2_instr_kinds
open Sail2_values
open Sail2_prompt_monad
open Sail2_state_monad
open Oak_memory_types
open Write_memory_trace_test

let checks = ref 0
let check name condition =
  incr checks;
  if not condition then failwith ("State replay check failed: " ^ name)
let replay events state = Sail2_state_replay.runTraceS eq_regval register_accessors events state
let present = function Some _ -> true | None -> false
let require_post name = function
  | Some post -> check name true; post
  | None -> check name false; assert false
let completed_model_trace events program state =
  if done_unit (run events program) then replay events state else None
let initial selector = init_state { __defaultRAM = selector }
let same_state a b =
  a.regstate = b.regstate &&
  Pmap.equal ( = ) a.memstate b.memstate && Pmap.equal ( = ) a.tagstate b.tagstate
let sort_bindings xs = List.sort (fun (a, _) (b, _) -> compare a b) xs

let () =
  List.iter (fun address ->
    let selector = bits 56 0x1234 in
    let base = initial selector in
    let before = {
      base with
      memstate = Pmap.add (address + 3) (bits 8 0xff)
        (Pmap.add (address + 8) (bits 8 0xaa)
          (Pmap.add (address + 1000) (bits 8 0xbb) base.memstate));
      tagstate = List.fold_left (fun tags offset -> Pmap.add (address + offset) B1 tags)
        base.tagstate [0; 1; 2; 3; 4; 5; 6; 7; 8; 1000];
    } in
    let program = memory 8 (bits 56 address) value in
    let events = [read selector; ea address; data address bytes true] in
    check "selector response agrees with actual generated accessor"
      (get_regval "__defaultRAM" before.regstate = Some (Regval_bitvector_56 selector));
    check "state-consistent trace returns normally" (done_unit (run events program));
    let post = require_post "both replayers accept the complete trace"
      (completed_model_trace events program before) in
    check "wrapper preserves generated register state" (post.regstate = before.regstate);
    let expected_bytes = sort_bindings
      (List.mapi (fun i byte -> address + i, byte) bytes @
        [address + 8, bits 8 0xaa; address + 1000, bits 8 0xbb]) in
    check "exact byte-map contents and presence" (Pmap.bindings_list post.memstate = expected_bytes);
    let expected_tags = sort_bindings
      (List.init 8 (fun i -> address + i, B0) @ [address + 8, B1; address + 1000, B1]) in
    check "plain writes clear generic runtime tags only in their declared range"
      (Pmap.bindings_list post.tagstate = expected_tags);
    check "absent byte outside the footprint stays absent" (Pmap.lookup (address + 9) post.memstate = None);
    check "absent tag outside the footprint stays absent" (Pmap.lookup (address + 9) post.tagstate = None);
    (* Lean's pinned SequentialState.tags is Unit, not this bit-valued map.
       The existing Lean footprint therefore cannot certify this tag effect. *)
    check "Lem state changes a real tag map absent from the Lean runtime"
      (not (Pmap.equal ( = ) before.tagstate post.tagstate));

    List.iter (fun (name, invalid_events) ->
      check (name ^ ": state replay alone accepts") (present (replay invalid_events before));
      check (name ^ ": prompt replay rejects") (not (done_unit (run invalid_events program)));
      check (name ^ ": conjunction rejects") (not (present (completed_model_trace invalid_events program before)))
    ) [
      "missing EA", [read selector; data address bytes true];
      "EA after data", [read selector; data address bytes true; ea address];
      "release substituted for plain", [read selector; ea address; E_write_mem (Write_release, address, 8, bytes, true)];
    ];
    List.iter (fun (name, invalid_events) ->
      check (name ^ ": prompt replay alone accepts") (done_unit (run invalid_events program));
      check (name ^ ": state replay rejects") (not (present (replay invalid_events before)));
      check (name ^ ": conjunction rejects") (not (present (completed_model_trace invalid_events program before)))
    ) [
      "selector inconsistent with state", [zero_read; ea address; data address bytes true];
      "false acknowledgement", [read selector; ea address; data address bytes false];
    ]
  ) [0; 0x1000; (1 lsl 52) - 1];

  let before = initial (bits 56 0) in
  let zero_bytes = List.init 8 (fun _ -> bits 8 0) in
  let first = memory 8 (bits 56 0x1000) (List.concat zero_bytes) in
  let last = memory 8 (bits 56 0x1000) value in
  let both = bind first (fun () -> last) in
  let first_events = [zero_read; ea 0x1000; data 0x1000 zero_bytes true] in
  let last_events = [zero_read; ea 0x1000; data 0x1000 bytes true] in
  let post_both = require_post "both complete calls are state consistent"
    (completed_model_trace (first_events @ last_events) both before) in
  let post_last = require_post "state replay alone accepts erasing the first call"
    (replay last_events before) in
  check "even full final model state hides the first same-address write" (same_state post_both post_last);
  check "prompt matcher prevents that erasure" (not (done_unit (run last_events both)));
  check "conjunction prevents that erasure" (not (present (completed_model_trace last_events both before)));
  let changed_second = [read (bits 56 0x1234); ea 0x1000; data 0x1000 bytes true] in
  check "prompt matcher permits inconsistent second selector"
    (done_unit (run (first_events @ changed_second) both));
  check "state replay rejects inconsistent second selector"
    (not (present (replay (first_events @ changed_second) before)));
  let injected_write = E_write_reg ("__defaultRAM", Regval_bitvector_56 (bits 56 0x1234)) in
  let injected = first_events @ [injected_write] @ changed_second in
  check "generated setter lets the state replayer process an injected register write"
    (present (replay injected before));
  check "prompt matcher rejects the injected register write" (not (done_unit (run injected both)));
  check "conjunction rejects the injected register write" (not (present (completed_model_trace injected both before)));

  let malformed_state = initial [BU] in
  check "generated model state can contain a malformed-width selector"
    (get_regval "__defaultRAM" malformed_state.regstate = Some (Regval_bitvector_56 [BU]));
  check "state consistency alone does not establish width or initialization"
    (present (completed_model_trace [read [BU]; ea 0; data 0 bytes true]
      (memory 8 (bits 56 0) value) malformed_state));
  Printf.printf "Arm Lem state replay: %d checks passed\n" !checks
