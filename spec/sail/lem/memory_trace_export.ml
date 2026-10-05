(* Observe the actual generated prompt constructors, not a prewritten trace.
   This executable adapter is NOT a kernel proof or an ARM/CAT interpreter.
   Selector and acknowledgement responses are test inputs, not state facts. *)
open Sail2_instr_kinds
open Sail2_values
open Sail2_prompt_monad
open Oak_memory_types

let fail () = failwith "memory trace export rejected"
let eq_regval = {
  Lem_basic_classes.isEqual_method = ( = );
  Lem_basic_classes.isInequal_method = ( <> );
}
let bits width value =
  List.init width (fun i -> if value land (1 lsl (width - 1 - i)) = 0 then B0 else B1)
let bit_text bits =
  String.concat "" (List.map (function B0 -> "0" | B1 -> "1" | BU -> "2") bits)
let memory address bytes =
  Oak_memory.__WriteMemory (Nat_big_num.of_int 8) (bits 56 address)
    (List.concat (List.rev bytes))

let observe program selectors acknowledgements =
  let rec walk remaining selectors acknowledgements events = function
    | Done () ->
        if selectors <> [] || acknowledgements <> [] then fail ();
        List.rev events
    | _ when remaining = 0 -> fail ()
    | Read_reg (name, continue) ->
        if name <> "__defaultRAM" then fail ();
        (match selectors with
         | selector :: rest ->
             let response = Regval_bitvector_56 selector in
             walk (remaining - 1) rest acknowledgements
               (E_read_reg (name, response) :: events) (continue response)
         | [] -> fail ())
    | Write_ea (Write_plain, address, size, continue) ->
        walk (remaining - 1) selectors acknowledgements
          (E_write_ea (Write_plain, address, size) :: events) continue
    | Write_mem (Write_plain, address, size, payload, continue) ->
        (match acknowledgements with
         | response :: rest ->
             walk (remaining - 1) selectors rest
               (E_write_mem (Write_plain, address, size, payload, response) :: events)
               (continue response)
         | [] -> fail ())
    | _ -> fail ()
  in
  let events = walk 16 selectors acknowledgements [] program in
  (* Replay the observed requests through the original pinned runtime too. *)
  match runTrace eq_regval events program with
  | Some (Done ()) -> events
  | _ -> fail ()

let event_text = function
  | E_read_reg ("__defaultRAM", Regval_bitvector_56 selector) ->
      "READ __defaultRAM " ^ bit_text selector
  | E_write_ea (Write_plain, address, size) ->
      Printf.sprintf "EA plain %d %d" address size
  | E_write_mem (Write_plain, address, size, payload, acknowledged) ->
      Printf.sprintf "WRITE plain %d %d %s %b" address size
        (String.concat "," (List.map bit_text payload)) acknowledged
  | _ -> fail ()

let () =
  if Array.length Sys.argv <> 1 then fail ();
  let zero = List.init 8 (fun _ -> bits 8 0) in
  let data = List.map (bits 8) [0xef; 0xcd; 0xab; 0x89; 0x67; 0x45; 0x23; 0x01] in
  let mixed = bind (memory 0x1000 zero) (fun () -> memory 0x1000 data) in
  let identical = bind (memory 0x1000 data) (fun () -> memory 0x1000 data) in
  let cases = [
    "mixed", observe mixed [bits 56 0; bits 56 0x1234] [true; false];
    "identical", observe identical [List.init 56 (fun _ -> BU); List.init 56 (fun _ -> BU)] [true; true];
  ] in
  (* Nothing is printed until both complete traces and all encodings exist. *)
  let output = "OAK_LEM_MEMORY_TRACE_V1\n" ^ String.concat ""
    (List.map (fun (name, events) ->
       "CASE " ^ name ^ "\n" ^ String.concat "\n" (List.map event_text events) ^ "\nDONE\n") cases)
    ^ "END\n" in
  print_string output
