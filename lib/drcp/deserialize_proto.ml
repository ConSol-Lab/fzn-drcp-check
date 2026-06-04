open Drcpcheck_core.Spec.ProofFacts
open Drcpcheck_core.CheckerStreamed
open Big_int_Z
module PB = Drcp_proto
module IntMap = Map.Make (Int)

let usage = "drcp-bin-parse <file>"
let bin_file = ref ""
let arg_count = ref 0

let time f =
  let t = Sys.time () in
  let res = f () in
  (res, Sys.time () -. t)

let parse_inf_hint (i : PB.inference_step) =
  let h = i.label_hint in
  match h with
  | PB.Initial_domain -> "initial_domain"
  | PB.Linear_bounds -> "linear_bounds"
  | PB.Nogood -> "nogood"
  | PB.Time_table -> "time_table"
  | PB.All_different -> "all_different"
  | PB.Binary_equals -> "binary_equals"
  | PB.Binary_not_equals -> "binary_not_equals"
  | Custom ->
      if PB.inference_step_has_label_custom i then i.label_custom else "none"

let parse_inference (i : PB.inference_step) : Parse.step =
  let id = i.id in
  let premises = i.premises in
  let propagated = i.propagated in
  let generated_by = i.generated_by in
  let label = parse_inf_hint i in

  Inference
    {
      constraint_id = big_int_of_int32 id;
      premises = List.map Int32.to_int premises;
      consequent =
        (if propagated <> 0l then Some (Int32.to_int propagated) else None);
      generated_by =
        (if generated_by <> 0l then [ big_int_of_int32 generated_by ] else []);
      label;
    }

let parse_nogood (n : PB.nogood_step) : Parse.step =
  let id = n.id in
  let literals = n.literals in
  let prophint = n.propagation_hint in

  Deduction
    {
      constraint_id = big_int_of_int32 id;
      premises = List.map Int32.to_int literals;
      sequence = List.map big_int_of_int32 prophint;
    }

type capnp_step = Conclusion of Parse.conclusion | Step of Parse.step

let parse_conclusion (c : PB.conclusion_step) : capnp_step =
  match c with
  | Unsat -> Conclusion Parse.Unsat
  | Objective_bound b -> Conclusion (Parse.DualBound (Int32.to_int b))

let map_op (op : PB.atomic_op) =
  match op with
  | Eq -> Coq_equal
  | Ne -> Coq_not_equal
  | Le -> Coq_less_equal
  | Ge -> Coq_greater_equal

let parse_constraint (c : PB.atomic_constraint) : capnp_step =
  let id = c.id in
  let variab = c.var in
  let op = c.op in
  let value = c.value in

  Step
    (AtomDefinition
       {
         id = Int32.to_int id;
         atomic =
           (variab, { atm_cmp = map_op op; atm_val = big_int_of_int32 value });
       })

let string_of_cstep (step : capnp_step) =
  match step with
  | Step s -> (
      match s with
      | Inference inf -> Printf.sprintf "Inference: %s" inf.label
      | Deduction ded ->
          Printf.sprintf "Deduction: %s" (string_of_big_int ded.constraint_id)
      | AtomDefinition def ->
          Printf.sprintf "AtomDefinition: %s" (fst def.atomic))
  | Conclusion c -> (
      match c with
      | Parse.Unsat -> "Conclusion: Unsat"
      | Parse.DualBound b -> Printf.sprintf "Conclusion: DualBound %d" b)

let process_step (message : PB.proof_step) : capnp_step =
  match message with
  | Constraint c -> parse_constraint c
  | Inference i -> Step (parse_inference i)
  | Nogood n -> Step (parse_nogood n)
  | Conclusion c -> parse_conclusion c

let process_step_or_conc (acc : Parse.step list * Parse.conclusion option)
    (step : PB.proof_step) =
  let steps, conc = acc in
  match process_step step with
  | Conclusion c -> (steps, Some c)
  | Step s -> (s :: steps, conc)

let process (buf : PB.proof_buffer) : Parse.step list * Parse.conclusion option
    =
  List.fold_left process_step_or_conc ([], None) buf.steps

let read_bin bin_file =
  let chan = open_in_bin bin_file in
  let len = in_channel_length chan in
  let bytes = Bytes.create len in
  really_input chan bytes 0 len;
  let decoder = Pbrt.Decoder.of_bytes bytes in
  let rec loop_over_buf steps conc i =
    (* skip length prefix *)
    Pbrt.Decoder.skip decoder Varint;
    let step = try Some (PB.decode_pb_proof_step decoder) with _ -> None in
    match step with
    | Some s -> (
        match process_step s with
        | Conclusion c -> (List.rev steps, Some c)
        | Step s_proc -> loop_over_buf (s_proc :: steps) conc (i + 1))
    | None -> (steps, conc)
  in
  let res = loop_over_buf [] None 0 in
  close_in chan;
  res

let create_decoder ?(off = 0) ?(len = 0) buf =
  match len with
  | 0 -> Pbrt.Decoder.of_bytes buf
  | l -> Pbrt.Decoder.of_subbytes buf off l

(* Adapted from Pbrt: https://github.com/mransan/ocaml-protoc/blob/master/src/runtime/stubs.c *)
let varint_size i =
  if i <= 0x7F then 1
  else if i <= 0x3FFF then 2
  else if i <= 0x1FFFFF then 3
  else if i <= 0xFFFFFFF then 4
  else if i <= 0x7FFFFFFFF then 5
  else if i <= 0x3FFFFFFFFFFF then 6
  else if i <= 0x1FFFFFFFFFFFF then 7
  else 8

let max_varint_size = 5

(** [read_if_unavailable fd buf until off len] checks if [len] bytes can still
    be read from the buffer and fills the buffer with more data from [fd] if
    [off + len] is larger than [until]. It returns the offset in the buffer from
    which to read. *)
let rec read_if_unavailable fd buf until off len =
  let bufsz = Bytes.length buf in
  if off + len > bufsz then (
    let rem_len = until - off in
    Bytes.blit buf off buf 0 rem_len;
    let n = Unix.read fd buf rem_len (bufsz - rem_len) in
    if n = 0 then (
      Unix.close fd;
      failwith "Unexpected end of proof file");
    read_if_unavailable fd buf (rem_len + n) 0 len)
  else if off + len > until then (
    let n = Unix.read fd buf until (bufsz - until) in
    if n = 0 then (
      Unix.close fd;
      failwith "Unexpected end of proof file");
    read_if_unavailable fd buf (until + n) off len)
  else (off, until)

let build_stage_from_buf fd buf off until atomics :
    coq_ProofStream * Parse.atomic_map * (int * int) =
  (* Collect list of steps *)
  let rec loop_steps acc conc off until =
    let off, until = read_if_unavailable fd buf until off max_varint_size in
    let decoder = Pbrt.Decoder.of_subbytes buf off max_varint_size in
    let msg_sz = Pbrt.Decoder.int_as_varint decoder in
    let off, until =
      read_if_unavailable fd buf until (off + varint_size msg_sz) msg_sz
    in
    let decoder = Pbrt.Decoder.of_subbytes buf off msg_sz in
    let step = Some (PB.decode_pb_proof_step decoder) in
    let off = off + msg_sz in

    match step with
    | Some s -> (
        match process_step s with
        | Conclusion c ->
            ((Some c, List.rev acc), (off, until))
        | Step (Deduction _ as d) ->
            ((conc, List.rev (d :: acc)), (off, until))
        | Step s_proc ->
            loop_steps (s_proc :: acc) conc off until)
    | None ->
        raise (Parse.ParseError "reached end of buffer while building stage")
  in

  let parse_result, new_offsets = loop_steps [] None off until in
  let proof, new_atomics =
    Parse.build_stage_from_parse_result parse_result atomics
  in
  (proof, new_atomics, new_offsets)

let calc_time_acc (acc : float ref) f =
  let start = Sys.time () in
  let res = f () in
  let end_ = Sys.time () in
  let dur = end_ -. start in
  acc := !acc +. dur;
  res

let parse_binary_proof (source : string) : coq_ProofStream =
  let steps, conclusion = read_bin source in
  let proof, atomics =
    Parse.convert_steps_to_proof steps Parse.IntMap.empty LNil
  in
  let conclusion_fact =
    match conclusion with
    | Some Unsat -> { i_premises = []; i_consequent = None }
    | Some (DualBound code) ->
        {
          i_premises = [ Parse.resolve_atomic_id atomics (-code) ];
          i_consequent = None;
        }
    | None -> raise (Parse.ParseError "No conclusion found in proof")
  in
  let open Drcpcheck_core.Lazy in
  proof @ Single conclusion_fact

let bufsz = 4096

let rec read_available_and_build_stage fd buf off until atomics : coq_ProofStream =
  (* Process all full stages encountered so far *)
  let stages, new_atomics, (new_off, new_until) =
    build_stage_from_buf fd buf off until atomics
  in

  let next =
   fun () -> read_available_and_build_stage fd buf new_off new_until new_atomics
  in

  let open Drcpcheck_core.Lazy in
  let out = append_terminate stages (Thunk next) in

  out
