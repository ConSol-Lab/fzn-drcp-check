open Drcpcheck_core.Checker.ProofFacts
open Drcpcheck_core.Checker
open Drcpcheck_util.Buffer
open Big_int_Z
module PB = Drcp_proto

type step = Conclusion of Parse.conclusion | Step of Parse.step

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
      constraint_id = big_int_of_int id;
      premises;
      consequent = (if propagated <> 0 then Some propagated else None);
      generated_by =
        (if generated_by <> 0 then [ big_int_of_int generated_by ] else []);
      label;
    }

let parse_nogood (n : PB.nogood_step) : Parse.step =
  let id = n.id in
  let literals = n.literals in
  let prophint = n.propagation_hint in

  Deduction
    {
      constraint_id = big_int_of_int id;
      premises = literals;
      sequence = List.rev_map big_int_of_int prophint |> List.rev;
    }

let parse_conclusion (c : PB.conclusion_step) : step =
  match c with
  | Unsat -> Conclusion Parse.Unsat
  | Objective_bound b -> Conclusion (Parse.DualBound b)

let map_op (op : PB.atomic_op) =
  match op with
  | Eq -> Coq_equal
  | Ne -> Coq_not_equal
  | Le -> Coq_less_equal
  | Ge -> Coq_greater_equal

let parse_atomic (c : PB.atomic_constraint) : step =
  let id = c.id in
  let variab = c.var in
  let op = c.op in
  let value = c.value in

  Step
    (AtomDefinition
       {
         id;
         atomic =
           (variab, { atm_cmp = map_op op; atm_val = big_int_of_int value });
       })

let process_step (message : PB.proof_step) : step =
  match message with
  | Constraint c -> parse_atomic c
  | Inference i -> Step (parse_inference i)
  | Nogood n -> Step (parse_nogood n)
  | Conclusion c -> parse_conclusion c

let bin_to_steps bytes =
  let open Pbrt in
  let decoder = Decoder.of_bytes bytes in
  let rec loop_over_buf steps conc i =
    (* skip length prefix *)
    let () =
      try Decoder.skip decoder Varint
      with Decoder.Failure e ->
        raise
          (Parse.ParseError
             (Printf.sprintf "Decoding error: %s" (Decoder.error_to_string e)))
    in

    let step =
      try PB.decode_pb_proof_step decoder
      with Decoder.Failure e ->
        raise
          (Parse.ParseError
             (Printf.sprintf "Decoding error: %s" (Decoder.error_to_string e)))
    in
    match process_step step with
    | Conclusion c -> (List.rev steps, Some c)
    | Step s_proc -> loop_over_buf (s_proc :: steps) conc (i + 1)
  in
  let res = loop_over_buf [] None 0 in
  res

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

let build_stage_from_buf fd buf atomics :
    proofStream * Parse.atomic_map * DBuffer.t =
  (* Collect list of steps *)
  let rec loop_steps acc conc (buf : DBuffer.t) =
    (* Read size of message *)
    let buf = DBuffer.read_if_unavailable fd buf max_varint_size in
    let decoder = Pbrt.Decoder.of_subbytes buf.data buf.off max_varint_size in
    let msg_sz = Pbrt.Decoder.int_as_varint decoder in

    (* Resize buffer accordingly *)
    let buf = DBuffer.advance buf (varint_size msg_sz) in
    let buf = DBuffer.read_if_unavailable fd buf msg_sz in

    let decoder = Pbrt.Decoder.of_subbytes buf.data buf.off msg_sz in
    let step =
      try PB.decode_pb_proof_step decoder
      with Pbrt.Decoder.Failure e ->
        raise
          (Parse.ParseError
             (Printf.sprintf "Decoding error: %s"
                (Pbrt.Decoder.error_to_string e)))
    in
    let buf = DBuffer.advance buf msg_sz in

    match process_step step with
    | Conclusion c -> ((Some c, List.rev acc), buf)
    | Step (Deduction _ as d) -> ((conc, List.rev (d :: acc)), buf)
    | Step s_proc -> loop_steps (s_proc :: acc) conc buf
  in

  let parse_result, new_buf = loop_steps [] None buf in
  let proof, new_atomics =
    Parse.build_stage_from_parse_result parse_result atomics
  in
  (proof, new_atomics, new_buf)

let calc_time_acc (acc : float ref) f =
  let start = Sys.time () in
  let res = f () in
  let end_ = Sys.time () in
  let dur = end_ -. start in
  acc := !acc +. dur;
  res

let deserialize_binary_proof (source : Bytes.t) :
    proofStage list * coq_ProofFact =
  let steps, conclusion = bin_to_steps source in
  let proof, atomics =
    Parse.convert_steps_to_proof steps Parse.IntMap.empty []
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
  (proof, conclusion_fact)

let rec read_available_and_build_stage fd buf atomics : proofStream =
  (* Process all full stages encountered so far *)
  let stages, new_atomics, new_buf = build_stage_from_buf fd buf atomics in

  let next = fun () -> read_available_and_build_stage fd new_buf new_atomics in

  let open Drcpcheck_core.Lazylist in
  let out = append_terminate stages (Thunk next) in

  out
