open Drcpcheck_core.Checker.ProofFacts
open Drcpcheck_core.Checker
open Drcpcheck_core.Lazylist
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

let max_varint_size = 5

(* Read a base-128 varint from the buffered channel. *)
let read_varint_chan chan =
  match input_byte chan with
  | exception End_of_file -> None
  | b0 ->
      let rec go shift acc b n =
        if n > max_varint_size then
          raise (Parse.ParseError "varint too long (corrupt proof)");
        let acc = acc lor ((b land 0x7f) lsl shift) in
        if b land 0x80 = 0 then acc
        else
          match input_byte chan with
          | b' -> go (shift + 7) acc b' (n + 1)
          | exception End_of_file ->
              raise (Parse.ParseError "truncated binary proof")
      in
      Some (go 0 0 b0 1)

module Source = struct
  type t = unit -> PB.proof_step option

  let decode dec =
    try PB.decode_pb_proof_step dec
    with Pbrt.Decoder.Failure e ->
      raise (Parse.ParseError (Pbrt.Decoder.error_to_string e))

  let of_bytes (b : Bytes.t) : t =
    let dec = Pbrt.Decoder.of_bytes b in
    fun () ->
      (try Pbrt.Decoder.skip dec Pbrt.Varint
       with Pbrt.Decoder.Failure e ->
         raise (Parse.ParseError (Pbrt.Decoder.error_to_string e)));
      Some (decode dec)

  let of_channel (chan : in_channel) : t =
    let scratch = ref (Bytes.create 4096) in
    fun () ->
      match read_varint_chan chan with
      | None -> None
      | Some len ->
          if Bytes.length !scratch < len then
            scratch := Bytes.create (Stdlib.max len (2 * Bytes.length !scratch));
          (try really_input chan !scratch 0 len
           with End_of_file -> raise (Parse.ParseError "truncated binary proof"));
          Some (decode (Pbrt.Decoder.of_subbytes !scratch 0 len))
end

let read_proof (read : Source.t) : proofStage list * coq_ProofFact =
  let rec loop steps =
    match read () with
    | None -> raise (Parse.ParseError "No conclusion found in proof")
    | Some message -> (
        match process_step message with
        | Conclusion c ->
            let proof, atomics =
              Parse.convert_steps_to_proof (List.rev steps) Parse.IntMap.empty []
            in
            (proof, Parse.conclusion_fact c atomics)
        | Step s -> loop (s :: steps))
  in
  loop []

let deserialize_binary_proof (source : Bytes.t) :
    proofStage list * coq_ProofFact =
  read_proof (Source.of_bytes source)

let stream_proof (read : Source.t) : proofStream =
  let rec next atomics steps =
    match read () with
    | None -> raise (Parse.ParseError "truncated binary proof")
    | Some message -> (
        match process_step message with
        | Conclusion c -> Single (Parse.conclusion_fact c atomics)
        | Step (Deduction _ as d) -> (
            match Parse.convert_proof_stage (List.rev (d :: steps)) atomics [] with
            | atomics, Some stage, _ -> Cons (stage, Thunk (fun () -> next atomics []))
            | atomics, None, _ -> next atomics [])
        | Step s -> next atomics (s :: steps))
  in
  next Parse.IntMap.empty []
