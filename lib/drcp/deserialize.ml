open Drcpcheck_core.Checker.ProofFacts
open Drcpcheck_core.Checker
open Drcpcheck_core.Lazylist
open Big_int_Z
module PB = Drcp_proto

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

let map_op (op : PB.atomic_op) =
  match op with
  | Eq -> Coq_equal
  | Ne -> Coq_not_equal
  | Le -> Coq_less_equal
  | Ge -> Coq_greater_equal

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

module Resolve = struct
  (* LATER: TRMC *)
  let map_tr f l = List.rev (List.rev_map f l)

  let atom (c : PB.atomic_constraint) : coq_BoundAtomic =
    (c.var, { atm_cmp = map_op c.op; atm_val = big_int_of_int c.value })

  let inference resolve (i : PB.inference_step) : indexedInference =
    {
      iinf_index = big_int_of_int i.id;
      iinf_fact =
        {
          i_premises = map_tr resolve i.premises;
          i_consequent =
            (if i.propagated <> 0 then Some (resolve i.propagated) else None);
        };
      iinf_hint =
        (if i.generated_by <> 0 then [ big_int_of_int i.generated_by ] else []);
      iinf_rule = parse_inf_hint i;
    }

  let stage resolve (n : PB.nogood_step) infs : proofStage =
    {
      s_inferences = infs;
      s_conclusion =
        { i_premises = map_tr resolve n.literals; i_consequent = None };
      s_chain = map_tr big_int_of_int n.propagation_hint;
      s_conclusion_index = big_int_of_int n.id;
    }

  let conclusion resolve (c : PB.conclusion_step) : coq_ProofFact =
    match c with
    | Unsat -> { i_premises = []; i_consequent = None }
    | Objective_bound code ->
        { i_premises = [ resolve (-code) ]; i_consequent = None }
end

let read_proof (read : Source.t) : proofStage list * coq_ProofFact =
  let rec loop atomics infs stages =
    match read () with
    | None -> raise (Parse.ParseError "No conclusion found in proof")
    | Some (Constraint c) ->
        loop (Parse.IntMap.add c.PB.id (Resolve.atom c) atomics) infs stages
    | Some (Inference i) ->
        loop atomics
          (Resolve.inference (Parse.resolve_atomic_id atomics) i :: infs)
          stages
    | Some (Nogood n) ->
        loop atomics []
          (Resolve.stage (Parse.resolve_atomic_id atomics) n (List.rev infs)
          :: stages)
    | Some (Conclusion c) ->
        ( List.rev stages,
          Resolve.conclusion (Parse.resolve_atomic_id atomics) c )
  in
  loop Parse.IntMap.empty [] []

let deserialize_binary_proof (source : Bytes.t) :
    proofStage list * coq_ProofFact =
  read_proof (Source.of_bytes source)

let stream_proof (read : Source.t) : proofStream =
  let rec next atomics infs =
    match read () with
    | None -> raise (Parse.ParseError "truncated binary proof")
    | Some (Constraint c) ->
        next (Parse.IntMap.add c.PB.id (Resolve.atom c) atomics) infs
    | Some (Inference i) ->
        next atomics
          (Resolve.inference (Parse.resolve_atomic_id atomics) i :: infs)
    | Some (Nogood n) ->
        Cons
          ( Resolve.stage (Parse.resolve_atomic_id atomics) n (List.rev infs),
            Thunk (fun () -> next atomics []) )
    | Some (Conclusion c) ->
        Single (Resolve.conclusion (Parse.resolve_atomic_id atomics) c)
  in
  next Parse.IntMap.empty []
