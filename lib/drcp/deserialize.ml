open Drcpcheck_core.Checker.ProofFacts
open Drcpcheck_core.Checker
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
      if PB.inference_step_has_label_custom i && i.label_custom <> "" then
        i.label_custom
      else raise (Parse.ParseError "custom inference hint without a label")

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
  let atom (c : PB.atomic_constraint) : coq_BoundAtomic =
    (c.var, { atm_cmp = map_op c.op; atm_val = big_int_of_int c.value })

  let inference resolve (i : PB.inference_step) : indexedInference =
    {
      iinf_index = big_int_of_int i.id;
      iinf_fact =
        {
          i_premises = Parse.map_tr resolve i.premises;
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
        { i_premises = Parse.map_tr resolve n.literals; i_consequent = None };
      s_chain = Parse.map_tr big_int_of_int n.propagation_hint;
      s_conclusion_index = big_int_of_int n.id;
    }

  let conclusion resolve (c : PB.conclusion_step) : coq_ProofFact =
    match c with
    | Unsat -> { i_premises = []; i_consequent = None }
    | Objective_bound code ->
        { i_premises = []; i_consequent = Some (resolve code) }
end

let stream_proof (read : Source.t) : proofStream =
  let t = Parse.Atoms.create () in
  let step () =
    let rec loop infs =
      match read () with
      | None -> raise (Parse.ParseError "truncated binary proof")
      | Some (Constraint c) ->
          Parse.Atoms.define t c.PB.id (Resolve.atom c);
          loop infs
      | Some (Inference i) ->
          loop (Resolve.inference (Parse.Atoms.resolve t) i :: infs)
      | Some (Nogood n) ->
          Parse.Stage (Resolve.stage (Parse.Atoms.resolve t) n (List.rev infs), ())
      | Some (Conclusion c) ->
          Parse.Conclusion (Resolve.conclusion (Parse.Atoms.resolve t) c)
    in
    loop []
  in
  Parse.stream_of step ()

let read_proof (read : Source.t) : proofStage list * coq_ProofFact =
  let rec collect acc (s : proofStream) =
    match s with
    | Conclusion conc -> (List.rev acc, conc)
    | Cons (stage, tl) -> collect (stage :: acc) tl
    | Thunk k -> collect acc (k ())
  in
  collect [] (stream_proof read)

let deserialize_binary_proof (source : Bytes.t) :
    proofStage list * coq_ProofFact =
  read_proof (Source.of_bytes source)
