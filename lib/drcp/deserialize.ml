open Drcpcheck_core.Checker.ProofFacts
open Drcpcheck_core.Checker
open Big_int_Z
module PB = Drcp_proto

let parse_label (i : PB.inference_step) =
  match i.label with
  | None | Some (PB.Label_custom "") ->
      raise (Parse.ParseError "inference without a label")
  | Some l -> (
      match l with
      | PB.Label_hint PB.Initial_domain -> "initial_domain"
      | PB.Label_hint PB.Linear_bounds -> "linear_bounds"
      | PB.Label_hint PB.Nogood -> "nogood"
      | PB.Label_hint PB.Time_table -> "time_table"
      | PB.Label_hint PB.All_different -> "all_different"
      | PB.Label_hint PB.Binary_equals -> "binary_equals"
      | PB.Label_hint PB.Binary_not_equals -> "binary_not_equals"
      | PB.Label_custom s -> s)

let map_op (op : PB.atomic_op) =
  match op with
  | Eq -> Coq_equal
  | Ne -> Coq_not_equal
  | Le -> Coq_less_equal
  | Ge -> Coq_greater_equal

let max_varint_size = 5

let read_varint next_byte =
  match next_byte () with
  | None -> None
  | Some b0 ->
      let rec go shift acc b n =
        if n > max_varint_size then
          raise (Parse.ParseError "varint too long (corrupt proof)");
        let acc = acc lor ((b land 0x7f) lsl shift) in
        if b land 0x80 = 0 then acc
        else
          match next_byte () with
          | Some b' -> go (shift + 7) acc b' (n + 1)
          | None -> raise (Parse.ParseError "truncated binary proof")
      in
      Some (go 0 0 b0 1)

module Source = struct
  type t = unit -> PB.proof_step option

  let decode dec =
    try PB.decode_pb_proof_step dec
    with Pbrt.Decoder.Failure e ->
      raise (Parse.ParseError (Pbrt.Decoder.error_to_string e))

  let read_header dec =
    let h = PB.decode_pb_header dec in
    if h.PB.format <> Parse.proof_format then
      raise
        (Parse.ParseError
           (Printf.sprintf "expected proof format %s, got %s" Parse.proof_format
              h.PB.format));
    if h.PB.version <> Parse.proof_version then
      raise
        (Parse.ParseError
           (Printf.sprintf "expected proof version %d, got %d" Parse.proof_version
              h.PB.version))

  let of_bytes (b : Bytes.t) : t =
    let dec = Pbrt.Decoder.of_bytes b in
    read_header (Pbrt.Decoder.nested dec);
    fun () ->
      (try Pbrt.Decoder.skip dec Pbrt.Varint
       with Pbrt.Decoder.Failure e ->
         raise (Parse.ParseError (Pbrt.Decoder.error_to_string e)));
      Some (decode dec)

  let of_reader (read : bytes -> int -> int -> int) : t =
    let b1 = Bytes.create 1 in
    let next_byte () =
      if read b1 0 1 = 0 then None else Some (Char.code (Bytes.get b1 0))
    in
    let scratch = ref (Bytes.create 4096) in
    let really_read dst n =
      let got = ref 0 in
      while !got < n do
        let r = read dst !got (n - !got) in
        if r = 0 then raise (Parse.ParseError "truncated binary proof");
        got := !got + r
      done
    in
    let read_frame () =
      match read_varint next_byte with
      | None -> None
      | Some len ->
          if Bytes.length !scratch < len then
            scratch := Bytes.create (Stdlib.max len (2 * Bytes.length !scratch));
          really_read !scratch len;
          Some (Pbrt.Decoder.of_subbytes !scratch 0 len)
    in
    (match read_frame () with
    | None -> raise (Parse.ParseError "missing proof header")
    | Some dec -> read_header dec);
    fun () -> Option.map decode (read_frame ())

  let of_channel (chan : in_channel) : t = of_reader (input chan)
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
      iinf_rule = parse_label i;
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
