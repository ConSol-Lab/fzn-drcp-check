open Big_int_Z
open Drcpcheck_core.Checker.ProofFacts
open Drcpcheck_core.Checker.Proofs
open Drcpcheck_core.Checker.Maps

exception IncompleteProofError
exception UndefinedAtomicCode of string

type inference = {
  constraint_id : big_int;
  premises : string list;
  consequent : string option;
  generated_by : big_int;
  label : coq_InferenceRule;
}

type deduction = {
  constraint_id : big_int;
  premises : string list;
  sequence : big_int list;
}

type atomic_map = coq_BoundAtomic Coq_smap.t
type step = Inference of inference | Deduction of deduction
type ast = { atomics : atomic_map; steps : step list }

let lookup_atomic (map : atomic_map) (code : string) : coq_BoundAtomic =
  match Coq_smap.find code map with
  | None -> raise (UndefinedAtomicCode code)
  | Some atomic -> atomic

let lookup_atomics (map : atomic_map) (codes : string list) :
    coq_BoundAtomic list =
  List.map (lookup_atomic map) codes

let rec parse_stage_rec (atomics : atomic_map) (steps : step list)
    (acc : coq_IndexedInference list) : coq_ProofStage * step list =
  match steps with
  | [] -> raise IncompleteProofError
  | Inference inference :: tail ->
      let inference =
        {
          iinf_index = inference.constraint_id;
          iinf_fact =
            {
              i_premises = lookup_atomics atomics inference.premises;
              i_consequent =
                Option.map (lookup_atomic atomics) inference.consequent;
            };
          iinf_hint = [ inference.generated_by ];
          iinf_rule = inference.label;
        }
      in
      parse_stage_rec atomics tail (inference :: acc)
  | Deduction deduction :: tail ->
      ( {
          s_conclusion_index = deduction.constraint_id;
          s_conclusion =
            {
              i_premises = lookup_atomics atomics deduction.premises;
              i_consequent = None;
            };
          s_chain = deduction.sequence;
          s_inferences = acc;
        },
        tail )

let parse_stage (atomics : atomic_map) (steps : step list) :
    coq_ProofStage * step list =
  parse_stage_rec atomics steps []

(*
let rec complete_cp_proof (atomics : coq_BoundAtomic Coq_smap.t)
    (steps : step list) (acc : coq_CPProof) : coq_CPProof =
  match steps with
  | [] -> acc
  | steps ->
      let stage, tail = parse_stage atomics steps in
      let new_proof =
        {
          proof_stages = acc.proof_stages @ [ acc.conclusion ];
          conclusion = stage;
        }
      in
      complete_cp_proof atomics tail new_proof

let to_cp_proof (parsed : ast) =
  let first_stage, tail = parse_stage parsed.atomics parsed.steps in
  complete_cp_proof parsed.atomics tail
    { proof_stages = []; conclusion = first_stage }
    *)
