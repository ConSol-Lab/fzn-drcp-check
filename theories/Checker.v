Require Import Checker.Deduction.
(*Require Import Checker.Cumulative.*)
(*Require Import Checker.CumulativeCheck.*)
Require Import Checker.ConstraintProblem.
Import Utility.Maps.
Require Import Bool.
Require Import List.
Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Checker.Spec.
Import Spec.ConstraintDefinitions.
Import Spec.Proofs.
Import Spec.ProofFacts.
Import Coq.Lists.List.ListNotations.
Open Scope Z_scope.


Definition step_fact (step : Step) :=
  match step with
  | inference fact _ _ => fact
  | nogood fact _ => fact
  end.

Record HydratedInference := {
  hinf_index : N ;
  hinf_fact : ProofFact ;
  hinf_hint : list Constraint ;
  hinf_rule : InferenceRule
}.

Record HydratedProofStage := {
  hs_inferences : list HydratedInference ;
  hs_chain : list ProofFact ;
  hs_conclusion : ProofFact ;
  hs_conclusion_index : N
}.

(* TODO: see the comment above Deduction.equiv, currently some equivalent inferences might still return false. *)
Definition validate_inference (fact : ProofFact) (hint : list Constraint) (rule : InferenceRule) :=
  match rule with
  | fact_equiv =>
      match hint with
      | [fact_c ref_fact] => Deduction.equiv fact ref_fact
      | _ => false
      end
      (*| cumulative =>
      match hint with
      | [cumulative_c c] => cumulative_checker fact c
      | _ => false
         end*)
  | linear =>
      match hint with
      | [linear_leq c] => Linear.linear_checker fact c
      | _ => false
      end
  end.


(* Compute validate_inference 
  {|
    i_premises := [("x", Domain.mk_atm_le 5 )];
    i_consequent := Some (("y", Domain.mk_atm_le 3 ));
  |}
  [
  fact_c {|
    i_premises := [("x", Domain.mk_atm_le 5 ) ; ("y", Domain.mk_atm_ge 4)];
    i_consequent := None;
  |}
  ]
  fact_equiv.
Compute validate_inference 
  {|
    i_premises := [("x", Domain.mk_atm_le 5 ) ; ("y", Domain.mk_atm_ge 4)];
    i_consequent := None;
  |}
  [
  fact_c {|
    i_premises := [("x", Domain.mk_atm_le 5 )];
    i_consequent := Some (("y", Domain.mk_atm_le 3 ));
  |}
  ]
  fact_equiv.
 *)

Lemma validate_inference_soundness :
  forall (fact : ProofFact) (hint : list Constraint) (rule : InferenceRule) (sol : string -> Z),
  (forall (c : Constraint), In c hint -> satisfies_constraint c sol) ->
  validate_inference fact hint rule = true ->
  fact_valid sol fact.
Proof.
  intros fact hint rule sol Hsat Hvalid.
  unfold validate_inference in Hvalid.
  destruct rule; simpl in Hvalid.
  - destruct hint as [|c [|c0 l]] eqn:Ehint ; try destruct c eqn:Ec ; try easy.
    apply Deduction.equiv_implies_equisat with (lhs := fact) (rhs := constraint).
    exact Hvalid.
    specialize (Hsat (fact_c constraint)).
    apply Hsat.
    simpl. left. reflexivity.
  - destruct hint as [|c [|c0 l]] eqn:Ehint ; try destruct c eqn:Ec ; try easy.
    apply Linear.linear_checker_soundness with (c := constraint); try assumption.
    specialize (Hsat (linear_leq constraint)).
    apply Hsat.
    simpl. left. reflexivity.
    apply Is_true_eq_left in Hvalid.
    assumption.
  (*- destruct hint as [|c [|c0 l]] eqn:Ehint ; try destruct c eqn:Ec ; try easy.
    apply checker_cumulative with (constr := constraint); try assumption.
    specialize (Hsat (cumulative_c constraint)).
    apply Hsat.
     simpl. left. reflexivity.*)
  (* - destruct hint as [|c [|c0 l]] eqn:Ehint ; try destruct c eqn:Ec ; try easy. *)
  (*   specialize (Hsat (alldifferent_c constraint)). *)
  (*   apply Is_true_eq_left. *)
  (*   apply alldifferent_checker_valid with (constr := constraint); apply Is_true_eq_true; try assumption. *)
  (*   apply Hsat. *)
  (*   simpl. left. reflexivity. *)
Qed.


Definition validate_nogood (fact : ProofFact) (chain : list ProofFact) :=
  match (i_consequent fact) with
  | None => check_deduct fact.(i_premises) chain
  | Some _ => false
  end.



Definition validate_inference_within_stage (step : HydratedInference) :=
  validate_inference step.(hinf_fact) step.(hinf_hint) step.(hinf_rule).


Definition validate_proof_stage (stage : HydratedProofStage) :=
  (* Validate every inference independently *)
  let inferences_ok := forallb 
    validate_inference_within_stage
    stage.(hs_inferences)
  in
  (* Check that the conclusion is a valid deduction *)
  let conclusion_ok := validate_nogood stage.(hs_conclusion) stage.(hs_chain) in
  andb inferences_ok conclusion_ok.
  

Definition used_constraints (stage : HydratedProofStage) :=
  let hints := flat_map hinf_hint stage.(hs_inferences)
  in
  let inferences := map fact_c stage.(hs_chain)
  in
  hints ++ inferences.


Lemma valid_proof_stage_implies_conclusion : forall
  (stage : HydratedProofStage) (sol : string -> Z),
  validate_proof_stage stage = true ->
  (forall (c : Constraint),
    In c (used_constraints stage) -> satisfies_constraint c sol
  ) ->
  fact_valid sol (stage.(hs_conclusion)).
Proof.
  intros stage sol Hvalid Estage_conclusion Hcons_sat.
  unfold validate_proof_stage in Hvalid.
  apply andb_prop in Hvalid.
  unfold validate_inference_within_stage in Hvalid.
  destruct Hvalid as [Hinf_valid Hnogood_valid].
  unfold validate_nogood in Hnogood_valid.
  destruct stage.(hs_conclusion).(i_consequent) eqn:Econs in Hnogood_valid ;
  inversion Hnogood_valid.
  rewrite Econs.
  rewrite forallb_forall in Hinf_valid.
  apply check_deduct_correct with
    (assignment := sol)
    (premises := stage.(hs_conclusion).(i_premises))
    (steps := stage.(hs_chain)) ; try assumption.
  intros inf Hin_inf.
  specialize (Estage_conclusion (fact_c inf)).
  simpl in Estage_conclusion.
  apply Estage_conclusion.
  unfold used_constraints.
  apply in_or_app.
  right.
  apply in_map, Hin_inf.
Qed.

Fixpoint hydrate_deduction_chain (csp : ConstraintProblem) (infs : list IndexedInference) (index_chain : list N) : list ProofFact :=
  match index_chain with
  | nil => nil
  | index :: tail =>
      let chain_tail := hydrate_deduction_chain csp infs tail
      in
      let chain_head :=
        match ConstraintProblem.lookup csp index with
        | Some (fact_c i) => [i]
        | _ => map
            (fun inf => inf.(iinf_fact))
            (filter (fun inf => N.eqb (inf.(iinf_index)) index) infs)
        end
      in chain_head ++ chain_tail
  end.


Lemma hydrated_chain_lookup : forall
  (csp : ConstraintProblem) (infs : list IndexedInference) (index_chain : list N)
  (fact : ProofFact),
  In fact (hydrate_deduction_chain csp infs index_chain) ->
  (exists x, ConstraintProblem.lookup csp x = Some (fact_c fact)) \/
  (exists inf, In inf infs /\ inf.(iinf_fact) = fact).
Proof.
  intros.
  generalize dependent fact.
  induction index_chain as [|index] ; try easy.
  simpl.
  intros fact Hin.
  apply in_app_iff in Hin.
  destruct Hin as [Hin_lookup | Hin_rec].
  - destruct (lookup csp index) as [c|] eqn:Elookup ;
    try destruct c ;
    try (
      right ;
      apply in_map_iff in Hin_lookup ;
      destruct Hin_lookup as [inf [Efact Hin_fact]] ;
      exists inf ;
      split ;
      try easy ;
      apply filter_In in Hin_fact ;
      destruct Hin_fact as [Hin_fact _] ;
      exact Hin_fact 
    ).
    left.
    exists index.
    inversion Hin_lookup ; try easy.
    rewrite <- H, Elookup.
    reflexivity.
  - apply IHindex_chain, Hin_rec.
Qed.


Definition hydrate_inference (csp : ConstraintProblem) (inf : IndexedInference) : HydratedInference :=
  let hint := flat_map (
    fun index =>
    match ConstraintProblem.lookup csp index with
    | Some c => [c]
    | None => []
    end
  )
  (inf.(iinf_hint))
  in
  {|
    hinf_index := inf.(iinf_index) ;
    hinf_fact := inf.(iinf_fact) ;
    hinf_hint := hint ;
    hinf_rule := inf.(iinf_rule)
  |}.


Definition hydrate (csp : ConstraintProblem) (stage : ProofStage) : HydratedProofStage :=
  let inferences := map (hydrate_inference csp) stage.(s_inferences)
  in
  let chain := hydrate_deduction_chain csp stage.(s_inferences) stage.(s_chain)
  in
  {|
    hs_inferences := inferences ;
    hs_conclusion := stage.(s_conclusion) ;
    hs_chain := chain ;
    hs_conclusion_index := stage.(s_conclusion_index) ;
  |}
  .


Fixpoint validate_stages (csp : ConstraintProblem) (p : list ProofStage) :=
  match p with
  | nil => Some csp
  | stage :: p' =>
      let csp' := ConstraintProblem.add
        (stage.(s_conclusion_index))
        (stage.(s_conclusion))
        csp
      in
      if validate_proof_stage (hydrate csp stage)
      then validate_stages csp' p'
      else None
  end.


Theorem step_soundness : forall
  (csp : ConstraintProblem) (p : list ProofStage) (stage : ProofStage),
    (exists csp', validate_stages csp (stage :: p) = Some csp') ->
    fact_holds csp (stage.(s_conclusion)).
Proof.
  intros csp p stage Hvalid.
  simpl in Hvalid.
  destruct Hvalid as [csp' Hvalid].
  (* Show that the proof checker on the hydrated stage returns true *)
  remember (hydrate csp stage) as h_stage.
  destruct (validate_proof_stage h_stage) eqn:Evalid ;
  inversion Hvalid.
  clear Hvalid.
  (* Destruct all parts of the stage definition *)
  destruct stage as [inferences chain conclusion conclusion_index].
  simpl.
  rewrite Heqh_stage in Evalid.
  unfold hydrate in Evalid.
  simpl in Evalid.
  (* Appeal to the proof stage checker soundness *)
  unfold fact_holds.
  intros sol Hsat.
  assert (Hrewrite: conclusion = (hs_conclusion h_stage)). {
    rewrite Heqh_stage.
    simpl.
    reflexivity.
  }
  rewrite Hrewrite.
  clear Hrewrite.
  apply valid_proof_stage_implies_conclusion.
  - (* Rewrite into the proof checker validity *)
    unfold hydrate in Heqh_stage.
    simpl in Heqh_stage.
    rewrite <- Heqh_stage in Evalid.
    rewrite Evalid.
    reflexivity.
  - (* Show that any constraint used by the _hydrated_ stage is valid *)
    intros c Hin_cons.
    unfold used_constraints in Hin_cons.
    apply in_app_iff in Hin_cons.
    destruct Hin_cons as [Hin_hint | Hin_chain].
    + (* The constraint in question has been found in the hint.
          Look up the constraint in the CSP and appeal to the CSP definition. *)
      apply in_flat_map in Hin_hint.
      destruct Hin_hint as [h_inf [Hin_inf Hin_hint]].
      rewrite Heqh_stage in Hin_inf.
      simpl in Hin_inf.
      apply in_map_iff in Hin_inf.
      destruct Hin_inf as [i_inf [Eh_inf Hin_inf]].
      rewrite <- Eh_inf in Hin_hint.
      simpl in Hin_hint.
      apply in_flat_map in Hin_hint.
      destruct Hin_hint as [index [Hin_hint Hin_c]].
      destruct (lookup csp index) eqn:Elookup; try contradiction.
      simpl in Hin_c.
      destruct Hin_c as [Hin_c | F] ; try contradiction.
      rewrite Hin_c in Elookup.
      apply sat_csp_implies_sat_lookup with 
        (csp := csp) (index := index) ; easy.
    + (* The constraint in question has been found in the inference chain.
         Use the lemma `hydrated_chain_lookup` *)
      apply in_map_iff in Hin_chain.
      destruct Hin_chain as [fact [Efact_c Hin_chain]].
      rewrite Heqh_stage in Hin_chain.
      simpl in Hin_chain.
      apply hydrated_chain_lookup in Hin_chain.
      destruct Hin_chain as [Hlookup|Hin_inferences].
      * (* The fact was introduced from the CSP; appeal to the CSP definition. *)
        destruct Hlookup as [index Elookup].
        rewrite <- Efact_c.
        apply sat_csp_implies_sat_lookup with
          (csp := csp) (index := index) ; easy.
      * (* The fact was introduced from the inference chain. Appeal to the 
           correctness of the inference checker. *)
        destruct Hin_inferences as [inf [Hin_inf Einf_fact]].
        unfold validate_proof_stage in Evalid.
        apply andb_prop in Evalid.
        destruct Evalid as [Hvalid_inferences _].
        rewrite forallb_forall in Hvalid_inferences.
        simpl in Hvalid_inferences.
        unfold validate_inference_within_stage in Hvalid_inferences.
        rewrite <- Efact_c.
        simpl.
        remember (hydrate_inference csp inf) as hinf.
        apply validate_inference_soundness with
          (hint := (hinf_hint hinf)) 
          (rule := (hinf_rule hinf)).
          -- (* Check that the hydrated hints are in the CSP *)
             intros c' Hin_hint.
             rewrite Heqhinf in Hin_hint.
             simpl in Hin_hint.
             apply in_flat_map in Hin_hint.
             destruct Hin_hint as [index' [Hin_inf' Hin_c']].
             destruct (lookup csp index') eqn:Elookup' ; try contradiction.
             simpl in Hin_c'.
             destruct Hin_c' as [Hin_c' | F] ; try contradiction.
             rewrite Hin_c' in Elookup'.
             apply sat_csp_implies_sat_lookup with (csp := csp) (index := index') ;
             try easy.
          -- (* Check that the inference checker returns true *)
             assert (Hrewrite: fact = (hinf_fact hinf)). {
               rewrite Heqhinf.
               simpl.
               rewrite Einf_fact.
               reflexivity.
             }
             rewrite Hrewrite.
             clear Hrewrite.
             apply
               Hvalid_inferences with (x := hinf),
               in_map_iff.
             exists inf.
             split ; easy.
Qed.


Definition compare_with_fact (rhs : ProofFact) (lhs : Constraint) :=
  match lhs with
  | fact_c lhs => equiv lhs rhs
  | _ => false
  end.


Definition validate (csp : ConstraintProblem) (p : CPProof) :=
  match validate_stages csp (p.(proof_stages)) with
  | Some csp' => nmap.exists_ (fun k => compare_with_fact (conclusion p)) csp'
  | None => false
  end.


Theorem soundness : checker_sound validate.
Proof.
  unfold checker_sound.
  intros csp p Hvalid.
  generalize dependent csp.
  destruct p as [stages conclusion].
  simpl.
  (* Induction by the sequence of stages *)
  induction stages as [|stage].
  (* Base case is a simple lookup in the original CSP *)
  - unfold validate.
    simpl.
    intros csp Hexists sol Hsat.
    apply nmap_prps.exists_iff in Hexists.
    + destruct Hexists as [index [fact_cons [Hmaps Hequiv]]].
      unfold compare_with_fact in Hequiv.
      destruct fact_cons ; inversion Hequiv.
      apply equiv_implies_equisat with (sol := sol) in Hequiv.
      apply Hequiv.
      unfold satisfies_problem in Hsat.
      specialize (Hsat index (fact_c constraint) Hmaps).
      easy.
    + unfold Morphisms.Proper, Morphisms.respectful.
      intros ix iy Ei cx cy Ec.
      rewrite Ec.
      reflexivity.
  (* Use the induction hypothesis for the remainder of the proof and
     the mutated CSP problem instance *)
  - intros csp Hvalid.
    assert (Hholds: fact_holds csp (stage.(s_conclusion))). {
      apply step_soundness with (p := stages).
      unfold validate in Hvalid.
      Opaque validate_stages.
      simpl in Hvalid.
      Transparent validate_stages.
      destruct (
          validate_stages csp (stage :: stages)
        ) as [csp'|] eqn:Evalid ; inversion Hvalid.
      exists csp'.
      reflexivity.
    }
    unfold fact_holds.
    apply entailed_addition with
      (fact := stage.(s_conclusion))
      (index := stage.(s_conclusion_index)) ;
    try exact Hholds.
    remember (add (stage.(s_conclusion_index)) (stage.(s_conclusion)) csp) as csp'.
    apply IHstages with (csp := csp').
    (* Proof conclusion stays the same, as it is not empty. *)
    unfold validate in Hvalid.
    simpl in Hvalid.
    unfold validate.
    simpl.
    destruct (validate_proof_stage (hydrate csp stage)) eqn:Estage ; inversion Hvalid.
    rewrite Heqcsp'.
    reflexivity.
Qed.
