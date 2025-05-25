Require Import Checker.Deduction.
Require Import Checker.Cumulative.
Require Import Checker.CumulativeCheck.
Require Import Checker.ConstraintProblem.
Import Utility.Maps.
Require Import Bool.
Require Import List.
Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Import Coq.Lists.List.ListNotations.
Open Scope Z_scope.


Inductive InferenceRule :=
  | linear
  (* TODO This is not _cumulative_ inference rule; look up the canonical naming *)
  | cumulative
  (* | alldifferent *)
  .

Inductive Step := 
  | inference (fact : Deduction.Inference) (hint : list N) (rule : InferenceRule)
  | nogood (fact : Deduction.Inference) (chain : list N).

Definition step_fact (step : Step) :=
  match step with
  | inference fact _ _ => fact
  | nogood fact _ => fact
  end.

Record HydratedInference := {
  hinf_index : N ;
  hinf_fact : Inference ;
  hinf_hint : list Constraint ;
  hinf_rule : InferenceRule
}.

Record HydratedProofStage := {
  hs_inferences : list HydratedInference ;
  hs_chain : list Inference ;
  hs_conclusion : Inference ;
  hs_conclusion_index : N
}.

Record IndexedInference := {
  iinf_index : N ;
  iinf_fact : Inference ;
  iinf_hint : list N ;
  iinf_rule : InferenceRule
}.

Record ProofStage := {
  s_inferences : list IndexedInference ;
  s_chain : list N ;
  s_conclusion : Inference ;
  s_conclusion_index : N
}.

Definition CPProof := (list ProofStage)%type.

Definition validate_inference (fact : Deduction.Inference) (hint : list Constraint) (rule : InferenceRule) :=
  match rule with
  | cumulative =>
      match hint with
      | [cumulative_c c] => cumulative_checker fact c
      | _ => false
      end
  | linear =>
      match hint with
      | [linear_leq c] => Linear.linear_checker fact c
      | _ => false
      end
  end.

Lemma validate_inference_soundness :
  forall (fact : Inference) (hint : list Constraint) (rule : InferenceRule) (sol : string -> Z),
  (forall (c : Constraint), In c hint -> satisfies_constraint c sol) ->
  Is_true (validate_inference fact hint rule) -> 
  inference_valid sol fact.
Proof.
  intros fact hint rule sol Hsat Hvalid.
  unfold validate_inference in Hvalid.
  destruct rule; simpl in Hvalid.
  - destruct hint as [|c [|c0 l]] eqn:Ehint ; try destruct c eqn:Ec ; try easy.
    apply Linear.linear_checker_soundness with (c := constraint); try assumption.
    specialize (Hsat (linear_leq constraint)).
    apply Hsat.
    simpl. left. reflexivity.
  - destruct hint as [|c [|c0 l]] eqn:Ehint ; try destruct c eqn:Ec ; try easy.
    apply checker_cumulative with (constr := constraint); try assumption.
    specialize (Hsat (cumulative_c constraint)).
    apply Hsat.
    simpl. left. reflexivity.
  (* - destruct hint as [|c [|c0 l]] eqn:Ehint ; try destruct c eqn:Ec ; try easy. *)
  (*   specialize (Hsat (alldifferent_c constraint)). *)
  (*   apply Is_true_eq_left. *)
  (*   apply alldifferent_checker_valid with (constr := constraint); apply Is_true_eq_true; try assumption. *)
  (*   apply Hsat. *)
  (*   simpl. left. reflexivity. *)
Qed.


Definition validate_nogood (fact : Inference) (chain : list Inference) := 
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
  Is_true (validate_proof_stage stage) ->
  (forall (c : Constraint),
    In c (used_constraints stage) -> satisfies_constraint c sol
  ) ->
  inference_valid sol (stage.(hs_conclusion)).
Proof.
  intros stage sol Hvalid Estage_conclusion Hcons_sat.
  unfold validate_proof_stage in Hvalid.
  apply andb_prop_elim in Hvalid.
  unfold validate_inference_within_stage in Hvalid.
  destruct Hvalid as [Hinf_valid Hnogood_valid].
  unfold validate_nogood in Hnogood_valid.
  destruct stage.(hs_conclusion).(i_consequent) eqn:Econs in Hnogood_valid ;
  try contradiction.
  rewrite Econs.
  apply Is_true_eq_true in Hinf_valid.
  rewrite forallb_forall in Hinf_valid.
  apply check_deduct_correct with
    (assignment := sol)
    (premises := stage.(hs_conclusion).(i_premises))
    (steps := stage.(hs_chain)).
  - exact Hcons_sat.
  - intros inf Hin_inf.
    specialize (Estage_conclusion (fact_c inf)).
    simpl in Estage_conclusion.
    apply Estage_conclusion.
    unfold used_constraints.
    apply in_or_app.
    right.
    apply in_map, Hin_inf.
  - apply Is_true_eq_true, Hnogood_valid.
Qed.

Fixpoint hydrate_deduction_chain (csp : ConstraintProblem) (infs : list IndexedInference) (index_chain : list N) : list Inference :=
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
  (fact : Inference),
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


Fixpoint validate (csp : ConstraintProblem) (p : CPProof) :=
  match p with
  | nil => true
  | stage :: p' =>
      let csp' := ConstraintProblem.add
        (stage.(s_conclusion_index))
        (stage.(s_conclusion))
        csp
      in
      if validate_proof_stage (hydrate csp stage)
      then validate csp' p'
      else false
  end.


Fixpoint conclusion (p : CPProof) := 
  match p with
  | [] => None
  | [stage] => Some (stage.(s_conclusion))
  | _ :: p' => conclusion p'
  end.


Definition conclusion_holds (csp : ConstraintProblem) (fact : Deduction.Inference) :=
  forall (sol : string -> Z),
    satisfies_problem csp sol ->
    Deduction.inference_valid sol fact.


Theorem step_soundness : forall
  (csp : ConstraintProblem) (p : CPProof) (stage : ProofStage),
    Is_true (validate csp (stage :: p)) ->
    conclusion_holds csp (stage.(s_conclusion)).
Proof.
  intros csp p stage Hvalid.
  simpl in Hvalid.
  (* Show that the proof checker on the hydrated stage returns true *)
  remember (hydrate csp stage) as h_stage.
  destruct (validate_proof_stage h_stage) eqn:Evalid ;
  try contradiction.
  clear Hvalid.
  (* Destruct all parts of the stage definition *)
  destruct stage as [inferences chain conclusion conclusion_index].
  simpl.
  rewrite Heqh_stage in Evalid.
  unfold hydrate in Evalid.
  simpl in Evalid.
  (* Appeal to the proof stage checker soundness *)
  unfold conclusion_holds.
  intros sol Hsat.
  assert (Hrewrite: conclusion = (hs_conclusion h_stage)). {
    rewrite Heqh_stage.
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
        apply Is_true_eq_left, andb_prop_elim in Evalid.
        destruct Evalid as [Hvalid_inferences _].
        apply Is_true_eq_true in Hvalid_inferences.
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
               Is_true_eq_left,
               Hvalid_inferences with (x := hinf),
               in_map_iff.
             exists inf.
             split ; easy.
Qed.


Theorem soundness : forall
  (csp : ConstraintProblem) (p : CPProof) (fact : Deduction.Inference),
    conclusion p = Some fact ->
    Is_true (validate csp p) ->
    conclusion_holds csp fact.
Proof.
  intros csp p fact Hconcl Hvalid.
  generalize dependent csp.
  (* Induction by proof length; base case p = nil is vacuously true. *)
  induction p as [|stage] ; try discriminate.
  intros csp Hvalid.
  destruct p eqn:Ep.
  (* The proof has a single stage; use stage checker soundness directly
     after appropriately unpacking all variables *)
  {
    inversion Hconcl as [Hconcl'].
    apply step_soundness with (p := nil).
    exact Hvalid.
  }
  (* Use the induction hypothesis for the remainder of the proof and
     the mutated CSP problem instance *)
  assert (Hholds: conclusion_holds csp (stage.(s_conclusion))). {
    apply step_soundness with (p := p0 :: l).
    exact Hvalid.
  }
  unfold conclusion_holds.
  apply entailed_addition with
    (fact := stage.(s_conclusion))
    (index := stage.(s_conclusion_index)) ;
    try exact Hholds.
  remember (add (stage.(s_conclusion_index)) (stage.(s_conclusion)) csp) as csp'.
  unfold conclusion_holds in IHp.
  apply IHp with (csp := csp').
  + (* Proof conclusion stays the same, as it is not empty. *)
    easy.
  + (* Checker reports true on the upcoming proof prefix
       after mutating the CSP *)
    remember (p0 :: l) as q.
    unfold validate in Hvalid.
    rewrite <- Heqcsp' in Hvalid.
    destruct (validate_proof_stage (hydrate csp stage)) ; try easy.
Qed.

