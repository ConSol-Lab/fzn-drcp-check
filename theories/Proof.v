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
  (* | linear *)
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

Definition CPProof := (list (N * Step))%type.

Definition validate_inference (fact : Deduction.Inference) (hint : list Constraint) (rule : InferenceRule) :=
  match rule with
   | cumulative =>
      match hint with
      | [cumulative_c c] => cumulative_checker fact c
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
  (* - destruct hint as [|c [|c0 l]] eqn:Ehint ; try destruct c eqn:Ec ; try easy. *)
  (*   simpl in Hsat. *)
  (*   apply Is_true_eq_true, linear_inference_checker_correct in Hvalid. *)
(*   unfold is_valid_linear_inference in Hvalid. *)
(*   specialize (Hvalid sol). *)
  (*   apply Hvalid. *)
  (*   specialize (Hsat c). *)
  (*   rewrite Ec in Hsat. *)
  (*   simpl in Hsat. *)
  (*   apply Hsat. *)
  (*   left. *)
  (*   reflexivity. *)
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


Record ProofStage := {
  s_inferences : list (N * Inference * (list Constraint) * InferenceRule) ;
  s_conclusion : Inference * list Inference
}.

Definition validate_inference_within_stage (step : N * Inference * (list Constraint) * InferenceRule) : bool :=
  match step with
  | (_, fact, hint, rule) => validate_inference fact hint rule
  end.


Definition validate_nogood_within_stage (step : (Inference * list Inference)) : bool :=
  match step with
  | (fact, chain) => validate_nogood fact chain
  end.

Definition validate_proof_stage (stage : ProofStage) :=
  (* Validate every inference independently *)
  let inferences_ok := forallb 
    validate_inference_within_stage
    stage.(s_inferences)
  in
  (* Check that the conclusion is a valid deduction *)
  let conclusion_ok := validate_nogood_within_stage stage.(s_conclusion) in
  andb inferences_ok conclusion_ok.
  

Definition used_constraints (stage : ProofStage) :=
  let hints :=
    flat_map (fun x => match x with
                       | (_, cs, _) => cs
                       end) stage.(s_inferences)
  in
  let (_, raw_inferences) := stage.(s_conclusion)
  in
  let inferences := map fact_c raw_inferences
  in
  hints ++ inferences.



Lemma valid_proof_stage_implies_conclusion : forall
  (stage : ProofStage) (sol : string -> Z) (conclusion : Inference) (chain : list Inference),
  Is_true (validate_proof_stage stage) ->
  stage.(s_conclusion) = (conclusion, chain) ->
  (forall (c : Constraint),
    In c (used_constraints stage) -> satisfies_constraint c sol
  ) ->
  inference_valid sol conclusion.
Proof.
  intros stage sol conclusion chain Hvalid Estage_conclusion Hcons_sat.
  unfold validate_proof_stage in Hvalid.
  apply andb_prop_elim in Hvalid.
  unfold validate_inference_within_stage, validate_nogood_within_stage in Hvalid.
  destruct Hvalid as [Hinf_valid Hnogood_valid].
  rewrite Estage_conclusion in Hnogood_valid.
  unfold validate_nogood in Hnogood_valid.
  destruct conclusion.(i_consequent) eqn:Econs in Hnogood_valid ;
  try contradiction.
  unfold inference_valid.
  rewrite Econs.
  intros Hvalid_atoms.
  apply Is_true_eq_true in Hinf_valid.
  rewrite forallb_forall in Hinf_valid.
  apply check_deduct_correct with
    (assignment := sol)
    (premises := i_premises conclusion)
    (steps := chain).
  - exact Hvalid_atoms.
  - intros inf Hin_inf.
    specialize (Hcons_sat (fact_c inf)).
    simpl in Hcons_sat.
    apply Hcons_sat.
    unfold used_constraints.
    rewrite Estage_conclusion.
    apply in_or_app.
    right.
    apply in_map, Hin_inf.
  - apply Is_true_eq_true, Hnogood_valid.
Qed.


Fixpoint validate_stateful (csp : ConstraintProblem) (p : CPProof)
  (stage_facts : list (N * Inference * list Constraint * InferenceRule)) :=
  match p with 
  | nil => true
  (* The next fact is a nogood; the proof stage is over, send it to the stage validator
     and, if it approves, proceed with the rest of the proof while forgetting the inferences *)
  | (step_index, nogood fact index_chain) :: p' =>
      (* Unpack the fact from the inferences available on the current stage *)
      let stage_lookup :=
        fun index => flat_map
          (fun stage_fact : (N * Inference * list Constraint * InferenceRule) =>
            match stage_fact with
            | (stage_index, i, _, _) =>
                if N.eqb stage_index index
                then [i]
                else []
            end)
          stage_facts
      in
      (* Unpack the fact from the CSP or forward to the stage lookup *)
      let fact_lookup := 
        fun index => match ConstraintProblem.lookup csp index with
                     | Some (fact_c i) => [i]
                     | _ => stage_lookup index
                     end
      in
      (* Unpack all facts from the index chain *)
      let chain := flat_map fact_lookup index_chain
      in
      (* Store all processed inferences and the newly found conclusion *)
      let stage := {|
        s_inferences := stage_facts ;
        s_conclusion := (
          fact,
          chain
        )
      |}
      in
      (* Add the conclusion into the CSP *)
      let csp' := ConstraintProblem.add
        step_index
        fact
        csp
      in
      (* Keep checking if the stage is valid, declare failure otherwise *)
      if validate_proof_stage stage
      then validate_stateful csp' p' nil
      else false
  (* The next fact is an inference, append it with metadata and keep goind *)
  | (step_index, inference fact hint_indices rule) :: p' =>
      (* Extract the hint constraints *)
      let lookup := fun index =>
        match ConstraintProblem.lookup csp index with
        | Some c => [c]
        | None => []
        end
      in
      let hint := flat_map lookup hint_indices
      in
      (* Store the inference in memory and proceed further *)
      validate_stateful csp p' ((step_index, fact, hint, rule) :: stage_facts)
  end.

Definition validate (csp : ConstraintProblem) (p : CPProof) := validate_stateful csp p nil.


Fixpoint conclusion (p : CPProof) := 
  match p with
  | [] => None
  | [(_, nogood fact _)] => Some fact
  | [(_, inference _ _ _)] => None
  | _ :: p' => conclusion p'
  end.


Definition conclusion_holds (csp : ConstraintProblem) (fact : Deduction.Inference) :=
  forall (sol : string -> Z),
    satisfies_problem csp sol ->
    Deduction.inference_valid sol fact.


Definition used_constraints_memory
  (mem : list (N * Inference * list Constraint * InferenceRule)) :=
  flat_map
  (
    fun x : N * Inference * list Constraint * InferenceRule =>
    match x with
    | (_, _, c, _) => c
    end
  )
  mem.

Lemma nogood_stateful_soundness : forall
  (csp : ConstraintProblem) (p : CPProof) (fact : Deduction.Inference) chain index
  (mem : list (N * Inference * list Constraint * InferenceRule)),
  (forall (c : Constraint),
    In c (used_constraints_memory mem) ->
    exists c_index, lookup csp c_index = Some c
  ) ->
  Is_true (validate_stateful csp ((index, nogood fact chain) :: p) mem) ->
  conclusion_holds csp fact.
Proof.
  unfold conclusion_holds.
  intros csp p fact chain index mem Hmem Hvalid sol Hsat.
  simpl in Hvalid.
  remember (
  flat_map
  (fun index => match lookup csp index with
                | Some (fact_c i) => [i]
                | _ => flat_map
                    (fun stage_fact : (N * Inference * list Constraint * InferenceRule) =>
                    match stage_fact with
                    | (stage_index, i, _, _) =>
                        if N.eqb stage_index index
                        then [i]
                        else []
                    end)
                    mem
                end)
                chain
  ) as full_chain.
  remember {|
    s_inferences := mem ;
    s_conclusion := (fact, full_chain)
  |} as stage.
  destruct (validate_proof_stage stage) eqn:Evalid; try contradiction.
  apply valid_proof_stage_implies_conclusion with (stage := stage) (chain := full_chain).
  - rewrite Evalid.
    reflexivity.
  - rewrite Heqstage.
    reflexivity.
  - intros c Hin_cons.
    unfold used_constraints_memory.
    rewrite Heqstage in Hin_cons.
    unfold used_constraints in Hin_cons.
    simpl in Hin_cons.
    apply in_app_or in Hin_cons.
    destruct Hin_cons as [Hin_mem | Hin_chain].
    + specialize (Hmem c).
      unfold used_constraints_memory in Hmem.
      assert (Hmem':
        In c
        (flat_map
        (fun x : N * Inference * list Constraint * InferenceRule =>
        let (p, _) := x in let (p0, c) := p in let (_, _) := p0 in c) mem)
      ). {
        apply in_flat_map.
        apply in_flat_map in Hin_mem.
        destruct Hin_mem as [x [Hin_mem Hin_hint]].
        destruct x as [x rule'].
        destruct x as [x hint'].
        destruct x as [index' fact'].
        exists (index', fact', hint', rule').
        split ; easy.
      }
      apply Hmem in Hmem'.
      destruct Hmem'.
      apply sat_csp_implies_sat_lookup with (csp := csp) (index := x) ; easy.
    + apply in_map_iff in Hin_chain.
      destruct Hin_chain as [fact' [Efact' Hin_fact']].
      rewrite Heqfull_chain in Hin_fact'.
      apply in_flat_map in Hin_fact'.
      destruct Hin_fact' as [index' [Hin_chain Hlookup]].
      remember (
        flat_map
          (fun stage_fact : N * Inference * list Constraint * InferenceRule
           =>
           let (p0, _) := stage_fact in
           let (p1, _) := p0 in
           let (stage_index, i) := p1 in
           if (stage_index =? index')%N then [i] else []) mem
      ) as mem_lookup eqn:Emem_lookup.
      assert (Hlookup_sat: In fact' mem_lookup -> satisfies_constraint c sol). {
        intros Hin_mem.
        rewrite Emem_lookup in Hin_mem.
        apply in_flat_map in Hin_mem.
        destruct Hin_mem as [x [Hin_x Hin_fact']].
        destruct x as [x rule''].
        destruct x as [x hint''].
        destruct x as [index'' fact''].
        destruct (index'' =? index')%N ; simpl in Hin_fact' ; try contradiction.
        destruct Hin_fact' as [Hin_fact' | F] ; try contradiction.
        rewrite Heqstage in Evalid.
        unfold validate_proof_stage in Evalid.
        apply andb_prop in Evalid.
        destruct Evalid as [Evalid_inf Evalid_nogood].
        simpl in Evalid_inf.
        rewrite forallb_forall in Evalid_inf.
        specialize Evalid_inf with (x := (index'', fact'', hint'', rule'')).
        apply Evalid_inf in Hin_x as Evalid_inf'.
        unfold validate_inference_within_stage in Evalid_inf'.
        rewrite <- Efact', <- Hin_fact'.
        simpl.
        apply validate_inference_soundness with (hint := hint'') (rule := rule'').
        - intros.
          specialize (Hmem c0).
          cut (exists c_index : N, lookup csp c_index = Some c0).
          + intros Hlookup_c0.
            destruct Hlookup_c0.
            apply sat_csp_implies_sat_lookup with (csp := csp) (index := x) ; easy.
          + apply Hmem.
            unfold used_constraints_memory.
            apply in_flat_map.
            exists (index'', fact'', hint'', rule'').
            split ; easy.
        - rewrite Evalid_inf'.
          reflexivity.
      }
      destruct (lookup csp index') as [c'|] eqn:Elookup.
      * destruct c' ; try apply Hlookup_sat, Hlookup.
        simpl in Hlookup.
        destruct Hlookup ; try contradiction.
        rewrite H, Efact' in Elookup.
        apply sat_csp_implies_sat_lookup with (csp := csp) (index := index').
        -- exact Elookup.
        -- exact Hsat.
      * apply Hlookup_sat, Hlookup.
Qed.

Theorem stateful_soundness : forall
  (csp : ConstraintProblem) (p : CPProof) (fact : Deduction.Inference)
    (mem : list (N * Inference * list Constraint * InferenceRule)),
    conclusion p = Some fact ->
    (forall (c : Constraint),
      In c (used_constraints_memory mem) ->
      exists c_index, lookup csp c_index = Some c
    ) ->
    Is_true (validate_stateful csp p mem) ->
    conclusion_holds csp fact.
Proof.
  intros csp p fact mem Econcl Hmem Hvalid.
  generalize dependent mem.
  generalize dependent csp.
  induction p ; try discriminate.
  (* Induction by proof length; base case p = nil is vacuously true. *)
  intros csp mem Hmem Hvalid.
  remember (a :: p) as p' eqn:Ep'.
  destruct a.
  destruct s.
  + (* The upcoming step is an inference. Use inference soundness to
       show that the memory invariant Hmem holds after adding this
       inference with hint constraints. *)
    remember (
    flat_map (fun ix =>
    match lookup csp ix with
    | Some c => [c]
    | None => []
    end) hint) as full_hint eqn:Ehint.
    remember ((n, fact0, full_hint, rule) :: mem) as mem'.
    (* Apply the induction hypothesis with updated memory *)
    apply IHp with (mem := mem').
    - (* Conclusion in the new state is the same. *) 
      simpl in Econcl.
      rewrite Ep' in Econcl.
      destruct p ; inversion Econcl.
      destruct p.
      destruct s ;
      simpl in Econcl ;
      rewrite Econcl ;
      simpl ;
      rewrite H0 ;
      reflexivity.
    - (* Memory invariant holds. *)
      intros.
      rewrite Heqmem' in H.
      simpl in H.
      apply in_app_or in H.
      destruct H.
      * (* Prove validity of hint constraints *)
        rewrite Ehint in H.
        apply in_flat_map in H.
        destruct H.
        destruct H.
        destruct (lookup csp x) eqn:Elookup ; try contradiction.
        simpl in H0.
        destruct H0 ; try contradiction.
        exists x.
        rewrite Elookup, H0.
        reflexivity.
      * (* Prove validity of constraints inserted earlier *)
        apply Hmem, H.
    - (* Checker reports true on the proof suffix with updated memory *)
      rewrite Ep' in Hvalid.
      simpl in Hvalid.
      rewrite <- Ehint, <- Heqmem' in Hvalid.
      exact Hvalid.
  + (* The upcoming step is a nogood. Use the special case lemma
       to show that this fact is entailed by CSP, observe that 
       the conclusion of the proof does not get invalidated by
       adding an entailed constraint, and, if needed, apply the 
       induction hypothesis. *)
    assert (Hholds: conclusion_holds csp fact0). {
      apply nogood_stateful_soundness with (p := p) (chain := chain) (index := n) (mem := mem).
      + exact Hmem.
      + rewrite <- Ep'.
        exact Hvalid.
    }
    destruct p eqn:Ep.
    - (* The proof suffix is a nogood and nothing else.
         Use the special case above to close the goal. *)
      rewrite Ep' in Econcl.
      simpl in Econcl.
      inversion Econcl.
      rewrite H0 in Hholds.
      exact Hholds.
    - (* The upcoming step is a nogood, with more steps on the way.
         Apply the induction hypothesis. *)
      unfold conclusion_holds.
      apply entailed_addition with (fact := fact0) (index := n) ;
      try exact Hholds.
      remember (add n fact0 csp) as csp'.
      unfold conclusion_holds in IHp.
      apply IHp with (mem := []) (csp := csp').
      * (* Proof conclusion stays the same, as it is not empty. *)
        rewrite Ep' in Econcl.
        destruct p ; inversion Ep.
        remember (p0 :: l) as q eqn:Eq.
        simpl in Econcl.
        destruct q ; inversion Eq.
        rewrite <- Eq.
        exact Econcl.
      * (* The next run starts with an empty memory *)
        intros.
        contradiction.
      * (* Checker reports true on the upcoming proof prefix
           after mutating the CSP *)
        rewrite Ep' in Hvalid.
        remember (p0 :: l) as q.
        simpl in Hvalid.
        rewrite <- Heqcsp' in Hvalid.
        destruct (validate_stateful csp' q []) ; try easy.
        rewrite <- andb_lazy_alt, andb_false_r in Hvalid.
        contradiction.
Qed.


Theorem soundness : forall
  (csp : ConstraintProblem) (p : CPProof) (fact : Deduction.Inference),
    conclusion p = Some fact ->
    Is_true (validate csp p) ->
    conclusion_holds csp fact.
Proof.
  intros.
  apply stateful_soundness with (p := p) (mem := []).
  - exact H.
  - simpl.
    intros.
    contradiction.
  - unfold validate in H0.
    exact H0.
Qed.
