Require Import Checker.Atomic.
(* Require Import Checker.Linear. *)
Require Import Checker.DomainVar.
Require Import Checker.Deduction.
Require Import Checker.Cumulative.
Require Import Checker.CumulativeCheck.
(* Require Import Checker.AllDifferentCheck. *)
Require Import Checker.Nogood.
Require Import Checker.Variable.
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

Definition Proof := (list (N * Step))%type.

Definition validate_inference (fact : Deduction.Inference) (hint : list Constraint) (rule : InferenceRule) :=
  match rule with
  (* | linear => *)
  (*     match hint with *)
  (*     | [linear_leq c] => linear_checker fact c *)
  (*     | _ => false *)
  (*     end *)
  | cumulative =>
      match hint with
      | [cumulative_c c] => cumulative_checker fact c
      | _ => false
      end
  (* | _ => false *)
  (* | alldifferent => *)
  (*   match hint with *)
  (*   | [alldifferent_c c] => alldifferent_checker fact c *)
  (*   | _ => false *)
  (*   end *)
  end.

Lemma validate_inference_soundness :
  forall (fact : Inference) (hint : list Constraint) (rule : InferenceRule) (sol : string -> Z),
  (forall (c : Constraint), In c hint -> Is_true(satisfies_constraint c sol)) ->
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
  s_inferences : list (Inference * (list Constraint) * InferenceRule) ;
  s_conclusion : Inference * list Inference
}.

Definition validate_inference_within_stage (step : Inference * (list Constraint) * InferenceRule) : bool :=
  match step with
  | (fact, hint, rule) => validate_inference fact hint rule
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
  flat_map (fun x => match x with
                     | (_, cs, _) => cs
                     end) stage.(s_inferences).


Lemma valid_proof_stage_implies_conclusion : forall
  (stage : ProofStage) (sol : string -> Z) (conclusion : Inference) (chain : list Inference),
  Is_true (validate_proof_stage stage) ->
  stage.(s_conclusion) = (conclusion, chain) ->
  (forall (c : Constraint),
    In c (used_constraints stage) -> Is_true (satisfies_constraint c sol)
  ) ->
  (forall (i : Inference),
    In i chain -> exists hint rule, In (i, hint, rule) stage.(s_inferences)
  ) ->
  inference_valid sol conclusion.
Proof.
  intros stage sol conclusion chain Hvalid Estage_conclusion Hcons_sat Hinf_sat.
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
  assert (Hinf_valid_expl:
    forall fact hint rule,
    In (fact, hint, rule) (s_inferences stage) ->
    validate_inference fact hint rule = true
  ). {
    intros.
    specialize (Hinf_valid (fact, hint, rule)).
    simpl in Hinf_valid.
    apply Hinf_valid, H.
  }
  apply check_deduct_correct with
    (assignment := sol)
    (premises := i_premises conclusion)
    (steps := chain).
  - exact Hvalid_atoms.
  - intros inf Hin_inf.
    specialize (Hinf_sat inf Hin_inf).
    destruct Hinf_sat as [hint [rule Hin_hint_rule]].
    apply validate_inference_soundness with (hint := hint) (rule := rule).
    + intros c Hin_cons.
      apply Hcons_sat.
      unfold used_constraints.
      apply in_flat_map.
      exists (inf, hint, rule).
      split.
      exact Hin_hint_rule.
      exact Hin_cons.
    + apply Is_true_eq_left, Hinf_valid_expl, Hin_hint_rule.
  - apply Is_true_eq_true, Hnogood_valid.
Qed.


Definition FactMap := nmap.t Inference.


Fixpoint read_proof_stage (csp : ConstraintProblem) (p : Proof) (fact_map : FactMap) : option ProofStage :=
  match p with
  | [] => None
  | step :: steps =>
      match step with
      | (step_index, nogood fact index_chain) =>
          let empty_stage := {|
            s_inferences := [] ;
            s_conclusion := (
              fact,
              (* TODO unpack index_chain from fact_map *)
              nil
            )
          |}
          in Some empty_stage
      | (step_index, inference fact hint_indices rule) => 
          match read_proof_stage csp steps fact_map with
          | None => None
          | Some stage => 
              let filled_inference := (
                fact,
                (* TODO unpack all hint_indices with fact_map *)
                nil,
                rule
              ) in
              let filled_stage := {|
                s_inferences := filled_inference :: (stage.(s_inferences)) ;
                s_conclusion := stage.(s_conclusion)
              |}
              in Some filled_stage
          end
      end
  end.



Fixpoint validate_stateful (csp : ConstraintProblem) (p : Proof)
  (fact_map : FactMap) (stage_facts : list (Inference * list Constraint * InferenceRule)) :=
  match p with 
  | nil => true
  (* The next fact is a nogood; the proof stage is over, send it to the stage validator
     and, if it approves, proceed with the rest of the proof while forgetting the inferences *)
  | (step_index, nogood fact index_chain) :: p' =>
      (* Unpack the fact from the chain of indices *)
      let fact_lookup := 
        fun index => match nmap.find index fact_map with
                     | Some i => [i]
                     | None => []
                     end
      in
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
      if validate_proof_stage stage
      (* Add the conclusion into the fact map *)
      then validate_stateful csp p' (nmap.add step_index fact fact_map) nil
      else false
  (* The next fact is an inference, append it with metadata and keep goind *)
  | (step_index, inference fact hint_indices rule) :: p' =>
      (* Extract the hint constraints *)
      let lookup := fun index =>
        match nth_error (constraints csp) (N.to_nat index) with
        | Some c => [c]
        | None => []
        end
      in
      let hint := flat_map lookup hint_indices
      in
      validate_stateful csp p' fact_map ((fact, hint, rule) :: stage_facts)
  end.

Definition validate (csp : ConstraintProblem) (p : Proof) :=
  validate_stateful csp p nmap.empty nil.


Lemma if_else_rewrite : forall (b : bool), (if b then false else false) = false. 
Proof.
  intros.
  destruct b ; reflexivity.
Qed.

Lemma if_else_false : forall (a b : bool), (if b then a else false) = a && b.
Proof.
  intros.
  destruct a, b ; reflexivity.
Qed.

(* Lemma soundness_with_kb : forall (csp : ConstraintProblem) (s : list Step) (c : Conclusion) (inferences : list Clause) (nogoods : list Clause), *)
(*   Is_true (validate_kb csp s c inferences nogoods) -> *)
(*   (forall (sol : Assignment), *)
(*     Is_true (satisfies_problem csp sol) -> *)
(*     forall (f : Clause), In f inferences \/ In f nogoods -> Is_true(satisfies_nogood f sol)) -> *)
(*   conclusion_holds csp c. *)
(* Proof. *)
(*   (* Induction by proof length *) *)
(*   intros csp s c inferences nogoods Hvalid Hsat. *)
(*   generalize dependent nogoods. *)
(*   generalize dependent inferences. *)
(*   induction s as [|head_step tail_steps IH] ; simpl. *)
(*   - (* Base case: empty proof *) *)
(*     intros. *)
(*     destruct c eqn:Ec. *)
(*     apply orb_prop_elim in Hvalid. *)
(*     (* Show that an empty clause is in the KB, *)
(*       which cannot be satisfied by definition *) *)
(*     destruct Hvalid as [Hvalid|Hvalid] ;  *)
(*     apply Is_true_eq_true, existsb_exists in Hvalid ; *)
(*     destruct Hvalid as [x [Hin Hnil]] ; *)
(*     destruct x ; *)
(*     try easy ; *)
(*     unfold conclusion_holds ; *)
(*     intros sol ; *)
(*     simpl ; *)
(*     destruct (satisfies_problem csp sol) eqn:Esat ; *)
(*     simpl ; *)
(*     try easy ; *)
(*     apply Is_true_eq_left in Esat ; *)
(*     specialize (Hsat sol Esat nil) as Hsat_empty ; *)
(*     simpl in Hsat_empty ; *)
(*     apply Hsat_empty. *)
(*     + right. *)
(*       apply Hin. *)
(*     + left. *)
(*       apply Hin. *)
(*   - (* Induction step: show that (n+1) steps are valid against any KB *)
(*     if the last n steps are valid against any KB. *) *)
(*     intros. *)
(*     destruct head_step eqn:Ehead. *)
(*     + (* If the next step is an inference, use the inference checker correctness *)
(*          and the induction hypothesis after adding the fact to the inferences list *) *)
(*       apply IH with (inferences := fact :: inferences) (nogoods := nogoods). *)
(*       * (* The proof tail is valid *) *)
(*         destruct (validate_kb csp tail_steps c (fact :: inferences) nogoods) ; try easy. *)
(*         simpl. *)
(*         rewrite if_else_rewrite in Hvalid. *)
(*         contradiction. *)
(*       * (* Any feasible solution satisfies the KB. *) *)
(*         intros sol Hsat_sol f. *)
(*         specialize (Hsat sol Hsat_sol f). *)
(*         intros Hin. *)
(*         destruct Hin as [Hin_inf | Hin_nogood]. *)
(*         -- (* Show that the newly added inference is satisfied by *)
(*            any feasible solution since it is derived by a checker from the model constraints. *) *)
(*            simpl in Hin_inf. *)
(*            destruct Hin_inf as [Heq | Hin_inf]. *)
(*            ++ rewrite if_else_false in Hvalid. *)
(*               apply andb_prop_elim in Hvalid. *)
(*               destruct Hvalid as [_ Hforall]. *)
(*               remember (flat_map (fun index => *)
(*               match nth_error (constraints csp) index with *)
(*               | Some found_cons => [found_cons] *)
(*               | None => [] *)
(*               end *)
(*               ) hint) as hint_cons. *)
(*               apply validate_inference_soundness with (rule := rule) (hint := hint_cons) ; *)
(*               try rewrite <- Heq ; *)
(*               try easy. *)
(*               intros hint_c Hin_c. *)
(*               unfold satisfies_problem in Hsat_sol. *)
(*               apply Is_true_eq_true in Hsat_sol. *)
(*               rewrite forallb_forall in Hsat_sol. *)
(*               specialize (Hsat_sol hint_c). *)
(*               apply Is_true_eq_left, Hsat_sol. *)
(*               rewrite Heqhint_cons in Hin_c. *)
(*               apply in_flat_map in Hin_c. *)
(*               destruct Hin_c as [index [_ Hin_by_index]]. *)
(*               destruct (nth_error (constraints csp) index) eqn:Elookup; try easy. *)
(*               simpl in Hin_by_index. *)
(*               destruct Hin_by_index ; try contradiction. *)
(*               apply nth_error_In in Elookup. *)
(*               rewrite H in Elookup. *)
(*               apply Elookup. *)
(*            ++ apply Hsat. *)
(*               left. *)
(*               apply Hin_inf. *)
(*         -- (* All nogoods are copied from the previous iteration *) *)
(*            apply Hsat. *)
(*            right. *)
(*            apply Hin_nogood. *)
(*     + (* If the next step is a nogood, do the same but use RUP correctness this time *) *)
(*       apply IH with (inferences := nil) (nogoods := fact :: nogoods). *)
(*       * (* The proof tail is valid *) *)
(*         destruct (validate_kb csp tail_steps c nil (fact :: nogoods)) ; try easy. *)
(*         simpl. *)
(*         rewrite if_else_rewrite in Hvalid. *)
(*         contradiction. *)
(*       * (* Any feasible solution satisfies the KB. *) *)
(*         simpl. *)
(*         intros sol Hsat_sol f. *)
(*         specialize (Hsat sol Hsat_sol f) as Hsat_f. *)
(*         intros Hin. *)
(*         destruct Hin as [Hcontra | [Heq | Hin_nogood]] ; try contradiction. *)
(*         -- (* Show that the newly added nogood is satisfied by any feasible solution *)
(*               since it is derived by RUP from the KB facts. *) *)
(*            destruct (rup database (map atomic_not fact)) eqn:Erup. *)
(*            ++ apply Is_true_eq_left, valid_rup_on_negation in Erup. *)
(*               unfold is_valid_nogood in Erup. *)
(*               rewrite Heq in Erup. *)
(*               apply Erup. *)
(*               unfold satisfies_all_nogoods. *)
(*               apply Is_true_eq_left, forallb_forall. *)
(*               intros db Hdb_in. *)
(*               apply Is_true_eq_true, Hsat ; try easy. *)
(*               rewrite if_else_false in Hvalid. *)
(*               apply andb_prop_elim in Hvalid. *)
(*               destruct Hvalid as [_ Hforall]. *)
(*               rewrite andb_true_r in Hforall. *)
(*               apply Is_true_eq_true in Hforall. *)
(*               rewrite forallb_forall in Hforall. *)
(*               specialize (Hforall db Hdb_in). *)
(*               apply orb_prop in Hforall. *)
(*               destruct Hforall as [Hforall | Hforall] ; *)
(*               apply existsb_exists in Hforall ; *)
(*               destruct Hforall as [db_ex [Hxin Hxeqb]] ; *)
(*               apply Is_true_eq_left, Nogood.eqb_eq in Hxeqb ; *)
(*               rewrite <- Hxeqb in Hxin. *)
(*               ** right. *)
(*                  apply Hxin. *)
(*               ** left. *)
(*                  apply Hxin. *)
(*            ++ (* No need to handle inferences, as there will be none *) *)
(*               rewrite andb_false_r in Hvalid. *)
(*               contradiction. *)
(*         -- (* All the other nogoods are copied *) *)
(*            specialize (Hsat sol). *)
(*            apply Hsat ; try easy. *)
(*            right. *)
(*            apply Hin_nogood. *)
(* Qed. *)

(* Definition step_fact (step : Step) := *)
(*   match step with *)
(*   | inference fact _ _ => fact *)
(*   | nogood fact _ => fact *)
(*   end. *)

(* Lemma soundness : forall (csp : ConstraintProblem) (p : Proof) (sol : string -> Z), *)
(*   Is_true (validate csp p) -> (forall ix stage, In (ix, stage) p -> inference_valid ) *)

(*   conclusion_holds csp (conclusion p). *)
(* Proof. *)
(*   unfold validate. *)
(*   intros csp p Hvalid. *)
(*   apply soundness_with_kb with (s := steps p) (c := conclusion p) (nogoods := nil) (inferences := nil). *)
(*   + apply Hvalid. *)
(*   + simpl. *)
(*     intros sol Hsat f Hcontra. *)
(*     exfalso. *)
(*     destruct Hcontra ; contradiction. *)
(* Qed. *)

(* Lemma completeness : forall (csp : ConstraintProblem) (c : Conclusion), *)
(*   conclusion_holds csp c -> exists (p : Proof), Is_true (validate csp p). *)
(* Proof. *)
(* Admitted. *)

(* Theorem correctness : forall (csp : ConstraintProblem) (c : Conclusion), *)
(*   conclusion_holds csp c <-> exists (p : Proof), Is_true (validate csp p). *)
(* Proof. *)
(*   split. *)
(*   - intros Hconcl. *)
(*     apply completeness with (c := c), Hconcl. *)
(*   - intros Hexist. *)
(*     destruct Hexist as [p Hval]. *)
(*     specialize (soundness csp p Hval). *)
(*     unfold conclusion_holds. *)
(*     intros Hproof_concl. *)
(*     (* TODO This proof requires a more careful wording for optimality conclusions *) *)
(*     destruct (conclusion p) eqn:Eproof ; *)
(*     destruct c eqn:Ec. *)
(*     apply Hproof_concl. *)
(* Qed. *)
