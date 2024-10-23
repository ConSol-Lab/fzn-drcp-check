Require Import ZArith.
Require Import Nat.
Require Import String.
Require Import Bool.
Require Import List.
Require Import Checker.Variable.
Require Import Checker.Atomic.
Require Import Checker.Nogood.
Require Import Checker.ConstraintProblem.
Require Import Checker.Proof.
Require Import Checker.Linear.

Inductive CheckerVerdict :=
  | valid
  | bad_step (step_index : nat) (step_def : Step)
  | bad_conclusion.

Definition inc_step_index (verdict : CheckerVerdict) :=
  match verdict with 
  | bad_step step_index step_def => bad_step (step_index + 1) step_def
  | _ => verdict
end.

Definition validate_step
  (step : Step) (problem : ConstraintProblem) :=
  let inference := clausal_form step in
  match (inference_rule step) with
  | rup_inf db => rup db (map atomic_not inference)
  | linear constraint => linear_checker inference constraint
  end.

(* TODO How to implement the conclusion validator? *)
Definition validate_conclusion
  (proof_conclusion : Conclusion) (problem : ConstraintProblem) := true.
  (* let target := match proof_conclusion with *)
  (* | unsat => nil *)
  (* | optimal bound => bound :: nil *)
  (* end in *)
  (* existsb (fun cons => Constraint.eqb cons (nogood target)) (constraints problem). *)

Definition append_inference (problem : ConstraintProblem) (step : Step) : ConstraintProblem :=
  {|
    variables := variables problem ;
    constraints := (nogood (clausal_form step)) :: (constraints problem)
  |}.

Theorem append_soundness :
  forall (problem : ConstraintProblem) (step : Step) (sol : Assignment),
  Is_true (validate_step step problem) -> 
  (
    forall (constraint : Constraint), 
    In constraint (constraints problem) ->
    Is_true (satisfies_constraint constraint sol)
  ) -> (
    forall (constraint : Constraint), 
    In constraint (constraints (append_inference problem step)) ->
    Is_true (satisfies_constraint constraint sol)
  ).
Proof.
  intros problem step sol Hval Hsat base_constraint Hin.
  unfold append_inference in Hin.
  simpl in Hin.
  destruct Hin as [Enogood|Hin] ; try apply Hsat, Hin.
  rewrite <- Enogood.
  unfold satisfies_constraint.
  unfold validate_step in Hval.
  destruct (inference_rule step) eqn:Einference.
  + apply Is_true_eq_true, linear_inference_checker_correct in Hval.
    unfold is_valid_linear_inference in Hval.
    apply Hval.
    (* TODO Show that the listed constraint can be found in the original model *)
    admit.
  + apply Is_true_eq_true in Hval.
    specialize valid_rup_on_negation with
      (clause_seq := database) (nogood := clausal_form step).
    unfold is_valid_nogood.
    intros Hrup.
    apply Hrup.
    - apply Is_true_eq_left, Hval.
    - (* TODO Show that all database clauses can be found in the model *)
      admit.
Admitted.

Fixpoint validate_unpacked
  (proof_steps : list Step) (proof_conclusion : Conclusion)
  (problem : ConstraintProblem) : CheckerVerdict :=
    match proof_steps with
    | nil =>
        if validate_conclusion proof_conclusion problem
        then valid
        else bad_conclusion
    | step :: tail =>
        if validate_step step problem
        then
        let problem_append := append_inference problem step in
        let tail_verdict := validate_unpacked tail proof_conclusion problem_append in
        inc_step_index tail_verdict
        else bad_step 0 step
    end.

Definition validate 
  (proof : Proof) (problem : ConstraintProblem) : CheckerVerdict :=
    validate_unpacked (steps proof) (conclusion proof) problem.
  
Definition is_valid_conclusion
  (proof_conclusion : Conclusion) (problem : ConstraintProblem) : Prop :=
  forall (sol : Assignment) (cons : Constraint),
  In cons (constraints problem) ->
  Is_true (satisfies_constraint cons sol) ->
  Is_true (satisfies_conclusion proof_conclusion sol).

Lemma unsat_no_invalid_step_implies_valid :
  forall (proof : Proof) (problem : ConstraintProblem),
    conclusion proof = unsat ->
    validate proof problem = valid ->
    is_valid_conclusion (conclusion proof) problem.
Proof.
  unfold is_valid_conclusion, satisfies_conclusion, validate.
  intros proof problem Eunsat Evalid sol con Hin Hsat.
  generalize dependent sol.
  generalize dependent con.
  rewrite Eunsat in Evalid.
  generalize dependent problem.
  induction (steps proof) as [|proof_head proof_tail IHproof].
  - (* TODO No implementation of conclusion validation yet, skipping this part for now *)
    admit.
  - intros.
    simpl in Evalid.
    destruct (validate_step proof_head problem) eqn:Evalid_step_packed ;
    simpl in Evalid ; inversion Evalid as [Etail].
    unfold inc_step_index in Etail.
    remember 
    {|
      variables := variables problem ;
      constraints := (nogood (clausal_form proof_head)) :: (constraints problem)
    |} as problem_append eqn:Eappend.
    destruct (validate_unpacked proof_tail unsat problem_append) eqn:Evalid_step ; inversion Etail.
    apply IHproof with (problem := problem_append) (sol := sol) (con := con).
    + apply Evalid_step.
    + rewrite Eappend.
      simpl.
      right.
      apply Hin.
    + apply Hsat.
Admitted.

Lemma bound_validate_append :
  forall (proof : Proof) (problem : ConstraintProblem) (bound : Atomic),
    conclusion proof = optimal bound ->
    validate proof problem = valid ->
    is_valid_conclusion (conclusion proof) problem.
Proof.
  unfold is_valid_conclusion, satisfies_conclusion, validate.
  intros proof problem bound Ebound Evalid sol con Hin Hsat.
  rewrite Ebound.
  generalize dependent sol.
  generalize dependent con.
  rewrite Ebound in Evalid.
  generalize dependent problem.
  induction (steps proof) as [|proof_head proof_tail IHproof].
  - (* TODO No implementation of conclusion validation yet, skipping this part for now *)
    admit.
  - intros.
    simpl in Evalid.
    destruct (validate_step proof_head problem) eqn:Evalid_step_packed ;
    simpl in Evalid ; inversion Evalid as [Etail].
    unfold inc_step_index in Etail.
    remember 
    {|
      variables := variables problem ;
      constraints := (nogood (clausal_form proof_head)) :: (constraints problem)
    |} as problem_append eqn:Eappend.
    destruct (validate_unpacked proof_tail (optimal bound) problem_append) eqn:Evalid_step ; inversion Etail.
    apply IHproof with (problem := problem_append) (sol := sol) (con := con).
    + apply Evalid_step.
    + rewrite Eappend.
      simpl.
      right.
      apply Hin.
    + apply Hsat.
Admitted.

Theorem no_invalid_step_implies_valid :
  forall (proof : Proof) (problem : ConstraintProblem),
    validate proof problem = valid ->
    is_valid_conclusion (conclusion proof) problem.
Proof.
  intros.
  destruct (conclusion proof) eqn:Econcl ; rewrite <- Econcl.
  + apply unsat_no_invalid_step_implies_valid.
    - apply Econcl.
    - apply H.
  + apply bound_validate_append with (bound := bound).
    - apply Econcl.
    - apply H.
Qed.
