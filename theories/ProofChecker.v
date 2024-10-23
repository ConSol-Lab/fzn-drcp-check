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
  | rup_inf db => rup db inference
  | linear constraint => linear_checker inference constraint
  end.

(* TODO How to implement the conclusion validator? *)
Definition validate_conclusion
  (proof_conclusion : Conclusion) (problem : ConstraintProblem) := false.
  (* let target := match proof_conclusion with *)
  (* | unsat => nil *)
  (* | optimal bound => bound :: nil *)
  (* end in *)
  (* existsb (fun cons => Constraint.eqb cons (nogood target)) (constraints problem). *)

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
        let problem_append :=
        {|
          variables := variables problem ;
          constraints := (nogood (clausal_form step)) :: (constraints problem)
        |} in
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
  intros proof problem Eunsat Evalid sol cons Hin Hsat.
  exfalso.
  generalize dependent sol.
  rewrite Eunsat in Evalid.
  generalize dependent problem.
  induction (steps proof) as [|proof_head proof_tail IHproof].
  - (* TODO No implementation of conclusion validation yet, skipping this part for now *)
    admit.
  - intros.
    simpl in Evalid.
    destruct (validate_step proof_head problem) eqn:Evalid_step ; simpl in Evalid ; inversion Evalid as [Etail].
    unfold inc_step_index in Etail.
    remember 
    {|
      variables := variables problem ;
      constraints := (nogood (clausal_form proof_head)) :: (constraints problem)
    |} as problem_append eqn:Eappend.
    destruct (validate_unpacked proof_tail unsat problem_append) eqn:Evalid_unpacked ; inversion Etail.
    apply IHproof with (problem := problem_append) (sol := sol).
    (* TODO This proof has to be much more elaborate, but everything short-circuits to false anyway *)
    + apply Evalid_unpacked.
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
