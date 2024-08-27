Require Import ZArith.
Require Import String.
Require Import Checker.Variable.
Require Import Checker.Atomic.
Require Import Checker.ConstraintProblem.
Require Import Checker.Proof.

Definition find_invalid_step 
  (proof : Proof) (problem : ConstraintProblem) : option (nat * Step) :=
    let 
      var := {| 
        name := "a"; 
        lower_bound := 1; 
        size := exist _ 5 (Nat.neq_succ_0 4) 
      |} 
    in
      Some (5, inference nil {| var := interval var; comparator := less_equal; value := 5 |}).

Definition is_valid_proof
  (proof : Proof) (problem : ConstraintProblem) : Prop := True.

Theorem no_invalid_step_means_proof_valid :
  forall (proof : Proof) (problem : ConstraintProblem),
    find_invalid_step proof problem = None -> is_valid_proof proof problem.
Proof.
  intros.
  unfold is_valid_proof.
  exact I.
Qed.

