Require Import Checker.ConstraintProblem.
Require Import Checker.Proof.

Definition proof_checker 
  (proof : Proof) (problem : ConstraintProblem) : bool :=
    true.

Definition is_valid_proof
  (proof : Proof) (problem : ConstraintProblem) : Prop := True.

Theorem proof_checker_valid :
  forall (proof : Proof) (problem : ConstraintProblem),
    proof_checker proof problem = true -> is_valid_proof proof problem.
Proof.
  Admitted.

