Require Import ZArith.
Require Import Checker.Variable.
Require Import Checker.Inference.

Record LinearConstraint :=
  {
    terms : list (Z * variable);
    bound : Z;
  }.

Record LinearInference :=
  {
    premises : list (variable * Z); (* (variable, lower_bound) *)
    conclusion : (variable * Z);    (* (variable, upper_bound) *)
  }.

Definition linear_checker
  (inference : LinearInference) (constraint : LinearConstraint) : bool := 

  true.

Definition is_valid_linear_inference 
  (inference : LinearInference) (constraint : LinearConstraint) : Prop := True.

Theorem linear_inference_checker_correct : 
  forall (inference : LinearInference) (constraint : LinearConstraint),
    linear_checker inference constraint = true ->
    is_valid_linear_inference inference constraint.
Proof.
Admitted.

