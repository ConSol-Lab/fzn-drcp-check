Require Checker.Spec.
Import Spec.ProofFacts.
Import Spec.ConstraintDefinitions.

Definition alldifferent_checker (fact : ProofFact) (constraint : AlldifferentConstraint) : bool :=
  match constraint.(diff_variables) with
  | nil => false
  | _ => false
  end.

Lemma checker_alldifferent :
  forall fact sol constr,
  Alldifferent constr sol
  -> alldifferent_checker fact constr = true
  -> fact_valid sol fact.
Proof.
Admitted.
