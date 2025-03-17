Require Import Coq.Strings.String.
Require Import Checker.Domain.
Require Import Checker.Variable.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Checker.AllDifferent.
Require Import Checker.Atomic.
Require Import Checker.Nogood.

Definition alldifferent_checker (inference : list Atomic) (constraint : AllDifferentConstraint) : bool :=
  match inference with
  | nil => true && false
  | _ => true
  end
.

Lemma checker_negated_is_conflict :
  forall fact sol constr,
  alldifferent_checker fact constr = true ->
  inference_negated fact sol -> 
  alldifferent_decide constr sol = false.
Proof.
Admitted.

Lemma valid_if_invalid_checked_is_conflict :
  forall satisfied checked fact_valid,
  (checked = true
  -> fact_valid = false
  -> satisfied = false)
    ->
  (satisfied = true
  -> checked = true
  -> fact_valid = true).
Proof.
  intros satisfied checked fact_valid H.
  intros Hsat Hchecked.
  destruct fact_valid.
  - reflexivity.
  - rewrite <- Hsat. symmetry.
    apply H; easy.
Qed.

Lemma alldifferent_checker_valid :
  forall fact sol constr,
  alldifferent_decide constr sol = true ->
  alldifferent_checker fact constr = true ->
  satisfies_nogood fact sol = true.
Proof.
  intros fact sol constr.
  apply valid_if_invalid_checked_is_conflict.
  intros Hchecked Hfact.
  apply alldifferent_checker_valid.