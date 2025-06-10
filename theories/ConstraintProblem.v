Require Import Checker.Atomic.
Require Checker.Linear.
Require Checker.Cumulative.
Require Checker.Deduction.
Require Checker.AllDifferent.
Require Import Checker.Nogood.
Require Import ZArith.
Require Import Bool.
Require Import List.
Require Import String.
Import Utility.Maps.
Open Scope Z_scope.
Require Import Spec.
Import Spec.ProofFacts.
Import Spec.ConstraintDefinitions.

Definition add (index : N) (fact : ProofFact) (csp : ConstraintProblem) : ConstraintProblem :=
  nmap.add index (fact_c fact) csp.

Definition lookup (csp : ConstraintProblem) (index : N) : option Constraint :=
  nmap.find index csp.

Lemma sat_csp_implies_sat_lookup : forall index csp sol c,
  lookup csp index = Some c ->
  satisfies_problem csp sol -> 
  satisfies_constraint c sol.
Proof.
  unfold satisfies_problem, lookup.
  intros.
  apply H0 with (index := index), nmap_prps.find_2, H.
Qed.

Lemma entailed_addition : forall csp fact index conclusion,
  (forall sol, satisfies_problem csp sol -> fact_valid sol fact) ->
  (forall sol, satisfies_problem (add index fact csp) sol -> fact_valid sol conclusion) ->
  (forall sol, satisfies_problem csp sol -> fact_valid sol conclusion).
Proof.
  intros csp fact index conclusion Hentail Hvalid_concl sol Hsat.
  apply Hvalid_concl.
  unfold satisfies_problem.
  intros index' c' Hmaps.
  simpl in Hmaps.
  apply nmap_prps.add_mapsto_iff in Hmaps.
  destruct (index =? index')%N eqn:Esame.
  - apply N.eqb_eq in Esame.
    rewrite <- Esame in Hmaps.
    destruct Hmaps ; destruct H ; try contradiction.
    rewrite <- H0.
    simpl.
    apply Hentail.
    exact Hsat.
  - apply N.eqb_neq in Esame.
    destruct Hmaps ; destruct H ; try contradiction.
    unfold satisfies_problem in Hsat.
    apply Hsat with (index := index').
    exact H0.
Qed.
