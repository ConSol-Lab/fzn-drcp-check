(* Require Import Checker.Variable. *)
Require Import Checker.Atomic.
(* Require Import Checker.Linear. *)
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

Inductive Constraint :=
  (* | linear_leq (constraint : LinearConstraint) *)
  | cumulative_c (constraint : Cumulative.CumulativeConstraint)
  | fact_c (constraint : Deduction.Inference)
  (* | alldifferent_c (constraint : AllDifferent.AllDifferentConstraint) *)
  .

Definition affected_variables (c : Constraint) :=
  match c with
  (* | linear_leq lin => *)
  (*     map (fun x => *)
  (*       match x with *)
(*       | (_, v) => v *)
  (*       end *)
  (*     ) (terms lin) *)
  | cumulative_c c => 
      map (Cumulative.def_x) (Cumulative.activities c)
  | fact_c c =>
      let unpack_var := fun (x : DomainVar.BoundAtomic) =>
        match x with
        | (v, _) => v
        end
      in
      let lits :=
        match (Deduction.i_consequent c) with
        | Some x => x :: (Deduction.i_premises c)
        | None => (Deduction.i_premises c)
        end
      in
      map unpack_var lits
  (* | alldifferent_c c => *)
  (*   AllDifferent.get_vars c *)
  end.

Definition satisfies_constraint (c : Constraint) (sol : string -> Z) :=
  match c with
  (* | linear_leq lin => satisfies_linear lin sol *)
  | cumulative_c c => Is_true (Cumulative.cumulative_decide c sol)
  | fact_c c => Deduction.inference_valid sol c
  (* | alldifferent_c c => AllDifferent.alldifferent_decide c sol *)
  end.

Definition ConstraintMap := nmap.t Constraint.

Record ConstraintProblem := 
  {
    csp_variables : list string;
    csp_constraints : ConstraintMap;
  }.

Definition add (index : N) (fact : Deduction.Inference) (csp : ConstraintProblem) : ConstraintProblem :=
  {|
    csp_variables := csp.(csp_variables) ;
    csp_constraints := nmap.add index (fact_c fact) (csp.(csp_constraints))
  |}.

Definition lookup (csp : ConstraintProblem) (index : N) : option Constraint :=
  nmap.find index csp.(csp_constraints).

Definition satisfies_problem (csp : ConstraintProblem) (sol : string -> Z) :=
  forall index c, nmap.MapsTo index c csp.(csp_constraints) -> satisfies_constraint c sol.
  
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
  (forall sol, satisfies_problem csp sol -> Deduction.inference_valid sol fact) ->
  (forall sol, satisfies_problem (add index fact csp) sol -> Deduction.inference_valid sol conclusion) ->
  (forall sol, satisfies_problem csp sol -> Deduction.inference_valid sol conclusion).
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
