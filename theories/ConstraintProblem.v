Require Import Checker.Variable.
Require Import Checker.Atomic.
Require Import Checker.Linear.
Require Checker.Cumulative.
Require Checker.AllDifferent.
Require Import Checker.Nogood.
Require Import ZArith.
Require Import Bool.
Require Import List.
Open Scope Z_scope.

Inductive Constraint :=
  | linear_leq (constraint : LinearConstraint)
  | cumulative_c (constraint : Cumulative.CumulativeConstraint)
  | alldifferent_c (constraint : AllDifferent.AllDifferentConstraint)
  .

Definition affected_variables (c : Constraint) :=
  match c with
  | linear_leq lin =>
      map (fun x =>
        match x with
        | (_, v) => v
        end
      ) (terms lin)
  | cumulative_c c => 
      map (fun x => 
        match x with
        | (v, _, _) => v
        end) (Cumulative.vs c)
  | alldifferent_c c =>
    AllDifferent.get_vars c
  end.

Record ConstraintProblem := 
  {
    variables : list Var;
    constraints : list Constraint;
  }.

Definition satisfies_constraint (c : Constraint) (sol : Assignment) :=
  match c with
  | linear_leq lin => satisfies_linear lin sol
  | cumulative_c c => Cumulative.cumulative_decide c sol
  | alldifferent_c c => AllDifferent.alldifferent_decide c sol
  end.

Definition satisfies_problem (csp : ConstraintProblem) (sol : Assignment) :=
  forallb (fun c => satisfies_constraint c sol) (constraints csp).
  