Require Import Checker.Variable.
Require Import Checker.Atomic.
Require Import Checker.Linear.
Require Import Checker.Nogood.
Require Import ZArith.
Require Import List.
Open Scope Z_scope.

Inductive Constraint :=
  | linear_leq (constraint : LinearConstraint).

Definition affected_variables (c : Constraint) :=
  match c with
  | linear_leq lin =>
      map (fun x =>
        match x with
        | (_, v) => v
        end
      ) (terms lin)
  end.

Record ConstraintProblem := 
  {
    variables : list Var;
    constraints : list Constraint;
  }.

Definition satisfies_constraint (c : Constraint) (sol : Assignment) :=
  match c with
  | linear_leq lin => satisfies_linear lin sol
  end.

Definition satisfies_problem (csp : ConstraintProblem) (sol : Assignment) :=
  forallb (fun c => satisfies_constraint c sol) (constraints csp).
