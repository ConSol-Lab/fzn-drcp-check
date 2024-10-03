Require Import Checker.Variable.
Require Import Checker.Atomic.
Require Import Checker.Linear.
Require Import Checker.Nogood.
Require Import ZArith.
Require Import List.
Open Scope Z_scope.

Inductive Constraint :=
  | linear_leq (constraint : LinearConstraint)
  | nogood (atomics : list Atomic).

Record ConstraintProblem := 
  {
    variables : list Var;
    constraints : list Constraint;
  }.

Definition satisfies_constraint (c : Constraint) (sol : Assignment) :=
  match c with
  | linear_leq lin => satisfies_linear lin sol
  | nogood atomics =>
      match satisfies_nogood atomics sol with
      | Some val => val
      | None => false
      end
  end.
