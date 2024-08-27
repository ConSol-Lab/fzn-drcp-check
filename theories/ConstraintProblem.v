Require Import Checker.Variable.
Require Import Checker.Atomic.
Require Import Checker.Linear.

Inductive Constraint :=
  | linear_leq (constraint : LinearConstraint)
  | nogood (atomics : list Atomic).

Record ConstraintProblem := 
  {
    variables : list Var;
    constraints : list Constraint;
  }.

