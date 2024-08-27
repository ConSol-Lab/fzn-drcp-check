Require Import ZArith.
Require Import Checker.Variable.

Inductive atomic_comparator :=
  | less_equal
  | greater_equal
  | not_equal
  | equal.

Record atomic :=
  {
    var : variable;
    comparator : atomic_comparator;
    value : Z;
  }.
