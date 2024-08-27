Require Import ZArith.
Require Import Checker.Variable.

Inductive AtomicComparator :=
  | less_equal
  | greater_equal
  | not_equal
  | equal.

Record Atomic :=
  {
    var : Var;
    comparator : AtomicComparator;
    value : Z;
  }.
