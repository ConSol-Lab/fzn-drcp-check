Require Import Checker.Variable.
Require Import Checker.Atomic.
Require Import ZArith.
Require Import List.
Open Scope Z_scope.

Fixpoint satisfies_nogood (x : list Atomic) (sol : Assignment) :=
  match x with
  | nil => false
  | a :: xs =>
      let val := (find_value sol) (var a) in
      if test_atomic a val
      then true
      else satisfies_nogood xs sol
  end.

