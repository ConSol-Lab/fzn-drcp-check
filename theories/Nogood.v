Require Import Checker.Variable.
Require Import Checker.Atomic.
Require Import ZArith.
Require Import List.
Open Scope Z_scope.

Fixpoint satisfies_nogood (x : list Atomic) (sol : Assignment) :=
  match x with
  | nil => false
  | a :: xs =>
      let maybe_value := find_value sol (var a) in
      match maybe_value with
      | Some v => if test_atomic a v then true else satisfies_nogood xs sol
      | None => false
      end
  end.

