Require Import Checker.Variable.
Require Import Checker.Atomic.
Require Import ZArith.
Require Import List.
Require Import Bool.
Open Scope Z_scope.

Definition Clause := list Atomic.

Fixpoint satisfies_nogood (x : Clause) (sol : Assignment) :=
  match x with
  | nil => false
  | a :: xs =>
      let val := (find_value sol) (var a) in
      if test_atomic a val
      then true
      else satisfies_nogood xs sol
  end.

Definition is_valid_nogood
  (inference : Clause) (clause_seq : list Clause) : Prop := 
  forall (sol : Assignment) (clause : Clause),
  In clause clause_seq ->
  Is_true (satisfies_nogood clause sol) ->
  Is_true (satisfies_nogood inference sol).

Fixpoint rup 
  (inference : Clause)
  (clause_seq : list Clause)
  (true_literals : list Atomic) : bool :=
  if contradiction true_literals then true
  else
  match clause_seq with
  | nil => false
  | clause :: remaining =>
      match find_unit clause true_literals with
      | Some x => rup inference remaining (true_literals :: x)
      | None => false
      end
  end.
