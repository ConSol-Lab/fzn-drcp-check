Require Import Bool.
Require Import List.
Require Import String.
Require Import ZArith.

Definition non_zero_Z := { n : nat | n <> 0 }.

Record IntervalVariable := 
  {
    name : string;
    lower_bound : Z;
    size: non_zero_Z;
    upper_bound : Z := lower_bound + Z.of_nat (proj1_sig size)
  }.

Compute upper_bound {| name := "a"; lower_bound := 1; size := exist _ 5 (Nat.neq_succ_0 4) |}.

Open Scope Z_scope.

Inductive Var :=
  | interval (var : IntervalVariable).

Definition eqb (lhs : Var) (rhs : Var) :=
  match (lhs, rhs) with
  | (interval lhs, interval rhs) => String.eqb (name lhs) (name rhs)
  end.

Definition var_lower_bound (x : Var) :=
  match x with
  | interval val => lower_bound val
  end.

Definition var_upper_bound (x : Var) :=
  match x with
  | interval val => upper_bound val
  end.

Definition is_in (x : Var) (val : Z) :=
  match x with
  | interval var => andb (lower_bound var <=? val) (val <=? upper_bound var)
  end.

Theorem is_in_implies_lower_bound : forall (x : Var) (val : Z),
  Is_true (is_in x val) -> val >= var_lower_bound x.
Proof.
  intros.
  destruct x.
  simpl.
  unfold is_in in H.
  apply andb_prop_elim in H.
  destruct H as [Hlb].
  apply Is_true_eq_true, Z.leb_le, Z.le_ge in Hlb.
  apply Hlb.
Qed.

Theorem is_in_implies_upper_bound : forall (x : Var) (val : Z),
  Is_true (is_in x val) -> val <= var_upper_bound x.
Proof.
  intros.
  destruct x.
  simpl.
  unfold is_in in H.
  apply andb_prop_elim in H.
  destruct H as [_ Hub].
  apply Is_true_eq_true, Z.leb_le in Hub.
  apply Hub.
Qed.

Record VariableAssignment := {
  variable : Var ;
  assigned : Z
}.

Definition consistent (x : VariableAssignment) := is_in (variable x) (assigned x).

Record Assignment := {
  mapping : list VariableAssignment ;
  consistency_prop : Is_true (forallb consistent mapping)
}.

Definition find_value (sol : Assignment) (var : Var) :=
  match find (fun x => eqb (variable x) var) (mapping sol) with
  | Some a => Some (assigned a)
  | None => None
  end.


