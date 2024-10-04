Require Import Bool.
Require Import List.
Require Import String.
Require Import ZArith.

Record IntervalVariable := 
  {
    name : string;
    lower_bound : Z;
    size: nat;
    upper_bound : Z := lower_bound + Z.of_nat size
  }.

Compute upper_bound {| name := "a"; lower_bound := 1; size := 5 |}.

Open Scope Z_scope.

Inductive Var :=
  | interval (var : IntervalVariable).

Definition eqb (lhs : Var) (rhs : Var) :=
  match (lhs, rhs) with
  | (interval lhs, interval rhs) => andb
      (andb (String.eqb (name lhs) (name rhs)) (Z.eqb (lower_bound lhs) (lower_bound rhs)))
      (Z.eqb (upper_bound lhs) (upper_bound rhs))
  end.

Theorem eqb_eq : forall (a b : Var), Is_true (eqb a b) <-> a = b.
Proof.
  intros a b.
  unfold eqb.
  destruct a as [[a]], b as [[b]].
  split.
  - intros Heq.
    unfold upper_bound in Heq.
    simpl in Heq.
    fold upper_bound0 in Heq.
    fold upper_bound1 in Heq.
    apply Is_true_eq_true, andb_prop in Heq.
    destruct Heq as [Heq Hub].
    apply andb_prop in Heq.
    destruct Heq as [Hname Hlb].
    apply String.eqb_eq in Hname.
    apply Z.eqb_eq in Hlb.
    apply Z.eqb_eq in Hub.
    f_equal.
    f_equal.
    + apply Hname.
    + apply Hlb.
    + unfold upper_bound0, upper_bound1 in Hub.
      rewrite Hlb in Hub.
      apply Z.add_reg_l, Nat2Z.inj in Hub.
      apply Hub.
  - intros Heq.
    inversion Heq.
    unfold upper_bound.
    apply Is_true_eq_left.
    simpl.
    apply andb_true_intro.
    split.
    apply andb_true_intro.
    split.
    + apply String.eqb_eq. reflexivity.
    + apply Z.eqb_eq. reflexivity.
    + apply Z.eqb_eq. reflexivity.
Qed.

Theorem eqb_symm : forall (a b : Var), eqb a b = eqb b a.
Proof.
  intros a b.
  unfold eqb.
  destruct a as [a],  b as [b].
  rewrite String.eqb_sym, Z.eqb_sym.
  rewrite Z.eqb_sym with (x := upper_bound b) (y := upper_bound a).
  reflexivity.
Qed.

Theorem eqb_trans : forall (a b c : Var), Is_true (eqb a b) -> Is_true(eqb b c) -> Is_true(eqb a c).
Proof.
  unfold eqb.
  intros a b c Hab Hbc.
  destruct a as [a], b as [b], c as [c].
  apply Is_true_eq_true, andb_prop in Hab.
  destruct Hab as [Hab Hab_ub].
  apply andb_prop in Hab.
  destruct Hab as [Hab_name Hab_lb].
  apply Is_true_eq_true, andb_prop in Hbc.
  destruct Hbc as [Hbc Hbc_ub].
  apply andb_prop in Hbc.
  destruct Hbc as [Hbc_name Hbc_lb].
  apply Is_true_eq_left, andb_true_intro. split.
  apply andb_true_intro. split.
  - apply String.eqb_eq in Hab_name.
    apply String.eqb_eq in Hbc_name.
    apply String.eqb_eq.
    rewrite Hab_name.
    apply Hbc_name.
  - apply Z.eqb_eq in Hab_lb.
    apply Z.eqb_eq in Hbc_lb.
    apply Z.eqb_eq.
    rewrite Hab_lb.
    apply Hbc_lb.
  - apply Z.eqb_eq in Hab_ub.
    apply Z.eqb_eq in Hbc_ub.
    apply Z.eqb_eq.
    rewrite Hab_ub.
    apply Hbc_ub.
Qed.


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

Record Assignment := {
  find_value : Var -> Z ;
  consistency_proof : forall (v : Var), Is_true (is_in v (find_value v))
}.

