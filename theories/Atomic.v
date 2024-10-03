Require Import ZArith.
Open Scope Z_scope.
Require Import Checker.Variable.
Require Import List.
Import ListNotations.

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

Definition atomic_not (x : Atomic) :=
  match comparator x with
  | less_equal => {|
    var := var x ;
    comparator := greater_equal ;
    value := value x + 1
  |}
  | greater_equal =>  {|
    var := var x ;
    comparator := less_equal ;
    value := value x - 1
  |}  
  | not_equal => {|
    var := var x ;
    comparator := equal ;
    value := value x
  |}
  | equal => {|
    var := var x ;
    comparator := not_equal ;
    value := value x
  |}
  end.

Definition test_atomic (x : Atomic) (v : Z) :=
  match comparator x with 
  | less_equal => v <=? value x
  | greater_equal => v >=? value x
  | not_equal => negb (v =? value x)
  | equal => v =? value x
  end.

Theorem gt_succ : forall (n m : Z), n + 1 <= m <-> n < m.
Proof.
  intros.
  split.
  - intros Hp1.
    apply Zle_lt_succ in Hp1.
    rewrite Z.add_1_r in Hp1.
    apply Z.succ_lt_mono in Hp1.
    apply Hp1.
  - intros Hnm.
    rewrite Z.add_1_r.
    apply Zlt_le_succ, Hnm.
Qed.



Theorem atomic_not_involution : forall (x : Atomic) (v : Z),
  test_atomic (atomic_not x) v = negb (test_atomic x v).
Proof.
  intros.
  unfold test_atomic, atomic_not.
  remember (value x).
  destruct (comparator x) eqn:E ; unfold comparator, value.
  - rewrite <- Z.ltb_antisym.
    specialize (Z.geb_spec v (z + 1)) as bound_ge.
    specialize (Z.ltb_spec z v) as bound_lt.
    destruct (bound_lt, bound_ge) as ([b_lt|b_lt], [b_ge|b_ge]).
    + reflexivity.
    + exfalso.
      apply gt_succ in b_lt.
      assert (contra: z + 1 < z + 1). {
        apply Z.le_lt_trans with (m := v).
        - apply b_lt.
        - apply b_ge.
      }
      apply Z.lt_irrefl in contra.
      apply contra.
    + exfalso.
      apply gt_succ in b_ge.
      assert (contra: v < v). {
        apply Z.le_lt_trans with (m := z).
        - apply b_lt.
        - apply b_ge.
      }
      apply Z.lt_irrefl in contra.
      apply contra.
    + reflexivity.
  - rewrite Z.geb_leb, <- Z.ltb_antisym.
    apply Bool.eq_bool_prop_intro.
    split ; intros ; apply Bool.Is_true_eq_true in H ; apply Bool.Is_true_eq_left.
    + apply Z.leb_le in H.
      apply Z.ltb_lt.
      apply gt_succ, Z.le_add_le_sub_r, H.
    + apply Z.ltb_lt in H.
      apply Z.leb_le.
      apply gt_succ, Z.le_add_le_sub_r in H.
      apply H.
  - rewrite Bool.negb_involutive.
    reflexivity.
  - reflexivity.
Qed.
