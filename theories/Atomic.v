Require Import ZArith.
Open Scope Z_scope.
Require Import List.
Require Import Bool.
Require Import Checker.Variable.
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


Theorem atomic_not_not : forall (a : Atomic), atomic_not (atomic_not a) = a.
Proof.
  intros.
  destruct (comparator a) eqn:Hcmp ;
  unfold atomic_not ;
  rewrite Hcmp ;
  simpl ;
  rewrite <- Hcmp ;
  destruct a ;
  simpl ;
  try reflexivity ;
  f_equal ;
  ring_simplify ;
  reflexivity.
Qed.


Theorem atomic_not_variable_eq : forall (atomic : Atomic),
  var atomic = var (atomic_not atomic).
Proof.
  intros.
  destruct (comparator atomic) eqn:Hcmp ;
  unfold atomic_not ;
  rewrite Hcmp ;
  reflexivity.
Qed.


Definition test_atomic (x : Atomic) (v : Z) :=
  match comparator x with 
  | less_equal => v <=? value x
  | greater_equal => v >=? value x
  | not_equal => negb (v =? value x)
  | equal => v =? value x
  end.


Definition test_atomic_assignment (atomic : Atomic) (sol : Assignment) :=
  test_atomic atomic ((find_value sol) (var atomic)).


Definition contradiction_binary (lhs : Atomic) (rhs : Atomic) : bool :=
  if eqb (var lhs) (var rhs) then
  let lhs_val := value lhs in
  let rhs_val := value rhs in
  match (comparator lhs), (comparator rhs) with
  | less_equal, greater_equal => lhs_val <? rhs_val
  | less_equal, equal => lhs_val <? rhs_val
  | greater_equal, less_equal => lhs_val >? rhs_val
  | greater_equal, equal => lhs_val >? rhs_val
  | equal, greater_equal => lhs_val <? rhs_val
  | equal, less_equal => lhs_val >? rhs_val
  | equal, equal => negb (lhs_val =? rhs_val)
  | equal, not_equal => lhs_val =? rhs_val
  | not_equal, equal => lhs_val =? rhs_val
  | _, _ => false
  end
  else false.


Lemma integer_cover : forall (x l r : Z), l < r -> ~(x <= l) \/ ~(x >= r).
Proof.
  intros.
  destruct (x <=? l) eqn:Ecmp ; simpl.
  - right.
    intros contra.
    apply Z.lt_irrefl with (x := r).
    apply Z.le_lt_trans with (m := l).
    + apply Z.le_trans with (m := x).
      * apply Z.ge_le, contra.
      * apply Z.leb_le in Ecmp.
        apply Ecmp.
    + apply H.
  - left.
    apply Z.leb_nle, Ecmp.
Qed.

Lemma binarize : forall (a b c : Z),
  ~(a <= b) \/ ~(a >= c) -> ~Is_true (a <=? b) \/ ~Is_true (a >=? c).
Proof.
  intros.
  destruct H.
  + left.
    apply negb_prop_elim, Is_true_eq_left, negb_true_iff, Z.leb_nle, H.
  + right.
    apply negb_prop_elim, Is_true_eq_left, negb_true_iff.
    rewrite Z.geb_leb.
    apply Z.leb_nle.
    unfold not.
    intros contra.
    apply Z.le_ge in contra.
    contradiction.
Qed.

Lemma weaken_equality_le : forall (a b : Z) (P : Prop),
  P \/ ~Is_true(a <=? b) -> P \/ ~Is_true(a =? b).
Proof.
  intros.
  destruct H.
  - left.
    exact H.
  - right.
    apply negb_prop_intro, Is_true_eq_true, negb_true_iff, Z.leb_gt in H.
    apply negb_prop_elim, Is_true_eq_left, negb_true_iff,
    Z.eqb_neq, not_eq_sym, Z.lt_neq, H.
Qed.

Lemma weaken_equality_ge : forall (a b : Z) (P : Prop),
  P \/ ~Is_true(a >=? b) -> P \/ ~Is_true(a =? b).
Proof.
  intros.
  destruct H.
  - left.
    exact H.
  - right.
    apply negb_prop_intro, Is_true_eq_true, negb_true_iff in H.
    rewrite Z.geb_leb in H.
    apply Z.leb_gt in H.
    apply negb_prop_elim, Is_true_eq_left, negb_true_iff,
    Z.eqb_neq, Z.lt_neq, H.
Qed.

Theorem contradiction_at_most_one :
  forall (x : Z) (lhs rhs : Atomic), 
  Is_true (contradiction_binary lhs rhs) ->
  ~Is_true (test_atomic lhs x) \/ ~Is_true (test_atomic rhs x).
Proof.
  unfold contradiction_binary, test_atomic.
  intros x lhs rhs.
  destruct (eqb (var lhs) (var rhs)) ; try contradiction.
  destruct (comparator lhs) ;
  destruct (comparator rhs) ;
  simpl ;
  intros ;
  try contradiction ;
  apply Is_true_eq_true in H ;
  try apply Z.ltb_lt in H ;
  try apply Z.gtb_gt in H ;
  try apply Z.eqb_eq in H .
  - apply binarize, integer_cover, H.
  - apply weaken_equality_ge, binarize, integer_cover, H.
  - apply or_comm, binarize, integer_cover, Z.gt_lt, H.
  - apply weaken_equality_le, or_comm, binarize, integer_cover, Z.gt_lt, H.
  - rewrite H.
    remember (value rhs) as y.
    destruct (x =? y) ; simpl .
    + left.
      intros contra.
      contradiction.
    + right.
      intros contra.
      contradiction.
  - apply or_comm, weaken_equality_ge, binarize, integer_cover, Z.gt_lt, H.
  - apply or_comm, weaken_equality_le, or_comm, binarize, integer_cover, H.
  - rewrite H.
    remember (value rhs) as y.
    destruct (x =? y) ; simpl.
    + right.
      intros contra.
      contradiction.
    + left.
      intros contra.
      contradiction.
  - destruct (x =? value lhs) eqn:Elhs ; simpl.
    + right.
      apply Z.eqb_eq in Elhs.
      apply negb_true_iff in H.
      rewrite Elhs, H.
      simpl.
      intros contra.
      contradiction.
    + left.
      intros contra.
      contradiction.
Qed.



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
