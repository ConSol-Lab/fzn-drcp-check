Require Import Coq.Logic.FinFun.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import String.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Arith.PeanoNat.
Require Import Bool.

Require Import Checker.Nogood.
Require Import Checker.Cumulative.
Require Checker.CumulativeUtil.
Import CumulativeUtil.ResourceSum.
Require Import Checker.Utility.
Import ListEx.
Require Import Lia.
Require Import Checker.Variable.
Require Checker.Utility.
Require Coq.MSets.MSetAVL.
Require Coq.MSets.MSetProperties.
Require Coq.Structures.OrdersEx.

(* ################################### *)
(* ####### MSet instantiations ####### *)

Module sstr := MSetAVL.Make OrdersEx.String_as_OT.
Module sint := MSetAVL.Make OrdersEx.Z_as_OT.
Module Z_String_as_OT := OrdersEx.PairOrderedType OrdersEx.Z_as_OT OrdersEx.String_as_OT.
Module sintstr := MSetAVL.Make Z_String_as_OT.
Module sstr_prps := MSetProperties.Properties sstr.
Module sint_prps := MSetProperties.Properties sint.
Module sintstr_prps := MSetProperties.Properties sintstr.

Inductive AtomicComparator :=
  | less_equal
  | greater_equal
  | equal
  | not_equal.

Record Atomic := {
    atm_cmp : AtomicComparator;
    atm_val : Z
}.

(* This is much more efficient than using filter twice. *)
Definition in_interval (s : sint.t) (from : Z) (to : Z) : sint.t :=
  let t := sint.this s in
  let split_1 := sint.Raw.t_right (sint.Raw.split (from - 1) t) in
  let ok_1 := sint.Raw.split_ok2 (from - 1) (sint.is_ok s) in
  let split_2 := sint.Raw.t_left (sint.Raw.split (to + 1) split_1) in
  let ok_2 := sint.Raw.split_ok1 (to + 1) ok_1 in
  {| sint.this := split_2; sint.is_ok := ok_2 |}.

Definition split_above (s : sint.t) (from : Z) : sint.t :=
  let result := sint.Raw.t_right (sint.Raw.split (from - 1) (sint.this s)) in
  let result_ok := sint.Raw.split_ok2 (from - 1) (sint.is_ok s) in
  {| sint.this := result; sint.is_ok := result_ok |}.

Definition split_below (s : sint.t) (to : Z) : sint.t :=
  let result := sint.Raw.t_left (sint.Raw.split (to + 1) (sint.this s)) in
  let result_ok := sint.Raw.split_ok1 (to + 1) (sint.is_ok s) in
  {| sint.this := result; sint.is_ok := result_ok |}.

Lemma split_below_spec :
  forall s ub,
    forall n,
      sint.In n (split_below s ub)
        <->
      sint.In n s /\ n <= ub.
Proof.
  specialize sint.Raw.split_spec1 as Hsplit.
  intros s ub n.
  unfold split_below.
  unfold sint.In; unfold sint.Raw.In; simpl.
  rewrite Hsplit.
  - clear. repeat rewrite Z.compare_lt_iff.
    repeat split; destruct H as [Hl Hr];
    try assumption; try lia.
  - exact (sint.is_ok s).
Qed.

Lemma split_above_spec :
  forall s lb,
    forall n,
      sint.In n (split_above s lb)
        <->
      sint.In n s /\ lb <= n.
Proof.
  specialize sint.Raw.split_spec2 as Hsplit.
  intros s lb n.
  unfold split_above.
  unfold sint.In; unfold sint.Raw.In; simpl.
  rewrite Hsplit.
  - clear. repeat rewrite Z.compare_lt_iff.
    repeat split; destruct H as [Hl Hr];
    try assumption; try lia.
  - exact (sint.is_ok s).
Qed.

Lemma in_interval_spec :
  forall s lb ub,
    forall n, 
      sint.In n (in_interval s lb ub) 
        <->
      sint.In n s /\ lb <= n <= ub.
Proof.
  specialize sint.Raw.split_spec2 as Hsplit_r.
  specialize sint.Raw.split_spec1 as Hsplit_l.
  intros s lb ub n.
  unfold in_interval.
  unfold sint.In; unfold sint.Raw.In; simpl.
  specialize (Hsplit_r (sint.this s) (lb-1) n (sint.is_ok s)).
  specialize (sint.Raw.split_ok2 (lb - 1) (sint.is_ok s)) as Hok_1.
  remember (sint.Raw.t_right (sint.Raw.split (lb-1) (sint.this s))) as split_1.
  specialize (Hsplit_l split_1 (ub+1) n Hok_1).
  rewrite Hsplit_l. rewrite Hsplit_r.
  repeat rewrite Z.compare_lt_iff.
  split.
  - clear. intros H.
    destruct H as [[Hin Hl] Hr].
    split.
    + exact Hin.
    + lia.
  - clear. intros H.
    destruct H as [Hin [Hl Hr]].
    repeat split.
    + exact Hin.
    + lia.
    + lia.
Qed.  

Definition check_bound (lb : Z) (ub : Z) (holes : sint.t) := 
  if lb <=? ub
    then Some (lb, ub, holes)
    else None.

Definition option_bound (x : Z) (bound : option Z) (P : Z -> Prop) :=
  match bound with
  | None => True
  | Some bound => P bound
  end.

Definition current_bound_holds (x : Z) (lb : option Z) (ub : option Z) :=
  option_bound x lb (Z.ge x)
    /\
  option_bound x ub (Z.le x). 

Definition is_not_holes (x : Z) (holes : sint.t) :=
  forall n,
    sint.In n holes
      ->
    x <> n.

Definition option_min (bound : option Z) (new : Z) :=
  match bound with
  | Some bound => Some (Z.min bound new)
  | None => Some new
  end.

Definition option_max (bound : option Z) (new : Z) :=
  match bound with
  | Some bound => Some (Z.max bound new)
  | None => Some new
  end.

Definition check_current_bound (lb : option Z) (ub : option Z) (holes : sint.t) :=
  match lb with
  | None => Some (lb, ub, holes)
  | Some lb_val =>
    match ub with
    | None => Some (lb, ub, holes)
    | Some ub_val =>
      if lb_val <=? ub_val
        then Some (lb, ub, holes)
        else None
    end
  end.

Definition is_in_bounds (lb : option Z) (ub : option Z) (x : Z) :=
  match lb with
  | None => true
  | Some lb => lb <=? x
  end
    &&
  match ub with
  | None => true
  | Some ub => x <=? ub
  end.

Definition apply_atomic (atomic : Atomic) (lb : option Z) (ub : option Z) (holes : sint.t) :=
  match atomic.(atm_cmp) with
  | less_equal => check_current_bound lb (option_min ub atomic.(atm_val)) holes
  | greater_equal => check_current_bound (option_max lb atomic.(atm_val)) ub holes
  | equal =>
      if is_in_bounds lb ub atomic.(atm_val)
        then Some (Some atomic.(atm_val), Some atomic.(atm_val), holes)
        else None
  | not_equal =>
      if is_in_bounds lb ub atomic.(atm_val)
        then Some (lb, ub, sint.add atomic.(atm_val) holes)
        else Some (lb, ub, holes)
  end.

Definition atomic_holds (x : Z) (a : Atomic) :=
  match a.(atm_cmp) with
  | less_equal => x <= a.(atm_val)
  | greater_equal => x >= a.(atm_val)
  | equal => x = a.(atm_val)
  | not_equal => x <> a.(atm_val)
  end.

Ltac simplify_bounds :=
  repeat match goal with
  | [ |- context[Z.max ?l ?a <=? ?u] ] =>
      let P := constr:(Z.max l a <=? u) in
      let H := fresh "H" in
      pose proof (Z.leb_le (Z.max l a) u) as H;
      unfold Z.leb in H;
      destruct (Z.max l a <=? u) eqn:Heq;
      try (rewrite Heq; try reflexivity; try lia)
  | [ |- context[?l <=? Z.min ?u ?a] ] =>
      let P := constr:(l <=? Z.min u a) in
      let H := fresh "H" in
      pose proof (Z.leb_le l (Z.min u a)) as H;
      unfold Z.leb in H;
      destruct (l <=? Z.min u a) eqn:Heq;
      try (rewrite Heq; try reflexivity; try lia)
  end.

Definition atomic_holds_for_implied (atomic : Atomic) (lb : option Z) (ub : option Z) (holes : sint.t) :=
  forall x,
    current_bound_holds x lb ub
      ->
    is_not_holes x holes
      ->
    atomic_holds x atomic.

Lemma apply_atomic_tightens :
  forall atomic lb ub holes,
    apply_atomics x 

Lemma apply_atomic_correct :
  forall atomic lb ub holes x,
    current_bound_holds x lb ub
      ->
    is_not_holes x holes
      ->
    atomic_holds x atomic
      ->
    match apply_atomic atomic lb ub holes with
    | Some (lb', ub', holes') =>
      current_bound_holds x lb' ub'
        /\
      is_not_holes x holes'
    | None => False
    end. 
Proof.
  intros atomic lb ub holes x.
  intros Hcurrent Hholes Hatom.
  assert (x <> atm_val atomic -> is_not_holes x (sint.add (atm_val atomic) holes)) as Hholeadd.
  {
    intros Hnot.
    unfold is_not_holes in *.
    intros n.
    rewrite sint.add_spec.
    intros H.
    destruct H.
    - rewrite H. exact Hnot.
    - apply Hholes. exact H.
  }
  unfold apply_atomic.
  unfold atomic_holds in Hatom.
  unfold current_bound_holds in *.
  unfold check_current_bound.
  unfold option_min; unfold option_max.
  unfold option_bound in *.
  unfold is_in_bounds.
  destruct atomic.(atm_cmp); destruct lb as [lb_val |]; destruct ub as [ub_val |];
  try (destruct (lb_val <=? atm_val atomic) eqn:Hlbatom);
  try (destruct (atm_val atomic <=? ub_val) eqn:Hubatom); simpl;
  repeat split; try apply Hholeadd; try assumption; try lia;
  (assert (lb_val <= ub_val) as Hlbub by lia);
  simplify_bounds;
  repeat split; try assumption; try reflexivity; try lia.
Qed.

Fixpoint apply_atomics_rec (atomics : list Atomic) (lb : option Z) (ub : option Z) (holes : sint.t):=
  match atomics with
  | nil => Some (lb, ub, holes)
  | a :: atomics' => 
    match apply_atomic a lb ub holes with
    | None => None
    | Some (lb, ub, holes) => apply_atomics_rec atomics' lb ub holes
    end
  end.

Lemma apply_atomics_rec_correct :
  forall atomics lb ub holes x,
    current_bound_holds x lb ub
      ->
    is_not_holes x holes
      ->
    (forall a, In a atomics -> atomic_holds x a)
      ->
    match apply_atomics_rec atomics lb ub holes with
    | None => False
    | Some (lb', ub', holes') =>
      current_bound_holds x lb' ub'
        /\
      is_not_holes x holes'
    end.
Proof.
  induction atomics.
  - intros lb ub holes x. intros Hcurrent Hholes Ha.
    simpl. split; assumption.
  - intros lb ub holes x. intros Hcurrent Hholes Hinholds.
    simpl.
    specialize (apply_atomic_correct) as Happly_correct.
    assert (atomic_holds x a) as Ha_holds.
    {
      clear -Hinholds. apply Hinholds. simpl. left. reflexivity.
    }
    eapply Happly_correct in Ha_holds.
    + destruct (apply_atomic a lb ub holes) as [[[lba' uba'] holesa']|] eqn:Ha.
      * rewrite Ha in Ha_holds.
        apply IHatomics; try easy.
        intros a' Hin. apply Hinholds.
        right. exact Hin.
      * rewrite Ha in Ha_holds. exact Ha_holds.
    + assumption.
    + assumption.
Qed.

Definition holes_in_bounds (holes : sint.t) (lb : option Z) (ub : option Z) :=
  let holes_above := 
    match lb with
    | None => holes
    | Some lb => split_above holes lb 
    end in
  match ub with
  | None => holes_above
  | Some ub => split_below holes_above ub
  end.

Lemma holes_split_equiv :
  forall lb ub holes x,
    current_bound_holds x lb ub /\ is_not_holes x holes
      <->
    current_bound_holds x lb ub /\ is_not_holes x (holes_in_bounds holes lb ub).
Proof.
  intros lb ub holes x.
  unfold current_bound_holds; unfold option_bound.
  unfold holes_in_bounds.
  destruct lb as [lb_val |]; destruct ub as [ub_val |];
  repeat split; destruct H as [Hbounds Hholes]; try assumption; try lia;
  unfold is_not_holes in *; intros n; specialize (Hholes n); try rewrite split_below_spec in *;
  try rewrite split_above_spec in *; try rewrite split_below_spec in *;
  try destruct (lb_val <=? n) eqn:Hln; try destruct (n <=? ub_val) eqn:Hun;
  intros H; try lia; apply Hholes;
  repeat split; try apply H; lia.
Qed.

Definition apply_holes_side (holes : list Z) 

Definition apply_atomic_init (atomic : Atomic) (lb : Z) (ub : Z) (holes : sint.t) :=
  match atomic.(atm_cmp) with
  | less_equal => check_bound lb (Z.min ub atomic.(atm_val)) holes
  | greater_equal => check_bound (Z.max lb atomic.(atm_val)) ub holes
  | equal =>
    if ((ub <? atomic.(atm_val)) || (atomic.(atm_val) <? lb))
      then None
      else Some (atomic.(atm_val), atomic.(atm_val), holes)
  | not_equal => 
    if ((lb <=? atomic.(atm_val)) && (atomic.(atm_val) <=? ub))
      then Some (lb, ub, sint.add atomic.(atm_val) holes)
      else None
  end.





Definition hole_fold_f (hole : Z) (acc : (Z * list Z)) :=
  match acc with
  | (lb, interior) =>
    if (hole =? lb)
      then (lb + 1, interior)
      else (lb, hole :: interior)
  end.

Definition apply_holes_l (lb : Z) (holes : sint.t) :=
  sint.fold hole_fold_f holes (lb, nil).

Definition hole_fold_r_f (acc : (Z * sint.t)) (hole : Z) :=
  match acc with
  | (ub, interior) =>
    if (hole =? ub)
      then (ub - 1, interior)
      else (ub, sint.add hole interior)
  end.

Definition apply_holes_r (ub : Z) (holes : list Z) :=
  fold_left hole_fold_r_f holes (ub, sint.empty).

Definition apply_holes (lb : Z) (ub : Z) (holes : sint.t) :=
  let holes_between := in_interval holes lb ub in
  match apply_holes_l lb holes_between with
  | (lb, interior_l) =>
    match apply_holes_r ub interior_l with
    | (ub, interior) =>
      check_bound lb ub interior
    end
  end.


Fixpoint apply_atomics_rec (atomics : list Atomic) (lb : Z) (ub : Z) (holes : sint.t):=
    match atomics with
    | nil => Some (lb, ub, holes)
    | a :: atomics' => 
      match apply_atomic a lb ub holes with
      | None => None
      | Some (lb, ub, holes) => apply_atomics_rec atomics' lb ub holes
      end
    end.

Definition apply_atomics (atomics : list Atomic) (lb : Z) (ub : Z) :=
  match apply_atomics_rec atomics lb ub sint.empty with
  | None => None
  | Some (lb, ub, holes) =>
    apply_holes lb ub holes
  end.