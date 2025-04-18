Require Import Coq.Logic.FinFun.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import String.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Arith.PeanoNat.
Require Import Bool.

Require Import Lia.
Require Coq.MSets.MSetAVL.
Require Coq.MSets.MSetProperties.
Require Coq.Structures.OrdersEx.

Require Checker.Utility.

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

Definition mk_atm_le (c : Z) :=
  {| atm_cmp := less_equal; atm_val := c |}.

Definition mk_atm_ge (c : Z) :=
  {| atm_cmp := greater_equal; atm_val := c |}.

Definition mk_atm_ne (c : Z) :=
  {| atm_cmp := not_equal; atm_val := c |}.

Definition mk_atm_eq (c : Z) :=
  {| atm_cmp := equal; atm_val := c |}.

Open Scope Z_scope.

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

Definition is_not_holes_list (x : Z) (holes : list Z) :=
  forall n,
    In n holes
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


(* We don't use this lemma elsewhere because the we don't prove that the tightening done in the apply holes step works, but this does at least provide strong evidence that the apply_atomic_rec really works! *)
Lemma apply_atomic_tightens :
  forall atomic lb ub holes,
    match apply_atomic atomic lb ub holes with
    | Some (lb', ub', holes') =>
      atomic_holds_for_implied atomic lb' ub' holes'
    | None => True
    end.
Proof.
  intros atomic lb ub holes.
  unfold apply_atomic.
  unfold atomic_holds_for_implied.
  unfold atomic_holds.
  unfold current_bound_holds.
  unfold is_in_bounds.
  unfold check_current_bound.
  unfold option_min; unfold option_max.
  unfold option_bound.
  destruct (atm_cmp atomic); destruct lb as [lb_val |]; destruct ub as [ub_val |];
  try (destruct (lb_val <=? atm_val atomic) eqn:Hlbatom);
  try (destruct (atm_val atomic <=? ub_val) eqn:Hubatom); simpl;
  try reflexivity; try simplify_bounds; try reflexivity;
  intros x; intros Hbound; intros Hholes; try lia;
  unfold is_not_holes in Hholes; apply Hholes; rewrite sint.add_spec; 
  left; reflexivity.
Qed.


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

Definition apply_hole (hole : Z) (bound : Z) (up : bool) :=
  if (hole =? bound)
    then if up
      then Some (bound + 1)
      else Some (bound - 1)
    else None.

Fixpoint apply_holes_side (holes : list Z) (bound : Z) (up : bool) :=
  match holes with
  | nil => bound
  | hole :: holes' => match apply_hole hole bound up with
    | None => bound
    | Some new_bound => apply_holes_side holes' new_bound up
    end
  end.

Lemma apply_holes_side_correct :
  forall holes up bound new_bound x,
    is_not_holes_list x holes
      ->
    apply_holes_side holes bound up = new_bound
      ->
    if up
      then
        bound <= x
          ->
        new_bound <= x
      else 
        x <= bound
          ->
        x <= new_bound
.
Proof.
  induction holes as [| h holes' IH].
  - intros up bound new_bound.
    intros x Hnotholes Happly. simpl in Happly. subst new_bound.
    destruct up; intros H; assumption.
  - intros up bound new_bound x Hnotholes Happly.
    assert (is_not_holes_list x holes' /\ x <> h) as [Hnotholes' Hxnh].
    {
      split.
      - intros n Hin. apply Hnotholes.
        right. exact Hin.
      - apply Hnotholes. left. reflexivity.
    }
    clear Hnotholes.
    simpl in Happly; unfold apply_hole in Happly.
    destruct (h =? bound) eqn:Hh; destruct up; intros H;
    try apply IH with (x := x) in Happly; try assumption;
    try apply Happly; lia.
Qed.

Lemma is_not_holes_to_list :
  forall x holes,
    is_not_holes x holes
      ->
    is_not_holes_list x (sint.elements holes).
Proof.
  intros x holes Hholes.
  unfold is_not_holes_list.
  intros n. intros H.
  apply SetoidList.In_InA with (eqA := Z.eq) in H.
  - rewrite sint.elements_spec1 in H. apply Hholes. exact H.
  - apply Z.eq_equiv.
Qed.

Lemma is_not_holes_list_rev :
  forall x holes,
    is_not_holes_list x (rev holes) <-> is_not_holes_list x holes.
Proof.
  intros x holes. unfold is_not_holes_list.
  split; intros H; intros n; specialize (H n); rewrite <- in_rev in *; assumption.
Qed.

Lemma apply_holes_side_lb :
  forall x lb holes,
    is_not_holes_list x holes
      ->
    x >= lb
      ->
    x >= apply_holes_side holes lb true.
Proof.
  intros x lb holes.
  intros Hholes Hlb.
  specialize apply_holes_side_correct with (up := true) (holes := holes) (bound := lb) as H. simpl in H.
  rewrite Z.ge_le_iff in *.
  apply H; try reflexivity; assumption.
Qed.


Lemma apply_holes_side_ub :
  forall x ub holes,
    is_not_holes_list x holes
      ->
    x <= ub
      ->
    x <= apply_holes_side holes ub false.
Proof.
  intros x ub holes.
  intros Hholes Hub.
  specialize apply_holes_side_correct with (up := false) (holes := holes) (bound := ub) as H. simpl in H.
  apply H; try reflexivity; assumption.
Qed.


Definition bounds_both_none (lb : option Z) (ub : option Z) :=
  match lb with
  | None => true
  | Some _ => false
  end
    &&
  match ub with
  | None => true
  | Some _ => false
  end.

(* An optimization that could be done is that if the size of the holes is equal to the size of the interval, we can also return None without checking all values. *)
Definition apply_holes (lb : option Z) (ub : option Z) (holes : sint.t) :=
  if bounds_both_none lb ub
    then Some (lb, ub, holes)
    else
  let holes_list := sint.elements holes in
  let new_lb :=
    match lb with
    | None => None
    | Some lb => Some (apply_holes_side holes_list lb true)
    end in
  let new_ub :=
    match ub with
    | None => None
    | Some ub => Some (apply_holes_side (rev holes_list) ub false)
    end in
  match check_current_bound new_lb new_ub holes with
  | None => None
  | Some _ =>
  Some (new_lb, new_ub, holes_in_bounds holes new_lb new_ub)
  end.

Ltac destruct_leb :=
  match goal with
  | [ |- context[?a <=? ?b] ] =>
      let H := fresh "Hleb" in
      destruct (a <=? b) eqn:H
  end.

(* Note that we don't prove anything about actually strengthening the bounds, we just prove they are still valid bounds! *)
(* For it actually working we rely on the fact that sint is ordered in increasing order but we don't use that anywhere in the proof, for example. *)
Lemma apply_holes_sound :
  forall lb ub holes x,
    current_bound_holds x lb ub
      ->
    is_not_holes x holes
      ->
    match apply_holes lb ub holes with
    | Some (lb', ub', holes') =>
      current_bound_holds x lb' ub'
        /\
      is_not_holes x holes'
    | None => False
    end.
Proof.
  intros lb ub holes x.
  intros Hcurrent Hholes.
  unfold apply_holes, bounds_both_none, check_current_bound;
  destruct lb as [lb_val|]; destruct ub as [ub_val |]; simpl; try destruct_leb;
  repeat split; try assumption; unfold current_bound_holds in Hcurrent;
  unfold option_bound in *; destruct Hcurrent as [Hlb Hub];
  try apply apply_holes_side_lb with (holes := (sint.elements holes)) in Hlb; try apply apply_holes_side_ub with (holes := (rev (sint.elements holes))) in Hub;
  try rewrite is_not_holes_list_rev;
  try apply is_not_holes_to_list; try assumption; try lia;
  unfold is_not_holes; intros n;
  try rewrite split_below_spec; try rewrite split_above_spec;
  try rewrite <- in_rev; intros H; apply Hholes; apply H.
Qed.

Definition apply_atomics (atomics : list Atomic) (lb : option Z) (ub : option Z) (holes : sint.t) :=
  match apply_atomics_rec atomics lb ub holes with
  | None => None
  | Some (lb, ub, holes) =>
    let holes := holes_in_bounds holes lb ub in
    apply_holes lb ub holes
  end.

Lemma apply_atomics_valid :
   forall atomics lb ub holes x,
    current_bound_holds x lb ub
      ->
    is_not_holes x holes
      ->
    (forall a, In a atomics -> atomic_holds x a)
      ->
    match apply_atomics atomics lb ub holes with
    | None => False
    | Some (lb', ub', holes') =>
      current_bound_holds x lb' ub'
        /\
      is_not_holes x holes'
    end.
Proof.
  intros atomics lb ub holes x.
  intros Hcurrent Hholes Hatomics.
  unfold apply_atomics.
  specialize (apply_atomics_rec_correct atomics lb ub holes x Hcurrent Hholes Hatomics) as Hrec.
  destruct (apply_atomics_rec atomics lb ub holes) as [[[lb' ub'] holes'] |].
  - specialize apply_holes_sound as Hholes_sound.
    rewrite holes_split_equiv in Hrec.
    apply Hholes_sound; apply Hrec.
  - exact Hrec.
Qed.

Lemma apply_atomics_some :
  forall atoms lb ub holes x,
  apply_atomics atoms None None sint.empty = Some (lb, ub, holes)
    ->
  (forall a, In a atoms -> atomic_holds x a)
    ->
  current_bound_holds x lb ub
    /\
  is_not_holes x holes.
Proof.
  intros atoms lb ub holes x.
  intros Hsome.
  intros Hatoms.
  apply apply_atomics_valid with (lb := None) (ub := None) (holes := sint.empty) in Hatoms.
  - rewrite Hsome in Hatoms. exact Hatoms.
  - unfold current_bound_holds. simpl. split; reflexivity.
  - unfold is_not_holes. intros n Hin. exfalso.
    specialize sint.empty_spec as Hempty.
    specialize (Hempty n). contradiction.
Qed.

Definition holes_consistent (lb : option Z) (ub : option Z) (holes : sint.t) :=
  forall h, sint.In h holes ->
    match lb with
    | Some lb => h > lb
    | None => True
    end
      /\
    match ub with
    | Some ub => h < ub
    | None => True
    end.

Definition is_not_in (y : Z) (lb : option Z) (ub : option Z) (holes : sint.t) : bool :=
    (match ub with
    | Some ub => ub <? y
    | None => false
    end)
      ||
    (match lb with
    | Some lb => y <? lb
    | None => false
    end)
      ||
    (sint.mem y holes).

Definition bounds_exact (y : Z) (lb : option Z) (ub : option Z) :=
  match ub with
  | None => false
  | Some ub =>
    match lb with
    | None => false
    | Some lb =>
      (lb =? y) && (ub =? y)
    end
  end.

Definition check_holds (a : Atomic) (lb : option Z) (ub : option Z) (holes : sint.t) : bool :=
  match a.(atm_cmp) with
  | greater_equal =>
    (* x >= c *)
    match lb with
    | Some lb => a.(atm_val) <=? lb
    | None => false
    end
  | less_equal =>
    (* x <= c *)
    match ub with
    | Some ub => ub <=? a.(atm_val)
    | None => false
    end
  | equal =>
    bounds_exact a.(atm_val) lb ub
  | not_equal =>
    is_not_in a.(atm_val) lb ub holes
  end.

Lemma check_holds_implies :
  forall lb ub holes y a, 
  current_bound_holds y lb ub
    ->
  is_not_holes y holes
    ->
  check_holds a lb ub holes = true
    ->
  atomic_holds y a.
Proof.
  unfold current_bound_holds, is_not_holes, check_holds, atomic_holds, is_not_in, option_bound, bounds_exact. 
  intros lb ub holes y a.
  intros Hcurrent Hholes Hcheck.
  destruct lb as [lb_val|]; destruct ub as [ub_val|]; destruct (atm_cmp a); try lia; try (specialize (Hholes (atm_val a))); repeat rewrite orb_true_iff in Hcheck;
  destruct Hcheck as [[H1 | H2] | H3]; try lia; apply Hholes; rewrite <- sint.mem_spec; exact H3.
Qed.

Import Utility.ListInd.
Import Utility.ZRange.

(* This could be optimized by not using the range and just doing one pass and checking each time whether the next value is in holes *)
Definition to_full_domain (lb : Z) (ub : Z) (holes : sint.t) : sint.t :=
  let range := build_range lb ub in
  let values := filter (fun y => negb (sint.mem y holes)) range in
    fold_left (fun acc y => sint.add y acc) values sint.empty
  .

Lemma to_full_domain_correct :
  forall lb ub holes,
    (forall n, sint.In n (to_full_domain lb ub holes) <-> current_bound_holds n (Some lb) (Some ub) /\ is_not_holes n holes).
Proof.
  intros lb ub holes n.
  unfold to_full_domain.
  remember (filter
    (fun y => negb (sint.mem y holes))
    (build_range lb ub)) as values.
  assert (In n values <-> current_bound_holds n (Some lb) (Some ub) /\ is_not_holes n holes).
  {
    subst values.
    rewrite filter_In. rewrite negb_true_iff.
    split; intros.
    all: rewrite is_range_In with (s := lb) (e := ub) in *; try apply build_range_correct.
    2: { destruct H as [Hin _]. apply build_range_In_bounds in Hin. assumption. }
    all: unfold current_bound_holds in *; unfold option_bound in *; unfold is_not_holes in *.
    - destruct H as [Hbound Hmem]. 
      split; try lia. 
      intros n' Hholes.
      destruct (Z.eq_dec n n') as [Hnn' | Hnn'].
      + subst n'. 
        rewrite <- sint.mem_spec in Hholes. rewrite Hholes in Hmem. discriminate Hmem.
      + exact Hnn'.
    - split; try lia. 
      destruct (sint.mem n holes) eqn:Hmem; try reflexivity.
      exfalso.
      destruct H as [_ Hholes].
      specialize (Hholes n). apply Hholes; try reflexivity.
      rewrite <- sint.mem_spec.
      assumption. 
    - lia.
  }
  rewrite <- H; clear Heqvalues H.
  rewrite <- fold_left_rev_right.
  rewrite in_rev.
  set (P := fun (s : list Z) (acc : sint.t) =>
    sint.In n acc <-> In n s).
  (* Below proof could be reused. *)
  enough (P (rev values) (fold_right sint.add sint.empty (rev values))).
  { apply H. }
  apply fold_ind.
  - unfold P; clear P. split; intros.
    + exfalso. apply (sint.empty_spec H).
    + destruct H.
  - intros n' acc s.
    unfold P; clear P. intros IH.
    destruct (Z.eq_dec n n') as [Hnn' | Hnn'].
    + subst n'. rewrite sint.add_spec.
      split.
      * left. reflexivity.
      * intros. left. reflexivity.
    + rewrite sint.add_spec.
      split.
      * intros [Hnisn' | Hin].
        -- subst n'. contradiction.
        -- right. apply IH. exact Hin.
      * intros [Hnisn' | Hin].
        -- subst n'. contradiction.
        -- right. apply IH. exact Hin.
Qed.

Open Scope Z_scope.

Compute 
  let atms := mk_atm_ne 3 :: mk_atm_ge (-1) :: mk_atm_ne (-1) :: mk_atm_le 3 :: nil in
    match apply_atomics atms None None sint.empty with
    | None => None
    | Some (lb, ub, holes) => Some (lb, ub, sint.elements (holes))
    end
  .

Compute 
  let atms := mk_atm_ne 3 :: mk_atm_ge 3 :: mk_atm_ne 4 :: mk_atm_le 4 :: nil in
    match apply_atomics atms None None sint.empty with
    | None => None
    | Some (lb, ub, holes) => Some (lb, ub, sint.elements (holes))
    end
  .