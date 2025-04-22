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
  | Some bound => Z.min bound new
  | None => new
  end.

Definition option_max (bound : option Z) (new : Z) :=
  match bound with
  | Some bound => Z.max bound new
  | None => new
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
  | less_equal => check_current_bound lb (Some (option_min ub atomic.(atm_val))) holes
  | greater_equal => check_current_bound (Some (option_max lb atomic.(atm_val))) ub holes
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

Definition apply_atomics_rec_prod (atomics : list Atomic) (applied : (option Z * option Z * sint.t)) :=
  match applied with
  | (lb, ub, holes) => apply_atomics_rec atomics lb ub holes
  end.

Definition apply_holes_prod (applied : (option Z * option Z * sint.t)) :=
  match applied with
  | (lb, ub, holes) => apply_holes lb ub holes
  end.

Definition option_map_flat {A} (f : A -> option A) (a : option A) : option A :=
  match a with
  | Some a => f a
  | None => None
  end.

Definition apply_atomics2 (atomics : list Atomic) (to_apply : option (option Z * option Z * sint.t)) :=
  let applied := option_map_flat (apply_atomics_rec_prod atomics) to_apply in
  option_map_flat apply_holes_prod applied.

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
Definition is_in_dom (y : Z) (dom : option (option Z * option Z * sint.t)) :=
  match dom with
  | None => False
  | Some (lb, ub, holes) =>
      (match ub with
      | Some ub => y <= ub
      | None => True
      end)
        /\
      (match lb with
      | Some lb => lb <= y
      | None => True
      end)
        /\
      (~ sint.In y holes)
  end.

Definition dom_equiv dom1 dom2 :=
  forall y, is_in_dom y dom1 <-> is_in_dom y dom2.

Definition atomics_res_equiv (dom1 dom2 : option (option Z * option Z * sint.t)) :=
  match dom1 with
  | None => dom1 = dom2
  | Some (lb1, ub1, holes1) =>
    match dom2 with
    | None => False
    | Some (lb2, ub2, holes2) => lb1 = lb2 /\ ub1 = ub2 /\ sint.Equal holes1 holes2
    end
  end.

Lemma and_true_r (P : Prop) : P /\ True <-> P.
Proof. 
  split; intros H; repeat split; try reflexivity; apply H.
Qed.

Lemma and_true_l (P : Prop) : True /\ P <-> P.
Proof.
  split; intros H; repeat split; try reflexivity; apply H.
Qed.

Lemma apply_holes_side_tightens :
  forall holes bound (up : bool),
    if up
      then bound <= apply_holes_side holes bound up
      else apply_holes_side holes bound up <= bound.
Proof.
  induction holes.
  - intros bound up. destruct up; simpl; lia.
  - simpl. intros bound up.
    destruct (apply_hole a bound up) as [bound'|] eqn:Happly; destruct up eqn:Hup; try lia;
    specialize (IHholes bound' up); rewrite Hup in IHholes.
    1: enough (bound <= bound') by lia. 
    2: enough (bound' <= bound) by lia.
    all: unfold apply_hole in Happly; destruct (a =? bound) eqn:Habound; inversion Happly; subst bound'.
    all: lia.
Qed.

(* Pushes ~ inwards between boolean statements *)
Ltac normalize_bool_in H :=
  repeat (
    rewrite <- andb_true_iff in H ||
    rewrite <- andb_false_iff in H ||
    rewrite <- orb_true_iff in H ||
    rewrite <- orb_false_iff in H
  ); repeat (
    rewrite not_true_iff_false in H ||
    rewrite not_false_iff_true in H
  ); repeat (
    rewrite andb_true_iff in H ||
    rewrite andb_false_iff in H ||
    rewrite orb_true_iff in H ||
    rewrite orb_false_iff in H
  ).

Ltac in_split_simpl H :=
  rewrite <- sint.mem_spec in H;
  repeat rewrite <- Z.leb_le in H;
  normalize_bool_in H;
  repeat rewrite <- not_true_iff_false in H;
  repeat rewrite Z.leb_le in H;
  rewrite sint.mem_spec in H.

Lemma not_in_holes_if :
  forall n holes,
  ~ sint.In n holes -> is_not_holes n holes.
Proof.
  intros n holes.
  intros Hnot_in.
  intros n' Hholesn' Hnn'; subst n'.
  contradiction.
Qed.

Lemma le_ge :
  forall n m,
    n >= m <-> m <= n.
Proof. lia. Qed.

Require Import Sorting.Permutation.

Instance dom_equiv_equiv : RelationClasses.Equivalence dom_equiv.
Proof.
  constructor.
  - intros x. unfold dom_equiv. reflexivity.
  - intros x y. unfold dom_equiv; easy.
  - intros x y z. unfold dom_equiv. 
    intros H1 H2.
    intros n.
    rewrite H1. rewrite <- H2. reflexivity.
Defined.

Lemma atom_eq_dec : forall a a' : Atomic, {a = a'} + {a <> a'}.
Proof. repeat decide equality. Qed.

Lemma current_bound_is_not_holes_iff_is_in_dom :
  forall lb ub holes y,
    is_in_dom y (Some (lb, ub, holes))
      <->
    current_bound_holds y lb ub
      /\
    is_not_holes y holes.
Proof.
  intros lb ub holes.
  intros y.
  unfold is_in_dom.
  unfold current_bound_holds, option_bound.
  unfold is_not_holes.
  split; intros H.
  - repeat split.
    + destruct lb; try reflexivity. lia.
    + destruct ub; try reflexivity. lia.
    + intros n Hin Hyn. apply H.
      subst y. assumption.
  - repeat split.
    + destruct ub; try reflexivity. lia.
    + destruct lb; try reflexivity. lia.
    + intros Hin. destruct H as [_ H].
      apply H in Hin. contradiction.
Qed.

Require Checker.Utility.
Import Utility.ListEx.

Definition stronger_domain (dom1 dom2 : option (option Z * option Z * sint.t)) :=
  forall n, is_in_dom n dom1 -> is_in_dom n dom2.

(* Lemma stronger_than_in :
  forall lb ub holes lb' ub' holes' a atoms,
    In a atoms
      ->
    stronger_domain (Some (lb, ub, holes)) (Some (lb', ub', holes'))
      ->
    stronger_domain (apply_atomics_rec atoms lb ub holes) (apply_atomic a lb' ub' holes').
Proof.
Admitted.

Lemma stronger_than_input :
  forall lb ub holes atoms,
    stronger_domain (apply_atomics_rec atoms lb ub holes) (Some (lb, ub, holes)).
Proof.
Admitted. *)

Lemma none_if_stronger :
  forall dom,
    dom_equiv None dom <-> stronger_domain dom None.
Proof.
  intros dom; unfold dom_equiv, stronger_domain.
  split.
  + intros Hequiv. intros n. rewrite Hequiv; easy.
  + intros Hstrong. intros n. split.
    * intros Hnone. unfold is_in_dom in Hnone.
      contradiction.
    * intros Hindom. apply Hstrong in Hindom.
      assumption.
Qed.

Instance stronger_domain_refl : RelationClasses.Reflexive stronger_domain.
Proof.
  intros x. unfold stronger_domain. easy.
Defined.

Instance stronger_domain_trans : RelationClasses.Transitive stronger_domain.
Proof.
  intros x y z.
  unfold stronger_domain.
  intros Hxy Hyz.
  intros n Hinx.
  apply Hyz.
  apply Hxy.
  assumption.
Qed.

Lemma dom_equiv_is_stronger :
  forall dom dom',
    dom_equiv dom dom'
      ->
    stronger_domain dom dom'.
Proof.
  intros dom dom'.
  unfold dom_equiv, stronger_domain.
  intros Hequiv.
  intros n. now rewrite Hequiv.
Qed.

Lemma check_current_bound_min :
  forall lb ub holes y lby uby holesy,
  check_current_bound lb (Some (option_min ub (atm_val y))) holes = Some (lby, uby, holesy)
    ->
  holesy = holes
    /\
  lby = lb
    /\
  uby = Some (option_min ub (atm_val y)).
Proof.
  intros lb ub holes y lby uby holesy.
  intros Hcheck.
  unfold check_current_bound in Hcheck.
  destruct lb as [lb|];
  try destruct (lb <=? option_min ub (atm_val y)); inversion Hcheck;
  try subst lby; try subst uby; try subst holesy;
  repeat split; reflexivity.
Qed.

Lemma check_current_bound_max :
  forall lb ub holes y lby uby holesy,
  check_current_bound (Some (option_max lb (atm_val y))) ub holes = Some (lby, uby, holesy)
    ->
  holesy = holes
    /\
  lby = Some (option_max lb (atm_val y))
    /\
  uby = ub.
Proof.
  intros lb ub holes y lby uby holesy.
  intros Hcheck.
  unfold check_current_bound in Hcheck.
  destruct ub as [ub|];
  try destruct (option_max lb (atm_val y) <=? ub); inversion Hcheck;
  try subst lby; try subst uby; try subst holesy;
  repeat split; reflexivity.
Qed.

Lemma option_min_swap :
  forall b x y,
    option_min (Some (option_min b x)) y = option_min (Some (option_min b y)) x.
Proof.
  intros b x y; unfold option_min.
  destruct b; lia.
Qed.

Lemma option_max_swap :
  forall b x y,
    option_max (Some (option_max b x)) y = option_max (Some (option_max b y)) x.
Proof.
  intros b x y; unfold option_max.
  destruct b; lia.
Qed.




Ltac destruct_ands :=
  repeat match goal with
  | [ H: _ /\ _ |- _ ] =>
      let H1 := fresh H "1" in
      let H2 := fresh H "2" in
      destruct H as [H1 H2]
  end.

Ltac apply_lemmas_with L1 L2 :=
  repeat match goal with
  | H: _ |- _ =>
      first [ apply L1 in H | apply L2 in H ]
  end. 

Ltac destruct_is_in_bounds :=
  repeat match goal with
  | [ H: context[if is_in_bounds ?lb ?ub ?val then _ else _] |- _ ] =>
      let b := fresh "b" in
      let Hb := fresh "Hb" in
      remember (is_in_bounds lb ub val) as b eqn:Hb;
      destruct b
  end.

Ltac invert_some_eq :=
  repeat match goal with
  | [ H: Some ?a = Some ?b |- _ ] =>
      inversion H; clear H; subst
  end.

Lemma not_in_add :
  forall n y s,
  ~ (n = y \/ sint.In n s)
    <->
  n <> y /\ ~ sint.In n s.
Proof.
  intros n y s.
  rewrite <- Z.eqb_eq. rewrite <- sint.mem_spec.
  split; intros H;
  normalize_bool_in H; destruct_ands;
  rewrite <- not_true_iff_false in *;
  rewrite Z.eqb_eq in *; rewrite sint.mem_spec in *;
  try easy.
  intros [Hny | Hin]; contradiction.
Qed.

Ltac destruct_all_option_Z :=
  repeat match goal with
  | [ H: option Z |- _ ] => destruct H
  end.

Lemma or_swap_first_second : forall A B C : Prop, A \/ B \/ C <-> B \/ A \/ C.
Proof.
  intros A B C.
  split; intros H;
  destruct H as [H1 | [H2 | H3]];
  try (left; assumption);
  try (right; left; assumption);
  (right; right; assumption).
Qed.

Lemma is_in_dom_add :
  forall y lb ub holes a, 
  is_in_dom y (Some (lb, ub, sint.add a holes))
    <->
  is_in_dom y (Some (lb, ub, holes)) /\ y <> a.
Proof.
  intros y lb ub holes a.
  unfold is_in_dom.
  rewrite sint.add_spec.
  rewrite not_in_add.
  split; intros H;
  destruct_ands;
  repeat split; easy.
Qed.

Lemma min_le_both :
  forall n m k,
    n <= Z.min m k
      <->
    n <= m /\ n <= k.
Proof. lia. Qed.

Lemma is_in_dom_min :
  forall y lb ub holes b, 
  is_in_dom y (Some (lb, Some (option_min ub b), holes))
    <->
  is_in_dom y (Some (lb, ub, holes)) /\ y <= b.
Proof.
  intros y lb ub holes b.
  unfold is_in_dom.
  unfold option_min.
  destruct ub as [ub|].
  - rewrite min_le_both.
    split; intros H; destruct_ands;
    repeat split; easy.
  - split; intros H; destruct_ands;
    repeat split; easy.
Qed.


Lemma is_in_bounds_false_in_dom_not :
  forall lb ub holes y a, 
  is_in_bounds lb ub a = false
    ->
  is_in_dom y (Some (lb, ub, holes))
    ->
  y <> a.
Proof.
  intros lb ub holes y a.
  unfold is_in_bounds, is_in_dom.
  destruct lb as [lb|]; destruct ub as [ub|];
  intros Hnotbounds Hdom; lia.
Qed.

Lemma dom_effect :
  forall a lb ub holes,
    forall n, 
      is_in_dom n (apply_atomic a lb ub holes)
        <->
      is_in_dom n (Some (lb, ub, holes)) /\ atomic_holds n a.
Proof.
  intros a lb ub holes.
  intros n.
  unfold apply_atomic, atomic_holds, check_current_bound.
  unfold is_in_bounds, option_min, option_max.
  unfold is_in_dom.
  destruct (atm_cmp a);
  destruct lb as [lb|]; destruct ub as [ub|];
  try (destruct (lb <=? atm_val a) eqn:Hlbatom);
  try (destruct (atm_val a <=? ub) eqn:Hubatom);
  simpl; try easy;
  simplify_bounds; simpl;
  try rewrite sint.add_spec;
  try rewrite not_in_add;
  split; intros; destruct_ands;
  repeat split; try easy; lia.
Qed.

Lemma dom_effect_rec :
  forall atoms lb ub holes,
    forall n,
      is_in_dom n (apply_atomics_rec atoms lb ub holes)
        <->
      is_in_dom n (Some (lb, ub, holes)) /\ (forall a, In a atoms -> atomic_holds n a).
Proof.
  induction atoms.
  - intros lb ub holes. simpl apply_atomics_rec.
    intros n.
    split; intros H.
    + split; try assumption.
      intros a Hin. destruct Hin.
    + apply H.
  - intros lb ub holes.
    simpl apply_atomics_rec.
    destruct (apply_atomic a lb ub holes) as [[[lb' ub'] holes']|]eqn:Ha.
    + intros n.
      rewrite IHatoms; clear IHatoms.
      split.
      * intros [Hdom Hholds].
        rewrite <- Ha in Hdom.
        rewrite dom_effect in Hdom.
        split.
        -- apply Hdom.
        -- intros a' Hin. destruct Hin.
          ++ subst a'. apply Hdom.
          ++ apply Hholds. exact H.
      * intros [Hdom Hholds].
        assert (is_in_dom n (apply_atomic a lb ub holes)) as Hinapply.
        { rewrite dom_effect. split.
          - apply Hdom.
          - apply Hholds. left. reflexivity. }
        split.
        -- rewrite <- Ha. exact Hinapply.
        -- intros a' Hin. apply Hholds.
          right. exact Hin.
    + intros n.
      split.
      * intros H. unfold is_in_dom in H. contradiction.
      * intros H.
        rewrite <- Ha.
        rewrite dom_effect.
        split.
        -- apply H.
        -- apply H. left. reflexivity.
Qed.

Lemma input_equiv_apply :
  forall a lb ub holes lb' ub' holes',
    dom_equiv (Some (lb, ub, holes)) (Some (lb', ub', holes'))
      ->
    dom_equiv (apply_atomic a lb ub holes) (apply_atomic a lb' ub' holes').
Proof.
  intros a lb ub holes lb' ub' holes'.
  unfold dom_equiv.
  intros Hequiv y.
  repeat rewrite dom_effect.
  rewrite Hequiv.
  reflexivity.
Qed.
 

(* Lemma input_equiv :
  forall atoms lb ub holes lb' ub' holes',
    dom_equiv (Some (lb, ub, holes)) (Some (lb', ub', holes'))
      ->
    dom_equiv (apply_atomics_rec atoms lb ub holes) (apply_atomics_rec atoms lb' ub' holes').
Proof.
  induction atoms.
  - intros. simpl. exact H.
  - intros. simpl.
    destruct (apply_atomic a lb ub holes) as [[[lba uba] holesa]|] eqn:Ha;
    destruct (apply_atomic a lb' ub' holes') as [[[lba' uba'] holesa']|] eqn:Ha'.
    + apply IHatoms; clear IHatoms.
      rewrite <- Ha.
      rewrite <- Ha'.
      apply input_equiv_apply.
      exact H.
    + symmetry. apply none_if_stronger.
      assert (dom_equiv None (Some (lba, uba, holesa))) as Hanone.
      { rewrite <- Ha'. rewrite <- Ha. apply input_equiv_apply. symmetry. exact H. }
      transitivity (Some (lba, uba, holesa)).
      * apply stronger_than_input.
      * apply dom_equiv_is_stronger.
        symmetry. exact Hanone.
    + apply none_if_stronger.
      transitivity (Some (lba', uba', holesa')).
      * apply stronger_than_input.
      * rewrite <- Ha.
        rewrite <- Ha'.
        apply dom_equiv_is_stronger.
        apply input_equiv_apply.
        symmetry. exact H.
    + reflexivity.
Qed.
 *)
Lemma permute_rec_equiv :
  forall atoms atoms' lb ub holes,
    Permutation atoms atoms'
      ->
    dom_equiv (apply_atomics_rec atoms lb ub holes) (apply_atomics_rec atoms' lb ub holes).
Proof.
  intros atoms atoms' lb ub holes.
  intros Hpermute.
  unfold dom_equiv.
  intros y.
  repeat rewrite dom_effect_rec.
  split; intros H;
  split; try apply H; 
  intros a Hin; apply H.
  - now apply Permutation_in with (l := atoms').
  - now apply Permutation_in with (l := atoms).
Qed.

Lemma apply_holes_equiv :
  forall lb ub holes, 
    dom_equiv (apply_holes lb ub holes) (Some (lb, ub, holes)).
Proof.
  intros lb ub holes.
  unfold apply_holes.
  unfold bounds_both_none.
  unfold dom_equiv; unfold is_in_dom; intros y; split.
  - specialize apply_holes_side_tightens as Htightens;
    destruct lb as [lb|]; destruct ub as [ub|]; simpl; 
    try destruct_leb; try rewrite split_below_spec; try rewrite split_above_spec; repeat rewrite <- and_assoc; repeat rewrite and_true_r; repeat rewrite and_true_l; try easy;
    intros H; pose proof Htightens as Htightens_lb; try specialize (Htightens_lb (sint.elements holes) lb true); try specialize (Htightens (rev (sint.elements holes)) ub false); try in_split_simpl H; simpl in *.
    2-3: destruct H as [H [Hin | Hnot_apply]]; try contradiction; split; try assumption; lia.
    destruct H as [[Hyapply Happlyy] [[Hnotin | Hnot] | Hnot]]; try contradiction.
    split; try assumption; lia.
  - specialize apply_holes_side_lb as Hside_lb; 
    specialize apply_holes_side_ub as Hside_ub;
    destruct lb as [lb|]; destruct ub as [ub|]; simpl; try destruct_leb;
    try rewrite split_below_spec; try rewrite split_above_spec;
    repeat rewrite <- and_assoc; repeat rewrite and_true_r; repeat rewrite and_true_l; try easy; intros H;
    assert (~ sint.In y holes) as Hholes by easy;
    apply not_in_holes_if in Hholes;
    apply is_not_holes_to_list in Hholes;
    pose proof Hholes as Hholes_rev;
    rewrite <- is_not_holes_list_rev in Hholes_rev;
    try apply Hside_lb with (lb := lb) in Hholes;
    try apply Hside_ub with (ub := ub) in Hholes_rev;
    try rewrite le_ge in *; repeat split; try easy.
    specialize (apply_holes_side_tightens (sint.elements holes) lb true) as Htightens_lb;
    specialize (apply_holes_side_tightens (rev (sint.elements holes)) ub false) as Htightens_ub; simpl in Htightens_ub, Htightens_lb.
    clear Hside_lb Hside_ub.
    rewrite <- not_true_iff_false in Hleb.
    rewrite Z.leb_le in Hleb.
    (* Unclear why lia doesn't work immediately here *)
    remember (apply_holes_side (sint.elements holes) lb true) as apply_lb;
    remember (apply_holes_side (rev (sint.elements holes)) ub false) as apply_ub.
    assert (y <= apply_ub).
    { rewrite Heqapply_ub. exact Hholes_rev. }
    lia.
Qed.



Lemma holes_in_bounds_equiv :
  forall lb ub holes,
    dom_equiv (Some (lb, ub, holes_in_bounds holes lb ub)) (Some (lb, ub, holes)).
Proof.
  specialize holes_split_equiv as Hsplit.
  intros lb ub holes.
  unfold dom_equiv.
  intros y. split; intros.
  - rewrite current_bound_is_not_holes_iff_is_in_dom in H.
    rewrite <- Hsplit in H.
    rewrite current_bound_is_not_holes_iff_is_in_dom.
    assumption.
  - rewrite current_bound_is_not_holes_iff_is_in_dom.
    rewrite <- Hsplit.
    rewrite <- current_bound_is_not_holes_iff_is_in_dom.
    assumption.
Qed. 

Lemma permute_apply_equiv :
  forall atoms atoms' lb_in ub_in holes_in,
    Permutation atoms atoms'
      ->
    dom_equiv (apply_atomics atoms lb_in ub_in holes_in) (apply_atomics atoms' lb_in ub_in holes_in).
Proof.
  intros atoms atoms' lb_in ub_in holes_in.
  intros Hpermute.
  unfold apply_atomics.
  destruct (apply_atomics_rec atoms lb_in ub_in holes_in) as [[[lb ub] holes]|] eqn:Hres;
  destruct (apply_atomics_rec atoms' lb_in ub_in holes_in) as [[[lb' ub'] holes']|] eqn:Hres'.
  + repeat rewrite apply_holes_equiv.
    repeat rewrite holes_in_bounds_equiv.
    rewrite <- Hres.
    rewrite <- Hres'.
    apply permute_rec_equiv.
    exact Hpermute.
  + rewrite apply_holes_equiv.
    rewrite holes_in_bounds_equiv.
    rewrite <- Hres.
    rewrite <- Hres'.
    apply permute_rec_equiv.
    exact Hpermute.
  + rewrite apply_holes_equiv.
    rewrite holes_in_bounds_equiv.
    rewrite <- Hres.
    rewrite <- Hres'.
    apply permute_rec_equiv.
    apply Hpermute.
  + reflexivity.
Qed.

(* Lemma apply_atomics_app :
  forall atoms atoms' lb ub ,
    dom_equiv (apply_atomics_dom (atoms ++ atoms') dom) (
      match apply_atomics_dom atoms' dom with 
      | Some dom' => apply_atomics_dom atoms dom'
      | None => None
      end
    ).
Proof.
(*  *)
    
  destruct lb as [lb|]; destruct ub as [ub|]; simpl;
  intros y.
  4: { reflexivity. }
  all: repeat rewrite <- and_assoc; repeat rewrite and_true_r; repeat rewrite and_true_l.
  all: split; intros H.
  1: { 
    destruct_leb.
    - rewrite split_below_spec; rewrite split_above_spec.
    - split; intros H; exfalso; try assumption.
      specialize (Htightens (sint.elements holes) lb true)as Htightenslb; simpl in Htightenslb.
      specialize (Htightens (rev (sint.elements holes)) ub false); simpl in Htightens.
      destruct H as [[Hub Hlb] Hholes].
      apply not_in_holes_iff in Hholes.
      apply is_not_holes_to_list in Hholes.
      pose proof Hholes as Hholes_rev.
      rewrite <- is_not_holes_list_rev in Hholes_rev.
      apply apply_holes_side_lb with (lb := lb) in Hholes; try lia.
      apply apply_holes_side_ub with (ub := ub) in Hholes_rev; try lia.
      rewrite <- not_true_iff_false in Hleb.
      rewrite Z.leb_le in Hleb.
      (* Unsure why lia doesn't work immediately. *)
      remember (apply_holes_side (rev (sint.elements holes)) ub false) as apply_ub.
      assert (y <= apply_ub).
      { rewrite Heqapply_ub. exact Hholes_rev. }
      clear Hholes_rev; rename H into Hholes_rev.
      clear Heqapply_ub.
      remember (apply_holes_side (sint.elements holes) lb true) as apply_lb; clear Heqapply_lb.
      lia.
  }
  2: {
    specialize apply_holes_side_lb as Hside_lb.
    split.
    - intros [Hside Hinabove].
      in_split_simpl Hinabove.
      destruct Hinabove as [Hin | Hholeside].
      + split; try assumption.
        specialize (Htightens (sint.elements holes) lb true); simpl in Htightens.
        lia.
      + contradiction. 
    - intros [Hlby Hholes].
      rewrite split_above_spec.
      specialize (Hside_lb y lb (sint.elements holes)).
      assert (is_not_holes y holes).
      { intros n' Hholesn' Hyn'; subst n'. apply Hholes; assumption. }
      apply is_not_holes_to_list in H.
      apply Hside_lb in H; try lia; clear Hside_lb.
      split.
      + lia.
      + intros [Hholes' Happly'].
        contradiction.
  }
 *)
  

(* Lemma atomics_holes_end :
  forall dom atoms1 atoms2,
    atomics_res_equiv (apply_atomics2 atoms2 (apply_atomics2 (atoms1) dom)) (option_map_flat apply_holes_prod (option_map_flat (apply_atomics_rec_prod (atoms1 ++ atoms2)) dom)).
Proof.
  intros dom atoms1 atoms2.
  unfold atomics_res_equiv.
  destruct (apply_atomics2 atoms2 (apply_atomics2 atoms1 dom)) as [[[lb' ub'] holes']|] eqn:Hres.
  - unfold option_map_flat.
    destruct dom as [dom|].
    2: { unfold apply_atomics2 in Hres. unfold option_map_flat in Hres. discriminate Hres. }
    destruct (apply_atomics_rec_prod (atoms1 ++ atoms2) dom) eqn:Hresrec.
    + destruct (apply_holes_prod p) eqn:Hholesp.
      {

      }
    (* 2: { unfold apply_atomics2 in Hres. unfold option_map_flat in Hres. rewrite Hresrec in Hres. discriminate Hres. }
    destruct apply_holes_prod eqn:Hholesres.
    2: { unfold apply_atomics2 in Hres. unfold option_map_flat in Hres. rewrite Hresrec in Hres. rewrite Hholesres in Hres. discriminate Hres. }
 *)
 *)

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