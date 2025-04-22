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
Import Utility.ListEx.
Import Utility.ListInd.
Import Utility.ZRange.


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

Record Domain := mkDom {
  d_lb : option Z;
  d_ub : option Z;
  d_holes : sint.t
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

Definition check_bound (lb : Z) (ub : Z) (holes : sint.t) := 
  if lb <=? ub
    then Some (lb, ub, holes)
    else None.

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

Definition check_current_bound (dom : Domain) : option Domain :=
  match dom.(d_lb) with
  | None => Some dom
  | Some lb_val =>
    match dom.(d_ub) with
    | None => Some dom
    | Some ub_val =>
      if lb_val <=? ub_val
        then Some dom
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

Definition apply_atomic (dom : Domain) (atomic : Atomic) :=
  match atomic.(atm_cmp) with
  | less_equal => check_current_bound (mkDom dom.(d_lb) (option_min dom.(d_ub) atomic.(atm_val)) dom.(d_holes))
  | greater_equal => check_current_bound (mkDom (option_max dom.(d_lb) atomic.(atm_val)) dom.(d_ub) dom.(d_holes))
  | equal =>
      if is_in_bounds dom.(d_lb) dom.(d_ub) atomic.(atm_val)
        then Some (mkDom (Some atomic.(atm_val)) (Some atomic.(atm_val)) dom.(d_holes))
        else None
  | not_equal =>
      if is_in_bounds dom.(d_lb) dom.(d_ub) atomic.(atm_val)
        then Some (mkDom dom.(d_lb) dom.(d_ub) (sint.add atomic.(atm_val) dom.(d_holes)))
        else Some dom
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


Definition apply_atomics_rec (atomics : list Atomic) (dom : Domain):=
  fold_left_error apply_atomic atomics dom.

Definition holes_in_bounds lb ub holes :=
  let holes_above := 
    match lb with
    | None => holes
    | Some lb => split_above holes lb 
    end in
  match ub with
  | None => holes_above
  | Some ub => split_below holes_above ub
  end.
  
Definition tighten_holes (dom : Domain) :=
  match dom with
  | mkDom lb ub holes => 
    mkDom lb ub (holes_in_bounds lb ub holes)
  end.

(* Lemma holes_split_equiv :
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
Qed. *)

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
    ~ In x holes
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
    assert (~ In x holes' /\ x <> h) as [Hnotholes' Hxnh].
    {
      split.
      - intros Hin. apply Hnotholes.
        right. exact Hin.
      - intros Hxh. subst x. apply Hnotholes. 
        left. reflexivity.
    }
    clear Hnotholes.
    simpl in Happly; unfold apply_hole in Happly.
    destruct (h =? bound) eqn:Hh; destruct up; intros H;
    try apply IH with (x := x) in Happly; try assumption;
    try apply Happly; lia.
Qed.

Lemma is_not_holes_to_list :
  forall x holes,
    ~ sint.In x holes
      ->
    ~ In x (sint.elements holes).
Proof.
  intros x holes Hholes.
  intros H.
  apply SetoidList.In_InA with (eqA := Z.eq) in H.
  - rewrite sint.elements_spec1 in H. apply Hholes. exact H.
  - apply Z.eq_equiv.
Qed.

Lemma apply_holes_side_lb :
  forall x lb holes,
    ~ In x holes
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
    ~ In x holes
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


Definition bounds_both_none (dom : Domain) :=
  match dom.(d_lb) with
  | None => true
  | Some _ => false
  end
    &&
  match dom.(d_ub) with
  | None => true
  | Some _ => false
  end.

(* An optimization that could be done is that if the size of the holes is equal to the size of the interval, we can also return None without checking all values. *)
Definition apply_holes (dom : Domain) :=
  if bounds_both_none dom
    then Some dom
    else
  let dom := tighten_holes dom in
  let holes_list := sint.elements dom.(d_holes) in
  let new_lb :=
    match dom.(d_lb) with
    | None => None
    | Some lb => Some (apply_holes_side holes_list lb true)
    end in
  let new_ub :=
    match dom.(d_ub) with
    | None => None
    | Some ub => Some (apply_holes_side (rev holes_list) ub false)
    end in
  option_map tighten_holes (check_current_bound (mkDom new_lb new_ub dom.(d_holes))).

Ltac destruct_leb :=
  match goal with
  | [ |- context[?a <=? ?b] ] =>
      let H := fresh "Hleb" in
      destruct (a <=? b) eqn:H
  end.

Definition apply_atomic_opt (dom : option Domain) (a : Atomic) := fold_left_error_f apply_atomic dom a.

Definition apply_atomics_rec_opt (atomics : list Atomic) (dom : option Domain) :=
  option_map_flat (apply_atomics_rec atomics) dom.

Definition apply_holes_opt (dom: option Domain) :=
  option_map_flat apply_holes dom.

Definition apply_atomics (atomics : list Atomic) (dom : option Domain) : option Domain :=
  apply_holes_opt (apply_atomics_rec_opt atomics dom).

Definition is_in_dom (y : Z) (dom : option Domain) :=
  match dom with
  | None => False
  | Some (mkDom lb ub holes) =>
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

Definition stronger_domain (dom1 dom2 : option Domain) :=
  forall n, is_in_dom n dom1 -> is_in_dom n dom2.

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


Lemma atom_eq_dec : forall a a' : Atomic, {a = a'} + {a <> a'}.
Proof. repeat decide equality. Qed.

Ltac destruct_ands :=
  repeat match goal with
  | [ H: _ /\ _ |- _ ] =>
      let H1 := fresh H "1" in
      let H2 := fresh H "2" in
      destruct H as [H1 H2]
  end.

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

Lemma dom_effect :
  forall a dom,
    forall n, 
      is_in_dom n (apply_atomic dom a)
        <->
      is_in_dom n (Some dom) /\ atomic_holds n a.
Proof.
  intros a dom.
  intros n.
  unfold apply_atomic, atomic_holds, check_current_bound.
  unfold is_in_bounds, option_min, option_max.
  unfold is_in_dom; simpl.
  destruct dom as [lb ub holes];
  destruct (atm_cmp a); simpl;
  destruct lb as [lb|]; destruct ub as [ub|];
  simpl; try rewrite sint.add_spec; try rewrite not_in_add;
  try (split; intros; destruct_ands; repeat split; try easy; lia);
  try (destruct (lb <=? atm_val a) eqn:Hlbatom);
  try (destruct (atm_val a <=? ub) eqn:Hubatom);
  simplify_bounds; simpl;
  try rewrite sint.add_spec; try rewrite not_in_add;
  split; intros; try easy; destruct_ands;
  repeat split; try easy; lia.
Qed.

Lemma dom_effect_opt :
  forall a dom,
    forall n, 
      is_in_dom n (apply_atomic_opt dom a)
        <->
      is_in_dom n dom /\ atomic_holds n a.
Proof.
  intros a dom.
  unfold apply_atomic_opt, fold_left_error_f.
  destruct dom; intros n.
  - apply dom_effect.
  - split; intros H; try apply H.
    unfold is_in_dom in H.
    exfalso. exact H.
Qed.

Lemma apply_atomics_rec_opt_cons :
  forall a dom atoms,
  apply_atomics_rec_opt (a :: atoms) dom =
  apply_atomics_rec_opt atoms (apply_atomic_opt dom a).
Proof.
  intros a dom atoms.
  unfold apply_atomics_rec_opt, option_map_flat.
  destruct dom as [dom'|];
  simpl; reflexivity.
Qed.

Lemma dom_effect_rec :
  forall atoms dom,
    forall n,
      is_in_dom n (apply_atomics_rec_opt atoms dom)
        <->
      is_in_dom n dom /\ (forall a, In a atoms -> atomic_holds n a).
Proof.
  induction atoms.
  - intros dom. unfold apply_atomics_rec_opt, option_map_flat, apply_atomics_rec.
    intros n.
    destruct dom; try rewrite fold_left_error_as_fold_left;
    simpl fold_left;
    split; intros H; try apply H; split; try apply H;
    intros a'; intros Hnil; destruct Hnil.
  - intros dom.
    intros n.
    rewrite apply_atomics_rec_opt_cons.
    rewrite IHatoms; clear IHatoms.
    rewrite dom_effect_opt.
    split; intros H; repeat split; try apply H.
    + intros a' Hin.
      destruct Hin as [Ha' | Hatoms].
      * now subst a'.
      * now apply H. 
    + left. reflexivity.
    + intros a' Hin.
      apply H.
      right. exact Hin.
Qed. 

Lemma tighten_holes_equiv :
  forall dom,
    dom_equiv (Some dom) (Some (tighten_holes dom)).
Proof.
  intros dom.
  unfold dom_equiv.
  intros y. destruct dom as [lb ub holes].
  unfold is_in_dom; simpl; unfold holes_in_bounds;
  destruct lb as [lb|]; destruct ub as [ub|];
  try rewrite split_below_spec; try rewrite split_above_spec; split; intros H;
  repeat rewrite <- sint.mem_spec in H;
  repeat rewrite <- Z.leb_le in H; normalize_bool_in H;
  repeat rewrite <- not_true_iff_false in H;
  repeat rewrite sint.mem_spec in H; repeat rewrite Z.leb_le in H; try easy; destruct_ands; repeat split; try easy.
  - destruct H22; try contradiction; now destruct H.
  - now destruct H22.
  - now destruct H22.
Qed.

Lemma tighten_holes_bounds_const :
  forall dom domt,
    domt = tighten_holes dom
      ->
    (d_holes domt) = holes_in_bounds (d_lb dom) (d_ub dom) (d_holes dom)
      /\
    (d_ub domt) = (d_ub dom)
      /\
    (d_lb domt) = (d_lb dom).
Proof.
  intros dom domt.
  intros Htighten.
  unfold tighten_holes in Htighten.
  destruct domt as [lbt ubt holest].
  destruct dom as [lb ub holes].
  inversion Htighten; subst.
  simpl. repeat split; reflexivity.
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

Ltac destruct_or :=
  repeat match goal with
  | [ H: _ \/ _ |- _ ] =>
      let H1 := fresh H "_left" in
      let H2 := fresh H "_right" in
      destruct H as [H1 | H2]
  end.

Lemma le_ge :
  forall n m,
    n >= m <-> m <= n.
Proof. lia. Qed.

Lemma apply_holes_equiv :
  forall dom,
    dom_equiv dom (apply_holes_opt dom).
Proof.
  intros dom.
  unfold apply_holes_opt, option_map_flat.
  destruct dom as [dom|]; try reflexivity.
  unfold apply_holes.
  remember (tighten_holes dom) as domt.
  apply tighten_holes_bounds_const in Heqdomt.
  destruct Heqdomt as (Hholest & ut & lt).
  destruct dom as [lb ub holes]; simpl in *.
  unfold bounds_both_none, check_current_bound, option_map;
  destruct lb as [lb|]; destruct ub as [ub|]; simpl;
  try reflexivity; 
  try rewrite <- tighten_holes_equiv; simpl;
  rewrite tighten_holes_equiv; unfold tighten_holes;
  rewrite <- ut in *; rewrite <- lt in *;
  rewrite <- Hholest;
  destruct domt as [lbt ubt holest]; simpl in *;
  subst ubt; subst lbt; clear Hholest holes;
  rename holest into holes; try destruct_leb; simpl;
  unfold dom_equiv; intros y; unfold is_in_dom;
  try rewrite split_below_spec; try rewrite split_above_spec;
  split; intros H;
  repeat rewrite <- sint.mem_spec in H;
  repeat rewrite <- Z.leb_le in H; normalize_bool_in H;
  repeat rewrite <- not_true_iff_false in H;
  repeat rewrite sint.mem_spec in H; repeat rewrite Z.leb_le in H;
  try specialize (apply_holes_side_tightens (sint.elements holes) lb true) as Htightens_lb;
  try specialize (apply_holes_side_tightens (rev (sint.elements holes)) ub false) as Htightens_ub; try simpl in Htightens_ub; try simpl in Htightens_lb;
  destruct_ands;
  try (destruct_or; try contradiction; repeat split; try easy; lia).
  - assert (y >= apply_holes_side (sint.elements holes) lb true).
    { apply apply_holes_side_lb.
      - intros Hin.
        apply is_not_holes_to_list in H22. contradiction.
      - rewrite le_ge. assumption. }
    assert (y <= apply_holes_side (rev (sint.elements holes)) ub false).
    { apply apply_holes_side_ub.
      - rewrite <- in_rev. intros Hin. apply is_not_holes_to_list in H22. contradiction.
      - assumption. }
    repeat split; try lia.
    intros Hfalse.
    destruct Hfalse as [[Hin _] _].
    contradiction.
  - rewrite <- not_true_iff_false in Hleb.
    rewrite Z.leb_le in Hleb.
    assert (y >= apply_holes_side (sint.elements holes) lb true).
    { apply apply_holes_side_lb.
      - intros Hin.
        apply is_not_holes_to_list in H22. contradiction.
      - rewrite le_ge. assumption. }
    assert (y <= apply_holes_side (rev (sint.elements holes)) ub false).
    { apply apply_holes_side_ub.
      - rewrite <- in_rev. intros Hin. apply is_not_holes_to_list in H22. contradiction.
      - assumption. }
    lia.
  - assert (y >= apply_holes_side (sint.elements holes) lb true).
    { apply apply_holes_side_lb.
      - intros Hin.
        apply is_not_holes_to_list in H22. contradiction.
      - rewrite le_ge. assumption. }
    repeat split; now try rewrite <- le_ge.
  - assert (y <= apply_holes_side (rev (sint.elements holes)) ub false).
    { apply apply_holes_side_ub.
      - rewrite <- in_rev. intros Hin. apply is_not_holes_to_list in H22. contradiction.
      - assumption. }
    now repeat split.
Qed.

Lemma apply_holes_in_out :
  forall atoms dom,
    dom_equiv (apply_atomics_rec_opt atoms (apply_holes_opt dom)) (apply_atomics_rec_opt atoms dom).
Proof.
  intros atoms dom.
  unfold dom_equiv.
  intros y.
  specialize (apply_holes_equiv dom y) as Heqv.
  repeat rewrite dom_effect_rec.
  rewrite Heqv. reflexivity.
Qed.

(* Definition atoms_for_dom (atoms : list Atomic) (dom : option Domain) :=
  dom_equiv (apply_atomics_rec_opt atoms dom) ()
 *)

(* Definition atoms_for_dom (atoms : list Atomic) (dom : option Domain) :=
  forall y,
    is_in_dom y dom
      <->
     *)

Lemma dom_effect_atomics :
  forall atoms y dom,
    is_in_dom y (apply_atomics atoms dom)
      <->
    is_in_dom y dom /\ (forall a, In a atoms -> atomic_holds y a).
Proof.
  intros atoms y dom.
  unfold apply_atomics.
  specialize (apply_holes_equiv (apply_atomics_rec_opt atoms dom) y) as Heqv.
  rewrite <- Heqv.
  apply dom_effect_rec.
Qed.
  
   
Lemma apply_atomics_app :
  forall atoms atoms' dom,
  dom_equiv (apply_atomics (atoms ++ atoms') dom) (apply_atomics atoms' (apply_atomics atoms dom)).
Proof.
  intros atoms atoms' dom.
  unfold apply_atomics.
  repeat rewrite <- apply_holes_equiv.
  rewrite apply_holes_in_out.
  unfold apply_atomics_rec_opt.
  unfold option_map_flat.
  destruct dom as [dom|]; try reflexivity.
  unfold apply_atomics_rec.
  repeat rewrite fold_left_error_as_fold_left.
  rewrite fold_left_app.
  rewrite <- fold_left_error_as_fold_left.
  destruct (fold_left_error apply_atomic atoms dom) eqn:Hatoms.
  - rewrite <- fold_left_error_as_fold_left. reflexivity.
  - induction atoms'.
    + simpl. reflexivity.
    + simpl. apply IHatoms'.
Qed.

Lemma apply_atomics_app_swap :
  forall atoms atoms' dom,
  dom_equiv (apply_atomics (atoms ++ atoms') dom)
  (apply_atomics (atoms' ++ atoms) dom).
Proof.
  intros atoms atoms' dom.
  unfold dom_equiv. intros y.
  repeat rewrite dom_effect_atomics.
  setoid_rewrite in_app_iff.
  setoid_rewrite or_comm at 1.
  reflexivity.
Qed.

Instance apply_atomics_proper : 
  Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful dom_equiv dom_equiv)) apply_atomics.
Proof.
  intros atoms atoms' Hatoms d1 d2 Heqv.
  subst atoms'.
  unfold dom_equiv.
  intros y.
  repeat rewrite dom_effect_atomics.
  specialize (Heqv y).
  rewrite Heqv.
  reflexivity.
Defined.


  (* apply apply_holes_side_lb  in 
  3: { specialize repeat split; try rewrite <- le_ge. }
  try enough (y >= apply_holes_side (sint.elements holes) lb true) by (destruct_or; try contradiction; repeat split; try easy; lia);
  try enough (y <= apply_holes_side (rev (sint.elements holes)) ub false) by (destruct_or; try contradiction; repeat split; try easy; lia);
  try apply apply_holes_side_lb;
  try apply apply_holes_side_ub;
  try rewrite <- in_rev.
  1
  try lia.
  6: { apply apply_holes_side with (up := true). }
    - destruct_or; try contradiction; repeat split; try easy; lia. }

  
 *)


Open Scope Z_scope.

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

(* Lemma check_holds_implies :
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
Qed. *)
