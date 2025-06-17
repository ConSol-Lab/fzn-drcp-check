Require Import Coq.ZArith.ZArith.
Require Import String.
Require Import Coq.Lists.List.
Require Import Bool.
Require Import Lia.
Require Import Coq.Structures.Orders.
Require Checker.Utility.
Import Utility.ListEx.
Import Utility.ListInd.
Import Utility.Sets.
Import Utility.ZRange.
Import Utility.Tactics.
Import Utility.SortedEx.
Require Import Checker.Zext.
Require Import Program.Basics.
Require Import Sorting.Sorted.
Require Checker.Spec.
Import Spec.ProofFacts.

Open Scope Z_scope.

(** This file contains general reasoning about domains using a holes-based representation of domains. It purposefully makes no mention of variables. *)

(** The most important definitions in this file are Atomic, Domain, `apply_atomics`, `dom_equiv`, `dom_effect_atomics` and `check_holds`. *)

(** * Atomics *)
Section Atomics.
(** An atomic, short for atomic constraint, is a constraint on some value using the >=, <=, = and != operators. *)

(** Utility functions for defining particular atomic types easily. *)
Definition mk_atm_le (c : Z) :=
  {| atm_cmp := less_equal; atm_val := c |}.

Definition mk_atm_ge (c : Z) :=
  {| atm_cmp := greater_equal; atm_val := c |}.

Definition mk_atm_ne (c : Z) :=
  {| atm_cmp := not_equal; atm_val := c |}.

Definition mk_atm_eq (c : Z) :=
  {| atm_cmp := equal; atm_val := c |}.

Definition decide_atomic (x : Z) (a : Atomic) :=
  match a.(atm_cmp) with
  | less_equal => x <=? a.(atm_val)
  | greater_equal => x >=? a.(atm_val)
  | equal => x =? a.(atm_val)
  | not_equal => negb (x =? a.(atm_val))
  end.

Lemma decide_atomic_prop : forall (x : Z) (a : Atomic),
  decide_atomic x a = true <-> atomic_holds x a.
Proof.
  intros x a.
  unfold decide_atomic, atomic_holds.
  remember (atm_val a) as v.
  destruct (atm_cmp a) ; intros.
  - apply Z.leb_le.
  - apply Z.geb_ge.
  - apply Z.eqb_eq.
  - split ; intros.
    + apply negb_true_iff in H.
      apply Z.eqb_neq, H.
    + apply negb_true_iff, Z.eqb_neq, H.
Qed.

Definition negate_atomic (a : Atomic) :=
  match a with
  | mkAtm cmp c =>
    match cmp with
    | less_equal => mkAtm greater_equal (c + 1)
    | greater_equal => mkAtm less_equal (c - 1)
    | equal => mkAtm not_equal c
    | not_equal => mkAtm equal c
    end
  end.

Lemma negate_atomic_not :
  forall n a,
    atomic_holds n a
      <->
    ~ atomic_holds n (negate_atomic a).
Proof.
  intros n a.
  destruct a as [cmp c].
  unfold atomic_holds, negate_atomic.
  simpl. destruct cmp; simpl; lia.
Qed.

End Atomics.

(** * Domains *)
Section Domains.

(** A domain consists of a lower bound, upper bound and a set of holes (see the Sets module in Utility, `sint` is a custom name short for `set_int`). We use the [Zext] type to represent bounds, meaning that a domain can be unbounded or bounded on only one side. Note that it is possible to represent empty domains. *)
Record Domain := mkDom {
  d_lb : Zext;
  d_ub : Zext;
  d_holes : sint.t
}.

Open Scope Zext_scope.
(** This defines the semantics of a domain. Here we see why it is nice to use Zext, they look just like normal, there is no matching on options or special cases for upper and lower bounds. *)
Definition is_in_dom (y : Z) (dom : Domain) :=
  d_lb dom <= zz y
    /\
  zz y <= d_ub dom
    /\
  ~ sint.In y (d_holes dom).

(** We define a notion of equivalency between domains based on two domains containing the same elements, i.e. they would be equal if they were seen as sets. A 'logical domain' is an equivalence class based on this relation. *)
Definition dom_equiv dom1 dom2 :=
  forall y, is_in_dom y dom1 <-> is_in_dom y dom2.

#[export] Instance is_in_dom_Proper :
  Proper (eq ==> dom_equiv ==> iff) is_in_dom.
Proof.
  intros y y' Hyy' dom dom'.
  subst y'.
  unfold dom_equiv. intros H.
  rewrite H.
  reflexivity.
Qed.

(** We register it as an equivalence relation to allow lots of nice rewriting. *)
#[export] Instance dom_equiv_equiv : RelationClasses.Equivalence dom_equiv.
Proof.
  constructor.
  - intros x. unfold dom_equiv. reflexivity.
  - intros x y. unfold dom_equiv; easy.
  - intros x y z. unfold dom_equiv. 
    intros H1 H2.
    intros n.
    rewrite H1. rewrite <- H2. reflexivity.
Qed.

Definition eqb (lhs : Domain) (rhs : Domain) :=
  let same_lb := (Zext.eqb (lhs.(d_lb)) (rhs.(d_lb)))
  in
  let same_ub := (Zext.eqb (lhs.(d_ub)) (rhs.(d_ub)))
  in
  let same_holes := sint.equal (lhs.(d_holes)) (rhs.(d_holes))
  in
  same_lb && same_ub && same_holes.

Lemma eqb_eq : forall lhs rhs, eqb lhs rhs = true -> dom_equiv lhs rhs.
Proof.
  intros lhs rhs.
  destruct lhs.
  destruct rhs.
  unfold eqb.
  simpl.
  intros.
  apply andb_prop in H.
  destruct H as [H Eholes].
  apply andb_prop in H.
  destruct H as [Elb Eub].
  apply Zext.eqb_eq in Elb.
  apply Zext.eqb_eq in Eub.
  apply sint_prps.Dec.F.equal_2 in Eholes.
  rewrite Elb, Eub.
  unfold dom_equiv, is_in_dom.
  intros.
  unfold sint.Equal in Eholes.
  split ; intros ; destruct H as [P Q] ; destruct Q as [Q R] ;
  simpl ; simpl in P ; simpl in Q ; simpl in R ;
  split ; try assumption ; split ; try assumption ;
  unfold not ; intros ; apply Eholes in H ; contradiction.
Qed.

(** A domain is consistent when there is at least one element inside it. This rules out many weird domains such as having negative infinity as upper bound. *)
Definition dom_consistent (dom : Domain) :=
  exists y,
    is_in_dom y dom.

#[export] Instance dom_consistent_Proper :
  Proper (dom_equiv ==> iff) dom_consistent.
Proof.
  intros dom dom'.
  unfold dom_consistent, dom_equiv.
  intros Hequiv.
  setoid_rewrite Hequiv.
  reflexivity.
Qed.

(** The initial domain contains all elements. It simplifies quite nicely, [is_in_dom y initial_dom] is provable with just the `easy` tactic. *)
Definition initial_dom := mkDom neg_inf pos_inf sint.empty.

End Domains.

(** * ApplyAtomic *)
Section ApplyAtomic.
(** This section defines the [apply_atomic] operation and proves that it does what we want it to do: ensure that all values in the domain with the applied atomic obey the atomic. *)

(** Again it is nice we use Zext because we can get the definitions and specs for max/min for free and this makes the definition very simple. *)
Definition update_ub (value : Z) (dom : Domain) :=
  mkDom dom.(d_lb) (Zext.min (zz value) dom.(d_ub)) dom.(d_holes).

Definition update_lb (value : Z) (dom : Domain) :=
  mkDom (Zext.max dom.(d_lb) (zz value)) dom.(d_ub) dom.(d_holes).

Definition punch_hole (value : Z) (dom : Domain) :=
  mkDom dom.(d_lb) dom.(d_ub) (sint.add value dom.(d_holes)).

Definition apply_atomic (dom : Domain) (atomic : Atomic) :=
  match (atm_cmp atomic) with
  | less_equal => update_ub atomic.(atm_val) dom
  | greater_equal => update_lb atomic.(atm_val) dom  
  | equal => update_ub atomic.(atm_val) (update_lb atomic.(atm_val) dom)  
  | not_equal => punch_hole atomic.(atm_val)  dom
   end.

(** The proofs are simple, destruct everything and then everything simplifies to something trivial or provable by lia since only integers are left. We make heavy use of the Zext tactics. *)
Lemma update_ub_spec :
  forall dom value y,
    is_in_dom y dom /\ (y <= value)%Z <-> is_in_dom y (update_ub value dom).
Proof.
  intros dom value y.
  unfold is_in_dom, update_ub; simpl.
  repeat split; try easy; destruct_ands;
  destruct_minmax; compare_to_ops; try easy;
  destruct (d_ub dom); zext_as_z; try zext_easy; lia.
Qed.

Lemma update_lb_spec :
  forall dom value y,
    is_in_dom y dom /\ (y >= value)%Z <-> is_in_dom y (update_lb value dom).
Proof.
  intros dom value y.
  unfold is_in_dom, update_lb; simpl.
  repeat split; try easy; destruct_ands;
  destruct_minmax; compare_to_ops; try easy;
  destruct (d_lb dom); zext_as_z; try zext_easy; lia.
Qed.

(** Helper lemma. *)
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

Lemma punch_hole_spec :
  forall dom value y,
    is_in_dom y dom /\ y <> value <-> is_in_dom y (punch_hole value dom).
Proof.
  intros dom value y.
  unfold is_in_dom, punch_hole; simpl.
  rewrite sint.add_spec. 
  rewrite not_in_add.
  repeat split; try easy.
Qed.

(** Now the actual spec. *)
Lemma apply_atomic_spec :
  forall dom atomic y,
    is_in_dom y dom /\ atomic_holds y atomic <-> is_in_dom y (apply_atomic dom atomic).
Proof.
  intros dom atomic y.
  unfold atomic_holds, apply_atomic.
  destruct atm_cmp.
  - apply update_ub_spec.
  - apply update_lb_spec.
  - rewrite <- update_ub_spec. rewrite <- update_lb_spec.
    unfold is_in_dom.
    repeat split; destruct_ands; try easy; lia.
  - apply punch_hole_spec.
Qed.

End ApplyAtomic.

(** * ZFlip *)
Declare Scope ZFlip_scope.
Module ZFlip.
(** In the next section, we will prove some things that is almost entirely symmetric for the upper and lower bound case. To avoid repeating the proofs, we parametrize the standard <= < over a 'sign' that can flip the order. *)
Local Open Scope ZFlip_scope.

Inductive Sign :=
| plus
| min.

Definition le_flip (sign : Sign) x y :=
  match sign with
  | plus => Z.le x y
  | min => Z.le y x
  end.

Definition lt_flip (sign : Sign) x y :=
  match sign with
  | plus => Z.lt x y
  | min => Z.lt y x
  end.

Definition ltb_flip (sign : Sign) x y :=
  match sign with
  | plus => Z.ltb x y
  | min => Z.ltb y x
  end.

Definition sign_to_z (sign : Sign) : Z :=
  match sign with
  | plus => 1
  | min => -1
  end.

Ltac simpl_sign :=
  match goal with
  | [ sign : Sign |- _ ] =>
    unfold sign_to_z in *; unfold le_flip in *; unfold lt_flip in *; unfold ltb_flip in *; destruct sign
  end.

Notation "x <=[ z ] y" := (le_flip z x y) (at level 70) : ZFlip_scope.
Notation "x <[ z ] y" := (lt_flip z x y) (at level 70) : ZFlip_scope.
Notation "x <?[ z ] y" := (ltb_flip z x y) (at level 70) : ZFlip_scope.
Notation "x +<= y" := (le_flip plus x y) (at level 70) : ZFlip_scope.
Notation "x -<= y" := (le_flip min x y) (at level 70) : ZFlip_scope. 
 
End ZFlip.

Import ZFlip.

(** * Tighten (definitions and soundness, [dom_equiv]) *)
Section Tighten.
Local Open Scope Z_scope.
Local Open Scope ZFlip_scope.

(** This section introduces the functions used for tightening a domain. This section contains all the definitions and proofs actually used outside this file, since there only soundness is proved. See the section at the end for more details on the actual properties. The idea is that after applying this operation on the bounds, we can easily check whether an atomic holds and whether or not the domain is inconsistent. As mentioned, we parameterize over a 'sign' to avoid repeating proofs for an upper and lower bound case that are entirely symmetric. In most proofs, we only have to destruct the two cases in the leafs of the proof. *)

(** `last` here refers to the last bound we know holds. This bound is updated as the holes are traversed. We assume the holes are sorted. *)
Fixpoint tighten_with_holes (sign : Sign) (holes : list Z) (last : Z) : Z :=
  match holes with
  | nil => last
  | h :: holes' =>
    match (h =? last) with
    | true => tighten_with_holes sign holes' (last + sign_to_z sign)
    | false => last
    end
  end.

(** This says that if a value obeys some bound, that after tightening that bound, the value still obeys it. *)
Lemma tighten_with_holes_sound :
  forall sign y holes last,
    ~ In y holes
      ->
    last <=[sign] y
      ->
    tighten_with_holes sign holes last <=[sign] y.
Proof.
  intros sign y. induction holes as [|h holes' IH]. 
  - intros last Hnin Hy.
    simpl. exact Hy.
  - intros last Hnotholes' Hy.
    assert (~ In y holes' /\ y <> h) as [Hnotholes Hynh].
    {
      split.
      - intros Hin. apply Hnotholes'.
        right. exact Hin.
      - intros Hyh. subst y. apply Hnotholes'. 
        left. reflexivity.
    }
    clear Hnotholes'. simpl.
    destruct (h =? last)%Z eqn:Hh.
    + apply IH; try assumption.
      simpl_sign; lia.  
    + exact Hy.
Qed.

Lemma tighten_holes_monotonic :
  forall sign (holes : list Z) (last : Z), 
    last <=[sign] tighten_with_holes sign holes last.
Proof.
  induction holes as [| h holes' IH].
  - intros last. simpl. simpl_sign; lia.
  - intros last. simpl.
    destruct (h =? last)%Z eqn:Hh.
    + specialize (IH (last + (sign_to_z sign))). 
      simpl_sign; lia.
    + simpl_sign; lia.
Qed.

Open Scope Z_scope.
(** After tightening once, we do not remove holes since that can be quite expensive. This means we can have holes that are already implied by bounds. In order for the tighten function to do anything and simplify the proofs, we only take the elements that are at least as large as the bound. *)
Fixpoint elements_bound (sign : Sign) (bound : Z) (values : list Z) :=
  match values with
  | nil => values
  | v :: values' =>
    match (v <?[sign] bound) with
    | true => elements_bound sign bound values'
    | false => values
    end
  end.

Lemma elements_bound_in :
  forall sign bound values n,
    In n (elements_bound sign bound values)
      ->
    In n values.
Proof.
  intros sign.
  induction values.
  - intros n. now simpl.
  - intros n. simpl.
    destruct (a <?[sign] bound).
    + intros H. right. now apply IHvalues.
    + intros Hin. destruct Hin.
      * now left.
      * now right.
Qed.

(** This is the critical lemma used to prove that tightening does not change the logical domain. Since shows that, given some holes in a value's domain, a bound and it's tightened variant holding are equivalent. *)
Definition tighten_holes_equiv :
  forall sign bound holes y,
    bound <=[sign] y /\ ~ In y holes
      <->
    tighten_with_holes sign (elements_bound sign bound holes) bound <=[sign] y /\ ~ In y holes.
Proof.
  intros sign bound holes y.
  split; intros H.
  - split.
    + apply (tighten_with_holes_sound sign y).
      * destruct H as [_ Hnotin].
        intros Hin.
        apply elements_bound_in in Hin.
        contradiction.
      * apply H.
    + apply H.
  - split.
    + destruct H as [Htighten _].
      specialize (tighten_holes_monotonic sign (elements_bound sign bound holes) bound) as Hmono.
      simpl_sign; lia.
    + apply H.
Qed.

(** Tighten lower bound of domain. *)
Definition tighten_lb (dom : Domain) : Domain :=
  match dom.(d_lb) with
  | zz lb =>
    if sint.mem lb dom.(d_holes)
      then 
        let new_lb := tighten_with_holes plus (elements_bound plus lb (sint.elements dom.(d_holes))) lb in
        mkDom (zz new_lb) dom.(d_ub) dom.(d_holes)
      else dom
  | _ => dom
  end.

Lemma tighten_lb_equiv :
  forall dom,
    dom_equiv dom (tighten_lb dom).
Proof.
  intros dom y.
  unfold is_in_dom.
  destruct dom as [lb ub holes]; simpl.
  unfold tighten_lb; simpl.
  destruct lb as [lb| |].
  2-3: simpl; reflexivity.
  destruct sint.mem.
  2: simpl; reflexivity.
  simpl.
  setoid_rewrite <- sint.elements_spec1.
  setoid_rewrite InA_eq_iff_In.
  remember (sint.elements holes) as holes'; clear Heqholes' holes.
  specialize (tighten_holes_equiv plus lb holes' y) as Hequiv.
  unfold le_flip in Hequiv.
  zext_as_z.
  setoid_rewrite <- and_assoc at 1.
  setoid_rewrite and_comm at 3.
  setoid_rewrite and_assoc at 1.
  rewrite Hequiv; clear Hequiv.
  now repeat split.
Qed.

(** Tighten upper bound of domain. *)
Definition tighten_ub (dom : Domain) : Domain :=
  match dom.(d_ub) with
  | zz ub =>
    if sint.mem ub dom.(d_holes)
      then 
        let new_ub := tighten_with_holes min (elements_bound min ub (rev (sint.elements dom.(d_holes)))) ub in
        mkDom dom.(d_lb) (zz new_ub) dom.(d_holes)
      else dom
  | _ => dom
  end.

Lemma tighten_ub_equiv :
  forall dom,
    dom_equiv dom (tighten_ub dom).
Proof.
  intros dom y.
  unfold is_in_dom.
  destruct dom as [lb ub holes]; simpl.
  unfold tighten_ub; simpl.
  destruct ub as [ub| |].
  2-3: simpl; reflexivity.
  destruct sint.mem.
  2: simpl; reflexivity.
  simpl.
  setoid_rewrite <- sint.elements_spec1.
  setoid_rewrite InA_eq_iff_In.
  setoid_rewrite in_rev.
  remember (rev (sint.elements holes)) as holes';
  setoid_rewrite <- Heqholes'; clear Heqholes' holes.
  specialize (tighten_holes_equiv min ub holes' y) as Hequiv.
  unfold le_flip in Hequiv.
  zext_as_z.
  rewrite Hequiv; clear Hequiv.
  now repeat split.
Qed.
End Tighten.

(** * Checking *)
Section CheckDomains.

(** This section describes two functions, [check_holds] and [dom_check_consistent] that are used to efficiently verify whether an atomic holds for a domain and whether a domain is empty, respectively. We do not prove that they actually decide those properties, since that is only the case when the domain is tight and we do not need that in proofs outside this file. *)

Open Scope Zext_scope.
(** For lower and upper bounds and equality: we only inspect the bounds, so that is very cheap. For a hole, we do need to do a membership test, but no complex logic otherwise. Note that if the domain is not tight, this might return false even when logically, the atomic does hold. *)
Definition check_holds (a : Atomic) (dom : Domain) : bool :=
  match a.(atm_cmp) with
  | greater_equal =>
    zz a.(atm_val) <=? dom.(d_lb)
  | less_equal =>
    dom.(d_ub) <=? zz a.(atm_val)
  | equal =>
    (dom.(d_ub) =? zz a.(atm_val))
      &&
    (dom.(d_lb) =? zz a.(atm_val))
  | not_equal =>
    (dom.(d_ub) <? zz a.(atm_val))
      ||
    (zz a.(atm_val) <? dom.(d_lb))
      ||
    (sint.mem a.(atm_val) dom.(d_holes))
  end.

(** When [check_holds] returns true, we definitely know the atomic holds! *)
Lemma check_holds_implies :
  forall dom y a,
  is_in_dom y dom
    ->
  check_holds a dom = true
    ->
  atomic_holds y a.
Proof.
  intros dom y a. 
  unfold is_in_dom, check_holds, atomic_holds.
  destruct atm_cmp.
  - rewrite Zext.leb_le; intros.
    enough (zz y <= zz (atm_val a)) by easy.
    destruct H as (_ & H & _).
    (* I really don't know why order tactic can't solve this... *)
    transitivity (d_ub dom); assumption.
  - rewrite Zext.leb_le; intros.
    enough (zz (atm_val a) <= zz y) by (zext_as_z; lia).
    destruct H as (H & _ & _).
    transitivity (d_lb dom); assumption.
  - rewrite andb_true_iff.
    setoid_rewrite Zext.eqb_eq; intros.
    enough (zz y = zz (atm_val a)).
    { inversion H1. reflexivity. }
    destruct H as (Hlb & Hub & _).
    destruct H0 as (Hubeq & Hlbeq).
    destruct dom; simpl in *; subst.
    rewrite Zext.eq_is_le_ge; compare_to_ops;
    normalize_not_zext. easy.
  - repeat rewrite orb_true_iff.
    setoid_rewrite Zext.ltb_lt.
    intros H.
    intros [[Hub | Hlb] | Hmem].
    + destruct_Zext; zext_as_z; lia.
    + destruct_Zext; zext_as_z; lia.
    + rewrite sint.mem_spec in Hmem.
      intros Heq; subst y; easy.
Qed.

Open Scope Zext_scope.
Definition consistent_bounds (dom : Domain) :=
  dom.(d_lb) <= dom.(d_ub).

(** Inspecting the bounds allows us to do an easy check to see if the domain is inconsistent. Again, if the domain is tight, this actually decides consistency! *)
Definition dom_check_consistent (dom : Domain) : bool :=
  match dom.(d_lb), dom.(d_ub) with
  | pos_inf, _ => false
  | _, neg_inf => false
  | _, _ => dom.(d_lb) <=? dom.(d_ub)
  end.

(** If it returns false, we know the domain is inconsistent. *)
Lemma dom_inconsistent_if_checked_false :
  forall dom,
  dom_check_consistent dom = false
    ->
  ~ dom_consistent dom.
Proof.
  intros dom. 
  unfold dom_check_consistent, dom_consistent, is_in_dom.
  intros Hcheck.
  assert (d_lb dom = pos_inf \/ d_ub dom = neg_inf \/ d_ub dom < d_lb dom) as H.
  {
    destruct (d_lb dom); destruct (d_ub dom);
    try solve_disjunction.
    right. right. rewrite <- not_true_iff_false in Hcheck.
    rewrite Zext.leb_le in Hcheck. zext_as_z. lia.
  }
  clear Hcheck.
  destruct H as [Hlbpos | [Hubneg | Hincons]].
  - rewrite Hlbpos. now intros (y & Hneg & _).
  - rewrite Hubneg. now intros (y & _ & Hneg & _).
  - intros (y & Hlb & Hub & Hholes).
    destruct (d_ub dom); destruct (d_lb dom);
    zext_as_z; try easy; lia.
Qed.
  
End CheckDomains.

(** * [apply_atomics] *)
Section ApplyAtomics.
(** This section describes the domain operations we actually use in practice: applying multiple atomics at once (e.g. when checking a nogood, we assume its premises), tightening the domain at once (after applying multiple atomics). We also define [apply_atomic_tighten], which when given a tight and consistent domain always returns a tight and consistent domain (returning None if the domain is now inconsistent). The latter would be used when e.g. applying the consequent of an inference during nogood checking, as we need to check the premises of another inference afterwards, or we want to know we are done since it is now inconsistent. It is a bit more efficient by only tightening what is necessary. *)
Definition apply_atomics (atoms : list Atomic) (dom : Domain) :=
  fold_left apply_atomic atoms dom.

(** This allows us to transform applying multiple atomics to just a statement about which atomics, from which a corollary is that the order does not matter. *)
Lemma dom_effect_atomics :
  forall atoms y dom,
    is_in_dom y (apply_atomics atoms dom)
      <->
    is_in_dom y dom /\ (forall a, In a atoms -> atomic_holds y a).
Proof.
  unfold apply_atomics.
  induction atoms.
  - intros y dom. simpl. split; intros H.
    * split; easy.
    * apply H.
  - intros y dom.
    simpl. rewrite IHatoms.
    rewrite <- apply_atomic_spec.
    split; intros H.
    + destruct H as ((Hydom & Haholds) & Hinholds).
      split; try easy.
      intros a' [Ha | Hin].
      * subst. exact Haholds.
      * apply Hinholds. exact Hin.
    + destruct H as (Hydom & Hinholds).
      split; [split|]; try easy.
      * apply Hinholds. left. reflexivity.
      * intros a' Hin.
        apply Hinholds. right. exact Hin.
Qed. 

Definition tighten_dom (dom : Domain) :=
  tighten_ub (tighten_lb dom).

(** This finally proves that tightening just preserves the logical domain. This is used a lot when we just care about domain equivalency and not about whether domains are tight. *)
Lemma tighten_equiv :
  forall dom,
    dom_equiv dom (tighten_dom dom).
Proof.
  intros dom. unfold tighten_dom.
  setoid_rewrite <- tighten_ub_equiv.
  setoid_rewrite <- tighten_lb_equiv.
  reflexivity.
Qed.

Definition apply_atomic_tighten (dom : Domain) (atomic : Atomic) :=
  let dom_applied := apply_atomic dom atomic in
  if dom_check_consistent dom_applied
    then
      let dom_tight := 
        match (atm_cmp atomic) with
        | less_equal => tighten_ub dom_applied
        | greater_equal => tighten_lb dom_applied
        | _ => tighten_dom dom_applied
        end in
      if dom_check_consistent dom_tight
        then Some dom_tight
        else None
    else None.

(** This shows that apply_atomic_valid modifies the logical domain in the the same as [apply_atomic] if it returns Some, and that when it returns None it is indeed inconsistent. *)
Lemma apply_atomic_tighten_valid :
  forall dom atomic,
    match apply_atomic_tighten dom atomic with
    | Some dom' => dom_equiv dom' (apply_atomic dom atomic)
    | None => ~ dom_consistent (apply_atomic dom atomic)
    end.
Proof.
  intros dom atomic.
  destruct apply_atomic_tighten as [dom'|] eqn:Htighten.
  - unfold apply_atomic_tighten in Htighten.
    destruct dom_check_consistent; try discriminate.
    destruct atm_cmp eqn:Hcmp; simpl; destruct dom_check_consistent eqn:Hcheck; try discriminate;
    inversion Htighten; subst; clear Htighten.
    + rewrite <- tighten_ub_equiv. reflexivity.
    + rewrite <- tighten_lb_equiv. reflexivity.
    + rewrite <- tighten_equiv. reflexivity.
    + rewrite <- tighten_equiv. reflexivity.  
  - unfold apply_atomic_tighten in Htighten.
    destruct dom_check_consistent eqn:Hconsistent_applied.
    + destruct atm_cmp; destruct dom_check_consistent eqn:Hconsistent_tight in Htighten; try discriminate.
      * rewrite tighten_ub_equiv. apply dom_inconsistent_if_checked_false.
        exact Hconsistent_tight.
      * rewrite tighten_lb_equiv. apply dom_inconsistent_if_checked_false.
        exact Hconsistent_tight.
      * rewrite tighten_equiv.
        apply dom_inconsistent_if_checked_false.
        exact Hconsistent_tight.
      * rewrite tighten_equiv.
        apply dom_inconsistent_if_checked_false.
        exact Hconsistent_tight.
    + apply dom_inconsistent_if_checked_false.
      exact Hconsistent_applied.
Qed.

End ApplyAtomics.

Section Tests.
Definition show_dom (dom : Domain) :=
  match dom with
  | mkDom lb ub holes =>
    (lb, ub, sint.elements holes)
  end.

Definition dom1 := (mkDom (zz 0) (zz 8) (sint.build (0 :: 9 :: 5 :: 1 :: 11 :: 7 :: 8 :: 9 :: 2 :: nil))).

(* Compute show_dom dom1. *)
(** Since we have 0,1,2 we expect >= 3. Since 7,8 we expect <= 6. We also have 5 so we expect it to be preserved. *)
(* Compute (show_dom (tighten_dom dom1)). *)

Definition dom2 := (mkDom (zz (-3)) (zz 1) (sint.build (-3 :: -4 :: -1 :: -2 :: 0 :: 1 :: 9 :: -5 :: 2 :: 3 :: nil))).
(* Since the lb <= ub, it will not show that it is inconsistent (even though it is). *)
(* Compute dom_check_consistent dom2. *)
(* But after tightening, it should have become invalid *)
Definition dom2_tight := tighten_dom dom2.
(* Compute (show_dom dom2_tight). *)
(* Compute dom_check_consistent dom2_tight. *)
End Tests.

(** * Tighten (decide [atomic_holds] and [dom_consistent] when tight)  *)
Section TightenComplete.

(** Until now, we have only shown that tighten preserves the logical domain. However, as the name implies, the tighten operation makes a domain become 'tightened'. When a domain is tightened, it has no holes at its bounds and these bounds are therefore as tight as they can be. Furthermore, in this tightened state, [dom_check_consistent] actually decides consistency of the domain. Furthermore, [check_holds] is able to decide an atomic holds. *)

(** *** Tightened effects  *)

Open Scope Zext_scope.
Local Open Scope ZFlip_scope.

Definition lb_tightened (dom: Domain) :=
  match dom.(d_lb) with
  | zz lb => ~ sint.In lb dom.(d_holes)
  | _ => True
  end.

Definition ub_tightened (dom: Domain) :=
  match dom.(d_ub) with
  | zz ub => ~ sint.In ub dom.(d_holes)
  | _ => True
  end.

Definition dom_tightened (dom : Domain) :=
  lb_tightened dom /\ ub_tightened dom.

(** When a domain is tight, [dom_check_consistent] actually decides consistency! *)
Lemma dom_consistent_iff_checked :
  forall dom,
    dom_tightened dom ->
    dom_check_consistent dom = true <-> dom_consistent dom.
Proof.
  intros dom [Htight_lb Htight_ub].
  split.
  2: {
    destruct (dom_check_consistent dom) eqn:Hcheck; try easy.
    intros Hconsistent. exfalso.
    enough (~ dom_consistent dom) by contradiction; clear Hconsistent.
    apply dom_inconsistent_if_checked_false, Hcheck.
  }
  unfold lb_tightened in Htight_lb; unfold ub_tightened in Htight_ub.
  unfold dom_check_consistent, dom_consistent, is_in_dom.
  destruct (d_ub dom) as [ub| |]; destruct (d_lb dom) as [lb| |]; repeat split; try easy; try rewrite Zext.leb_le.
  - intros H. 
    exists lb; repeat split; try easy.
  - intros _.
    exists ub; repeat split; try easy.
  - intros _.
    exists lb; repeat split; try easy.
  - intros _.
    specialize (exists_sint_lb (d_holes dom) Z0) as (y' & _ & H).
    exists (y' - 1).
    repeat split; try easy.
    apply H. lia.
Qed.

Definition ub_not_neg_inf (dom : Domain) :=
  dom.(d_ub) <> neg_inf.

(** We prove here for just the lower bound case for lack of time. *)
Lemma tightened_then_checks_lb :
  forall dom lb,
    consistent_bounds dom
      ->
    ub_not_neg_inf dom
      ->
    lb_tightened dom
      ->
    (* That means that this bound is valid *)
    (forall y, is_in_dom y dom -> (lb <= y)%Z)
      ->
    zz lb <=? dom.(d_lb) = true.
Proof.
  intros dom lb.
  unfold is_in_dom, lb_tightened, consistent_bounds, ub_not_neg_inf.
  intros Hconsistent Hubnotneginf Htightened Hlb.
  rewrite Zext.leb_le.
  destruct (d_lb dom) as [dlb| |] eqn:Hlbdestr.
  - specialize (Hlb dlb).
    zext_as_z.
    compare_to_ops.
    enough (lb <= dlb)%Z by lia.
    apply Hlb.
    repeat split.
    + lia.
    + destruct (d_ub dom) as [dub| |];
      zext_as_z; zext_easy.
    + exact Htightened.
  - exfalso.
    enough (exists n, n < lb /\ lb <= n)%Z.
    { destruct H. lia. }
    destruct (exists_sint_lb (d_holes dom) lb) as (hlb & Hhlblb & Hhlb).
    destruct (d_ub dom) as [dub| |].
    + exists ((Z.min dub hlb) - 1).
      split.
      * lia.
      * apply Hlb. repeat split.
        -- zext_as_z; zext_easy.
        -- zext_as_z; lia.
        -- apply Hhlb. lia.
    + contradiction.
    + exists (hlb - 1).
      split.
      * lia.
      * apply Hlb. repeat split.
        -- zext_easy.
        -- zext_easy.
        -- apply Hhlb.
          lia.
  - zext_easy.
Qed.

(* Lemma tightened_then_checks :
  forall dom a,
    dom_consistent dom
      ->
    dom_tightened dom
      ->
    (* That means that this bound is valid *)
    (forall y, is_in_dom y dom -> atomic_holds y a)
      <->
    check_holds a dom = true.
Proof.
  intros dom a Hconsistent Htight.
  split.
  2: { intros. apply check_holds_implies with (dom := dom); assumption. }
  unfold dom_consistent in Hconsistent.
  unfold dom_tightened, lb_tightened, ub_tightened in Htight.
  destruct Hconsistent as (y & Hdom).
  unfold check_holds, atomic_holds.
  unfold is_in_dom in *.
  destruct dom as [lb ub holes];
  destruct a as [cmp value]; simpl in *.
  destruct cmp eqn:Hcmp.
  - rewrite Zext.leb_le.
    destruct ub as [ub| |].
    + intros Hbound.
      specialize (Hbound ub).
      zext_as_z.
      apply Hbound.
      split; try easy.
      destruct lb; try easy.
      zext_as_z; lia.
    + zext_easy.
    + intros Hbound.
      exfalso.
      enough (exists n, value < n /\ n <= value)%Z.
      { destruct H. lia. }
      destruct (exists_sint_ub holes value) as (hvalue & Hhvalueub & Hhvalue).
      destruct lb as [lb| |].
      * exists ((Z.min dub hlb) - 1).
        split.
        * lia.
        * apply Hlb. repeat split.
          -- zext_as_z; zext_easy.
          -- zext_as_z; lia.
          -- apply Hhlb. lia.
      + contradiction.
      + exists (hlb - 1).
        split.
        * lia.
        * apply Hlb. repeat split.
          -- zext_easy.
          -- zext_easy.
          -- apply Hhlb.
            lia.

       *)


(** *** Tighten tightens  *)
(** Here, we actually prove that the tighten operations we defined actually make the domain tight. For this, we need that the holes are sorted. *)

Open Scope Z_scope.

Lemma elements_bound_in_iff : 
  forall sign bound values n,
    Sorted (lt_flip sign) values
      ->
    In n (elements_bound sign bound values)
      <->
    In n values /\ bound <=[sign] n.
Proof.
  intros sign bound. induction values.
  { intros n Hsorted; try easy. }
  intros n Hsorted.
  inversion Hsorted; subst a0 l; clear H2.
  specialize (IHvalues n H1); clear H1.
  apply Sorted_StronglySorted in Hsorted.
  2: { simpl_sign; intro; lia. }
  simpl. destruct (a <?[sign] bound) eqn:Hlt;
  try rewrite IHvalues; repeat split; try easy.
  - now right.
  - destruct H as [[Han | Hin] Hbound].
    + subst a. simpl_sign; lia.
    + apply Hin.
  - rewrite <- not_true_iff_false in Hlt. 
    destruct H as [Han | Hin].
    + subst a.
      simpl_sign; lia.
    + inversion Hsorted; subst a0 l.
      rewrite Forall_forall in H2.
      specialize (H2 n Hin).
      simpl_sign; lia.
Qed.

Lemma elements_bound_sorted : 
  forall sign bound values,
    Sorted (lt_flip sign) values
      ->
    Sorted (lt_flip sign) (elements_bound sign bound values).
Proof.
  intros sign bound. induction values; try easy.
  simpl. intros H.
  inversion H; subst l a0.
  specialize (IHvalues H2).
  destruct (a <?[sign] bound) eqn:Hlt.
  - apply IHvalues.
  - apply Sorted_cons; assumption.
Qed.

Lemma tighten_holes_spec :
  forall sign holes last,
    StronglySorted (lt_flip sign) holes
      ->
    (forall h, In h holes -> last <=[sign] h)
      ->
    ~ In (tighten_with_holes sign holes last) holes.
Proof.
  intros sign.
  induction holes as [|h holes' IH].
  - intros last Hsorted Hlast. simpl.
    easy.
  - intros last Hsorted Hlast. 
    inversion Hsorted; subst a l;
    rewrite Forall_forall in H2; clear Hsorted;
    rename H1 into Hsorted'; rename H2 into Hhlt.
    simpl. destruct (h =? last) eqn:Hh.
    + rewrite Z.eqb_eq in Hh; subst last.
      intros [Hhis | Hin].
      * clear -Hhis.
        specialize (tighten_holes_monotonic sign holes' (h + sign_to_z sign)) as H.
        simpl_sign; lia.
      * assert (forall h', In h' holes' -> h + (sign_to_z sign) <=[sign] h').
        { intros h' Hin'. specialize (Hhlt h' Hin').
         simpl_sign; lia. }
        specialize (IH (h + (sign_to_z sign)) Hsorted' H).
        contradiction.
    + intros [Hhlast | Hlastin].
      * rewrite Z.eqb_neq in Hh; subst h; contradiction.
      * specialize (Hhlt last Hlastin).
        assert (In h (h :: holes')) by (left; reflexivity);
        specialize (Hlast h H); clear H.
        simpl_sign; lia.
Qed.

Lemma tighten_lb_tightens :
  forall dom dom',
    dom' = tighten_lb dom 
      ->
    lb_tightened dom'.
Proof.
  intros dom dom'.
  intros Hdom'; subst dom'.
  unfold tighten_lb, lb_tightened.
  destruct (d_lb dom) eqn:Hdlb; simpl.
  2: { rewrite Hdlb. reflexivity. }
  2: { rewrite Hdlb. reflexivity. }
  destruct sint.mem eqn:Hmem.
  2: { rewrite Hdlb. rewrite <- sint.mem_spec.
    rewrite not_true_iff_false. exact Hmem. }
  simpl.
  rewrite <- sint.elements_spec1.
  rewrite InA_eq_iff_In.
  remember (sint.elements (d_holes dom)) as holes.
  specialize (sint.elements_spec2 (d_holes dom)) as Hsort; fold Z.lt in Hsort.
  rewrite <- Heqholes in Hsort; clear -Hsort.
  intros H. remember (tighten_with_holes plus (elements_bound plus z holes) z) as z'. assert (z +<= z') as Hzz'.
  { subst z'. apply tighten_holes_monotonic.  }
  assert (In z' holes /\ z +<= z') as Hin by (split; assumption).
  rewrite <- elements_bound_in_iff in Hin; try assumption.
  enough (~ In z' (elements_bound plus z holes)) by easy.
  subst z'; clear -Hsort.
  apply tighten_holes_spec.
  - apply Sorted_StronglySorted.
    * intro. unfold lt_flip. lia.
    * apply elements_bound_sorted. exact Hsort.
  - intros h Hin. rewrite elements_bound_in_iff in Hin.
    * apply Hin.
    * exact Hsort.
Qed.

Lemma tighten_ub_tightens :
  forall dom dom',
    dom' = tighten_ub dom 
      ->
    ub_tightened dom'.
Proof.
  intros dom dom'.
  intros Hdom'; subst dom'.
  unfold tighten_ub, ub_tightened.
  destruct (d_ub dom) eqn:Hdub; simpl.
  2: { rewrite Hdub. reflexivity. }
  2: { rewrite Hdub. reflexivity. }
  destruct sint.mem eqn:Hmem.
  2: { rewrite Hdub. rewrite <- sint.mem_spec.
    rewrite not_true_iff_false. exact Hmem. }
  simpl.
  rewrite <- sint.elements_spec1.
  rewrite InA_eq_iff_In.
  specialize (sint.elements_spec2 (d_holes dom)) as Hsort; fold Z.lt in Hsort.
  apply Sorted_reverse in Hsort; unfold flip in Hsort.
  rewrite in_rev.
  remember (rev (sint.elements (d_holes dom))) as holes;
  setoid_rewrite <- Heqholes; setoid_rewrite <- Heqholes in Hsort; clear -Hsort.
  intros H. remember (tighten_with_holes min (elements_bound min z holes) z) as z'. assert (z -<= z') as Hzz'.
  { subst z'. apply tighten_holes_monotonic.  }
  assert (In z' holes /\ z -<= z') as Hin by (split; assumption).
  rewrite <- elements_bound_in_iff in Hin; try assumption.
  enough (~ In z' (elements_bound min z holes)) by easy.
  subst z'; clear -Hsort.
  apply tighten_holes_spec.
  - apply Sorted_StronglySorted.
    * intro. unfold lt_flip. lia.
    * apply elements_bound_sorted. exact Hsort.
  - intros h Hin. rewrite elements_bound_in_iff in Hin.
    * apply Hin.
    * exact Hsort.
Qed.

Lemma tighten_tightens :
  forall dom dom',
    dom' = tighten_dom dom
      ->
    dom_tightened dom'.
Proof.
  intros dom dom'. unfold tighten_dom.
  unfold dom_tightened.
  intros Hdom'. split.
  + subst. assert (lb_tightened (tighten_lb dom)).
    { apply tighten_lb_tightens with (dom := dom) (dom' := (tighten_lb dom)). reflexivity. }
    remember (tighten_lb dom) as dom'.
    remember (tighten_ub dom') as dom''.
    assert (d_lb dom'' = d_lb dom' /\ d_holes dom'' = d_holes dom') as [Hlb Hholes].
    {
      subst dom''. unfold tighten_ub.
      destruct (d_ub dom'); try destruct (sint.mem z (d_holes dom')); easy.
    }
    unfold lb_tightened.
    rewrite Hlb. rewrite Hholes.
    apply H.
  + apply tighten_ub_tightens with (dom := (tighten_lb dom)).
    exact Hdom'.
Qed.

Lemma lb_tightened_not_ub :
  forall lb ub ub' holes,
    lb_tightened (mkDom lb ub holes) <-> lb_tightened (mkDom lb ub' holes).
Proof.
  intros lb ub ub' holes.
  unfold lb_tightened; simpl. reflexivity.
Qed.

Lemma ub_tightened_not_lb :
  forall lb lb' ub holes,
    ub_tightened (mkDom lb ub holes) <-> ub_tightened (mkDom lb' ub holes).
Proof.
  intros lb lb' ub holes.
  unfold ub_tightened; simpl. reflexivity.
Qed.


Lemma apply_atomic_tighten_spec :
  forall dom atomic,
    dom_consistent dom
      ->
    dom_tightened dom
      ->
    match apply_atomic_tighten dom atomic with
    | Some dom' => 
      dom_tightened dom'
        /\
      dom_consistent dom'
        /\ 
      dom_equiv dom' (apply_atomic dom atomic)
    | None => ~ dom_consistent (apply_atomic dom atomic)
    end.
Proof.
  intros dom atomic Hconsistent Htightened.
  specialize (apply_atomic_tighten_valid dom atomic) as Hvalid.
  destruct apply_atomic_tighten as [dom'|] eqn:Htighten.
  - unfold apply_atomic_tighten in Htighten.
    destruct dom_check_consistent; try discriminate.
    destruct atm_cmp eqn:Hcmp; simpl; destruct dom_check_consistent eqn:Hcheck; try discriminate.
    + assert (dom_tightened dom').
      { split.
        - clear Hcheck Hconsistent.
          destruct dom as [lb ub holes].
          destruct dom' as [lb' ub' holes'].
          rewrite lb_tightened_not_ub with (ub' := ub).
          destruct Htightened as [Htightened _].
          enough (lb' = lb /\ holes' = holes).
          { destruct H; now subst. }
          inversion Htighten; clear Htighten.
          rename H0 into H.
          unfold apply_atomic in H; rewrite Hcmp in H.
          unfold tighten_ub, update_ub in H; simpl in H.
          destruct Zext.min; try now inversion H.
          destruct sint.mem; now inversion H.
        - inversion Htighten. subst; clear Htighten.
          apply tighten_ub_tightens with (dom := (apply_atomic dom atomic)). reflexivity. }
      inversion Htighten; subst; clear Htighten.
      split; try assumption.
      split.
      * apply dom_consistent_iff_checked; assumption.
      * exact Hvalid.
    + assert (dom_tightened dom').
      { split.
        - inversion Htighten. subst; clear Htighten.
          apply tighten_lb_tightens with (dom := (apply_atomic dom atomic)). reflexivity.
        - clear Hcheck Hconsistent.
          destruct dom as [lb ub holes].
          destruct dom' as [lb' ub' holes'].
          rewrite ub_tightened_not_lb with (lb' := lb).
          destruct Htightened as [_ Htightened].
          enough (ub' = ub /\ holes' = holes).
          { destruct H; now subst. }
          inversion Htighten; clear Htighten.
          rename H0 into H.
          unfold apply_atomic in H; rewrite Hcmp in H.
          unfold tighten_lb, update_lb in H; simpl in H.
          destruct Zext.max; try now inversion H.
          destruct sint.mem; now inversion H. }
      inversion Htighten; subst; clear Htighten.
      split; try assumption.
      split.
      * apply dom_consistent_iff_checked; assumption.
      * exact Hvalid.
    + assert (dom_tightened dom').
      { inversion Htighten. subst.
        apply tighten_tightens with (dom := (apply_atomic dom atomic)). reflexivity. }
      inversion Htighten; subst; clear Htighten.
      split; try assumption.
      split.
      * apply dom_consistent_iff_checked; assumption.
      * exact Hvalid.
    + assert (dom_tightened dom').
      { inversion Htighten. subst.
        apply tighten_tightens with (dom := (apply_atomic dom atomic)). reflexivity. }
      inversion Htighten; subst; clear Htighten.
      split; try assumption.
      split.
      * apply dom_consistent_iff_checked; assumption.
      * exact Hvalid.
  - exact Hvalid. 
Qed.


End TightenComplete.
