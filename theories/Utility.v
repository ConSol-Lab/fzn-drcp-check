From Coq Require Lists.List.
From Coq Require Sorting.Sorted.
From Coq Require Sorting.Permutation.
Require Coq.ZArith.ZArith.
Require Coq.ZArith.Int.
Require Coq.NArith.NArith.
Require Coq.Logic.FinFun.
Require Lia.
Require Coq.Structures.Orders.
Require Coq.Structures.OrdersEx.
Require Coq.MSets.MSetInterface.
Require Coq.MSets.MSetRBT.
Require Coq.MSets.MSetProperties.
Require MMaps.Interface.
Require MMaps.RBT.
Require Program.Basics.

Module Tactics.
  Import Bool.
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

Ltac destruct_pairs :=
  repeat match goal with
  | [ x : _ * _ |- _ ] => destruct x
  end.

Ltac solve_equiv :=
  constructor;
  repeat (
    repeat intro;
    destruct_pairs;
    simpl in *;
    destruct_ands;
    subst;
    try reflexivity;
    try symmetry; try assumption;
    try easy
  ).

Ltac solve_disjunction :=
  first
    [ easy
    | match goal with
      | |- _ \/ _ =>
          (left; solve_disjunction)
          ||
          (right; solve_disjunction)
      end
    ].

Import List.
Ltac break_in_hyps :=
  repeat match goal with
  | [ H: In ?x _  |- In ?x _ ] => simpl in H
  end;
  repeat match goal with
  | [ H: _ \/ In ?x _ |- In ?x _ ] =>
      let Hnew := fresh H in
      destruct H as [Hnew | Hnew]; subst; try discriminate
  end;
  simpl.

Ltac solve_in := break_in_hyps; try solve_disjunction.

Lemma reflect_neg_iff (P : Prop) (b : bool) :
  reflect P b -> (~ P <-> b = false).
Proof.
  intros R; destruct R; split; cbv; congruence.
Qed.

(* The below are very useful when you have a bool and Prop version of a lemma but don't want to active the full ssreflect machinery. Used to translate between the cumulative Prop and non-Prop versions. *)
Ltac reflect_rewrite_base R loc is_goal :=
  match type of R with
  | reflect ?P ?P_dec =>
    let Rtrue := fresh in
    let Rfalse := fresh in
    specialize (reflect_iff P P_dec R) as Rtrue;
    specialize (reflect_neg_iff P P_dec R) as Rfalse;
    match is_goal with
    | false =>
      first [ rewrite Rtrue in loc
        | rewrite <- Rtrue in loc
        | rewrite Rfalse in loc
        | rewrite <- Rfalse in loc ]
    | true =>
      first [ rewrite Rtrue
        | rewrite <- Rtrue
        | rewrite Rfalse
        | rewrite <- Rfalse ]
    end;
    clear Rtrue Rfalse
  | _ => fail "Argument should be reflect lemma!"
  end.

Ltac reflect_rewrite R := reflect_rewrite_base R True true.
 
Tactic Notation "reflect_rewrite" constr(R) :=
  reflect_rewrite R.

Tactic Notation "reflect_rewrite" constr(R) "in" hyp(H) :=
  reflect_rewrite_base R H false.

End Tactics.

Module ListInd.
Import List.
Lemma fold_ind {X} :
  forall (Acc:Type)(P : list X -> Acc -> Type)(f : X -> Acc -> Acc)(i : Acc)(s:list X),
  P nil i ->
  (forall x a s',
    P s' a -> P (x :: s') (f x a)) ->
  P s (fold_right f i s).
Proof.
  intros Acc P f i s Hnil Hstep.
  induction s as [| x s IH].
  - simpl. exact Hnil.
  - simpl. specialize (Hstep x (fold_right f i s)).
    apply Hstep.
    exact IH.
Qed.

End ListInd.

(** * ZMaxMinList  *)
(** These are used by cumulative. *)
Module ZMaxMinList.
  Import ZArith.
  Import List.
  Open Scope Z_scope.
  Import ListInd.
  Import Lia.
  Definition max_l (l : list Z) :=
  fold_right Z.max (hd 0 l) l.

  Definition min_l (l : list Z) :=
    fold_right Z.min (hd 0 l) l.

  Lemma min_l_spec l : forall n, In n l -> min_l l <= n.
  Proof.
    set (P := fun (s : list Z) (acc : Z) =>
      forall n, In n s -> acc <= n).
    enough (P l (min_l l)).
    { apply H. } 
    unfold min_l.
    apply fold_ind; unfold P in *; clear P.
    - intros n Hin. destruct Hin.
    - intros n acc s. intros IH.
      intros n'. intros [Hnn' | Hin].
      + subst. lia.
      + specialize (IH n' Hin).
        lia.
  Qed.

  Lemma max_l_spec l : forall n, In n l -> n <= max_l l.
  Proof.
    set (P := fun (s : list Z) (acc : Z) =>
      forall n, In n s -> n <= acc).
    enough (P l (max_l l)).
    { apply H. } 
    unfold max_l.
    apply fold_ind; unfold P in *; clear P.
    - intros n Hin. destruct Hin.
    - intros n acc s. intros IH.
      intros n'. intros [Hnn' | Hin].
      + subst. lia.
      + specialize (IH n' Hin).
        lia.
  Qed.
End ZMaxMinList.

(** * SubList *)
(** This logic was originally critical to Cumulative when there was still a dependency on there being no duplicates and looking up activities for bounds using names. But with the new valid_bounds definition, the below is no longer necessary.

If this is still around by 2026 without any use being found, feel free to delete. *)
Module SubList.
  Import List.
  Import Sorted.
  Import Permutation.
  Import Lia.
  Section SubLists.
  Context {A : Type}.
  
  Definition sublist (l1 l2 : list A) :=
    exists diff, Permutation (l1 ++ diff) l2.

  Lemma sublist_if_in_nodup :
    forall (l1 l2 : list A),
      (forall (a : A), In a l1 -> In a l2) 
        -> NoDup l1 
        -> sublist l1 l2.
  Proof.
    intros l1.
    induction l1 as [| a1 l1 IH].
    - intros.
      exists l2. simpl. reflexivity.
    - intros l2 Hin.
      intros Hnodup.
      inversion Hnodup; subst; clear Hnodup.
      assert (In a1 l2) as H1in2 
        by (apply Hin; left; reflexivity).
      apply in_split in H1in2.
      rename l2 into l'.
      destruct H1in2 as (l2 & l3 & Hl23); subst l'.
      specialize (IH (l2 ++ l3)).
      assert (sublist l1 (l2 ++ l3)).
      { 
        apply IH; try assumption.
        intros a Hin1.
        assert (In a (a1 :: l1)) as Hacons
          by (right; assumption).
        apply Hin in Hacons.
        apply in_app_or in Hacons.
        destruct Hacons.
        - rewrite in_app_iff. left. assumption.
        - destruct H.
          + subst a. contradiction.
          + rewrite in_app_iff. right. assumption.
      }
      clear -H.
      destruct H as (diff & Hperm).
      exists diff.
      rewrite <- Permutation_middle.
      rewrite <- app_comm_cons.
      apply perm_skip.
      exact Hperm.
  Qed.

  Lemma nodup_sublist :
    forall l1 l2,
      NoDup l2
        ->
      sublist l1 l2
        ->
      NoDup l1.
  Proof.
    intros l1 l2 Hnodup.
    intros (diff & Hperm).
    apply NoDup_app_remove_r with (l' := diff).
    apply Permutation_NoDup with (l := l2).
    - symmetry. exact Hperm.
    - exact Hnodup.
  Qed.

  (* Helper lemma for sublist_filter *)
  Lemma permutation_partition (pred : A -> bool ):
    forall l,
    Permutation l (fst (partition pred l) ++ snd (partition pred l)).
  Proof.
    intros l.
    repeat rewrite partition_as_filter. simpl.
    induction l.
    - simpl. apply perm_nil.
    - simpl. destruct (pred a) eqn:Hfa.
      + simpl. apply perm_skip. apply IHl.
      + simpl. remember (filter (fun x : A => negb (pred x)) l) as l1;
        clear Heql1.
        remember (filter pred l) as l2; clear Heql2.
        apply Permutation_cons_app.
        exact IHl.
  Qed.

  Lemma sublist_filter (pred : A -> bool) :
    forall (l : list A),
    sublist (filter pred l) l.
  Proof.
    intros l.
    assert (partition pred l = partition pred l) by reflexivity.
    rewrite partition_as_filter in H at 1.
    remember (fun x : A => negb (pred x)) as antipred.
    assert (fst (partition pred l) = filter pred l) as Hfilter.
    { rewrite <- H. reflexivity. }
    assert (snd (partition pred l) = filter antipred l) as Hantifilter.
    { rewrite <- H. reflexivity. }
    rewrite <- Hfilter.
    exists (filter antipred l).
    rewrite <- Hantifilter.
    symmetry.
    apply permutation_partition.
  Qed.

  End SubLists.

  Section Map.
  
  Context {A B : Type}.
  Context {f : A -> B}.

  Lemma sub_list_map : 
    forall (l1 l2 : list A),
    sublist l1 l2
      ->
    sublist (map f l1) (map f l2).
  Proof.
    intros l1 l2.
    intros (l1_diff & Hperm).
    exists (map f l1_diff).
    rewrite <- map_app.
    apply Permutation_map.
    exact Hperm.
  Qed.

  Lemma nodup_map_filter (pred : A -> bool) : forall l,
    NoDup (map f l)
      ->
    NoDup (map f (filter pred l)).
  Proof.
    intros l Hnodup.
    apply nodup_sublist with (l2 := map f l).
    - exact Hnodup.
    - apply sub_list_map.
      apply sublist_filter.
  Qed.
 
  End Map.

  Section Count.
  Context {A : Type}.
  Hypothesis eq_dec : forall x y : A, {x = y}+{x <> y}.

  Definition sublist_count (l1 l2 : list A) :=
    forall a, 
      In a l1 -> 
      count_occ eq_dec l1 a <= count_occ eq_dec l2 a.

  Definition repeat_f {A} (f : A -> nat) (a : A) :=
    repeat a (f a).

  Definition build_counts (l : list A) (f : A -> nat) :=
    concat (map (repeat_f f) (nodup eq_dec l)).

  Definition count_diff (l1 l2 : list A) (a : A) :=
    count_occ eq_dec l2 a - count_occ eq_dec l1 a.

  Lemma build_counts_zero :
    forall f l a,
      ~ In a l
        ->
      count_occ eq_dec (build_counts l f) a = 0.
  Proof.
    intros f l.
    intros a Hnin.
    rewrite <- count_occ_not_In.
    unfold build_counts.
    rewrite in_concat.
    unfold not. intros H.
    destruct H as (a_repeat & Hinmap & Hinrep).
    rewrite in_map_iff in Hinmap.
    destruct Hinmap as (a' & Hrep & Hinnodup).
    unfold repeat_f in Hrep; subst a_repeat.
    apply repeat_spec in Hinrep; subst a'.
    rewrite nodup_In  in Hinnodup.
    apply Hnin. exact Hinnodup.
  Qed.

  Lemma build_counts_correct :
  forall f l a,
    In a l
      ->
    count_occ eq_dec (build_counts l f) a = f a.
  Proof.
    intros f. induction l.
    - intros a. intros Hnil. destruct Hnil.
    - intros a'. simpl.
      intros Ha'.
      unfold build_counts. simpl.
      destruct (in_dec eq_dec a l) as [Hin|Hnin].
      + destruct Ha'.
        * subst a'. apply IHl. exact Hin.
        * apply IHl. exact H.
      + destruct Ha' as [| Haa'].
        * subst a'.
          unfold build_counts. simpl.
          rewrite count_occ_app.
          unfold repeat_f at 1. 
          rewrite count_occ_repeat_eq; try reflexivity.
          apply build_counts_zero with (f := f) in Hnin. unfold build_counts in Hnin. rewrite Hnin.
          lia.
      * simpl. rewrite count_occ_app.
          unfold repeat_f at 1.
          rewrite count_occ_repeat_neq.
          -- simpl. apply IHl. exact Haa'.
          -- intros Ha_eq_a'.
            subst a'. apply Hnin.
            exact Haa'.
  Qed.

  Lemma sublist_iff_count :
    forall l1 l2,
      sublist l1 l2 <-> sublist_count l1 l2.
  Proof.
    unfold sublist, sublist_count.
    intros l1 l2. split.
    - intros (diff & Hperm).
      intros a Hin.
      rewrite Permutation_count_occ in Hperm.
      rewrite <- Hperm.
      rewrite count_occ_app. lia.
    - intros Hsub.
      exists (build_counts l2 (count_diff l1 l2)).
      rewrite Permutation_count_occ with (eq_dec := eq_dec).
      intros a.
      rewrite count_occ_app.
      destruct (in_dec eq_dec a l1) as [Hin | Hnin].
      + rewrite build_counts_correct.
        * unfold count_diff. apply Hsub in Hin. lia.
        * rewrite count_occ_In with (eq_dec := eq_dec). apply Hsub in Hin as Hcounts. rewrite count_occ_In with (eq_dec := eq_dec) in Hin.
          lia.
      + rewrite count_occ_not_In with (eq_dec := eq_dec) in Hnin.
        destruct (in_dec eq_dec a l2) as [Hin2 | Hnin2].
        * rewrite build_counts_correct.
          -- unfold count_diff. rewrite Hnin. lia.
          -- exact Hin2.
        * rewrite build_counts_zero.
          -- rewrite count_occ_not_In with (eq_dec := eq_dec) in Hnin2. lia.
          -- exact Hnin2.
  Qed.

  (* The below definitions were originally used for a lot of the sublist_count proofs, but those were migrated to use only sublist. *)
  Fixpoint remove_once (a : A) (l : list A) :=
    match l with
    | nil => nil
    | a' :: l' => if eq_dec a a'
                      then l'
                      else a' :: (remove_once a l')
    end.

  Lemma remove_once_one_less_count :
    forall l a, pred (count_occ eq_dec l a) = count_occ eq_dec (remove_once a l) a. 
  Proof.
    induction l.
    - intros a. simpl. reflexivity.
    - intros a'.
      simpl. destruct (eq_dec a a').
      + subst a'. rewrite <- pred_Sn. 
        destruct (eq_dec a a); try contradiction.
        reflexivity.
      + destruct (eq_dec a' a).
        { symmetry in e. contradiction. }
        simpl.
        destruct (eq_dec a a').
        { contradiction. }
        apply IHl.
  Qed.
  
  Lemma remove_once_one_same_if_neq :
    forall l a a', a <> a' -> count_occ eq_dec l a' = count_occ eq_dec (remove_once a l) a'. 
  Proof.
    induction l.
    - intros a. simpl. reflexivity.
    - intros a1 a2 Ha1a2.
      simpl. 
      destruct (eq_dec a a2) as [| Haa2].
      + subst a2. 
        destruct (eq_dec a1 a).
        * subst a1. contradiction.
        * simpl.
          destruct (eq_dec a a) as [Haa | Haa]; try contradiction.
          f_equal.
          apply IHl. exact Ha1a2.
      + destruct (eq_dec a1 a) as [| Ha1a].
        * subst a1. reflexivity.
        * simpl. destruct (eq_dec a a2).
          { subst a2. contradiction. }
          clear n.
          apply IHl. exact Ha1a2.
  Qed. 

  Lemma remove_once_one_In :
    forall l a a', In a' (remove_once a l) -> In a' l. 
  Proof.
    induction l.
    - intros a a'. intros Hnil. simpl in Hnil. contradiction.
    - intros a1 a2.
      simpl. destruct (eq_dec a1 a).
      + subst a1. intros Hin. right. exact Hin.
      + simpl. intros Hin. destruct Hin.
        * left. exact H.
        * right. apply IHl with (a := a1).
          exact H.
  Qed.

  Lemma permutation_remove_once :
    forall (a : A) l l',
    Permutation (a :: l) l'
      ->
    Permutation l (remove_once a l').
  Proof.
    intros a l l'.
    repeat rewrite Permutation_count_occ with (eq_dec := eq_dec).
    intros H.
    intros a'.
    specialize (H a'); simpl in H.
    destruct (eq_dec a a') as [Haa'|Haa'].
    + subst a'. rewrite <- remove_once_one_less_count.
      rewrite <- H. lia.
    + rewrite <- remove_once_one_same_if_neq.
      * exact H.
      * exact Haa'.
  Qed.

  End Count.
  
End SubList.

(** * ListEx  *)
(** Various utilities for working with lists.  *)
Module ListEx.
  Import Bool.
  Import List.
  Import Lia.
  Import Permutation.
  Import Tactics.

(* From Coq 9.0 *)
Lemma filter_false {A} l : filter (fun _ : A => false) l = nil.
Proof. induction l; cbn [filter]; congruence. Qed.


Lemma forallb_false {A} (f : A -> bool) :
  forall l,
    forallb f l = false <-> exists a, In a l /\ f a = false.
Proof.
  induction l.
  - simpl; split; try easy.
    now intros (a & Hfalse & _).
  - simpl. rewrite andb_false_iff.
    rewrite IHl.
    split; intros H.
    + destruct H as [Hfalse | (a' & Hin & Hfalse')].
      * exists a. split; solve_disjunction.
      * exists a'. split; solve_disjunction.
    + destruct H as (a' & Ha' & Hfalse').
      destruct Ha' as [Haa' | Hin].
      * subst a'. now left.
      * right. now exists a'.
Qed.
 
Lemma InA_eq_iff_In {A} :
  forall (l : list A) a,
    SetoidList.InA eq a l <-> In a l.
Proof.
  induction l.
  - intros a; easy.
  - intros a'. split; intros H.
    + inversion H; subst y l0.
      * subst a'. left. reflexivity.
      * right. rewrite <- IHl. assumption.
    + apply SetoidList.InA_cons.
      inversion H.
      * subst a'. left. reflexivity.
      * right. rewrite IHl. assumption.
Qed.

Definition flat_map_option {A B} (f : A -> option B) (l : list A) : list B :=
  flat_map (fun a =>
    match f a with
    | Some b => b :: nil
    | None => nil
    end
  ) l.

Lemma in_flat_map_option {A B} f (l : list A) (b : B) :
  In b (flat_map_option f l) <-> exists a, In a l /\ f a = Some b.
Proof.
  unfold flat_map_option.
  rewrite in_flat_map.
  repeat split; intros H; destruct H as [a [Hina Hb]];
  exists a; repeat split; try assumption; destruct (f a);
  try discriminate Hb; try contradiction.
  - destruct Hb; try contradiction. subst b. reflexivity.
  - inversion Hb. subst b. left. reflexivity.
Qed.

Definition option_default {A} (d : A) (a : option A) :=
  match a with
  | Some a => a
  | None => d
  end.

Definition option_map_default {A B} (f : A -> option B) (d : B) : A -> B :=
  fun a =>
    match f a with
    | Some b => b
    | None => d
    end.

Definition option_map_flat {A} (f : A -> option A) (a : option A) : option A :=
  match a with
  | Some a => f a
  | None => None
  end.


Definition filter_option {A} (a : option A) :=
  match a with
  | Some _ => true
  | None => false
  end.

Definition filter_f_option {A B} (f : A -> option B) (a : A) :=
  match f a with
  | Some _ => true
  | None => false
  end.

(* This one is usually more useful. *)
Lemma flat_map_option_as_filter_map :
  forall A B (f : A -> option B) d l,
  flat_map_option f l = map (option_map_default f d) (filter (filter_f_option f) l).
Proof.
  intros A B f d.
  induction l.
  - simpl. reflexivity.
  - simpl. destruct (f a) as [fa |] eqn:Hfa.
    + assert (filter_f_option f a = true).
      { unfold filter_f_option. rewrite Hfa. reflexivity. }
      rewrite H. simpl. rewrite <- IHl. unfold option_map_default. rewrite Hfa. reflexivity.
    + assert (filter_f_option f a = false).
      { unfold filter_f_option. rewrite Hfa. reflexivity. }
      rewrite H. simpl. rewrite <- IHl. reflexivity.
Qed.

Lemma flat_map_option_as_map_filter :
  forall A B (f : A -> option B) d l,
  flat_map_option f l = map (option_default d) (filter filter_option (map f l)).
Proof.
  intros A B f d.
  induction l.
  - simpl. reflexivity.
  - simpl. destruct (f a) as [fa |] eqn:Hfa.
    + assert (filter_option (Some fa) = true) by (unfold filter_option; reflexivity). rewrite H. simpl.
    rewrite IHl. reflexivity.
    + simpl. rewrite IHl. reflexivity.
Qed.

Lemma nodup_map (A B : Type) :
  forall (f : A -> B) (l : list A),
    NoDup (map f l)
      ->
    forall a1 a2,
      In a1 l
        ->
      In a2 l
        ->
      f a1 = f a2
        ->
      a1 = a2.
Proof.
  intros f. induction l.
  - intros _ a1 a2 Hnil. destruct Hnil.
  - simpl. intros Hnodup.
    inversion Hnodup; subst x l0.
    specialize (IHl H2).
    assert (forall a', In a' l -> f a = f a' -> False).
    {
      intros a' Hin Hf.
      clear IHl H2 Hnodup.
      apply in_split in Hin. 
      destruct Hin as (l1 & l2 & Hl); subst l.
      apply H1; clear H1.
      rewrite in_map_iff.
      setoid_rewrite in_app_iff.
      exists a'.
      split; try easy.
      right. left. reflexivity.
    }
    intros a1 a2.
    intros [Ha1 | Hin1].
    + subst a1.
      intros [Ha2 | Hin2].
      * now subst a2.
      * intros Hfa2.
        exfalso. apply H with (a' := a2);
        assumption.
    + intros [Ha2 | Hin2].
      * subst a2.
        intros Hfa1.
        exfalso. apply H with (a' := a1);
        easy.
      * apply IHl; assumption.
Qed.

Lemma nodup_key :
  forall K B A (l : list A) (a_k : A -> K) (f : A -> B) (b_k : B -> K),
  NoDup (map a_k l)
    ->
  (forall a, In a l -> a_k a = b_k (f a))
    ->
  NoDup (map b_k (map f l)).
Proof.
  intros K B A l a_k f b_k Hnodup Hkeq.
  induction l.
  - simpl. apply NoDup_nil.
  - simpl.
    inversion Hnodup; subst x; subst l0.
    specialize (IHl H2).
    apply NoDup_cons.
    + unfold not.
      intros Hin.
      apply H1; clear H1.
      rewrite in_map_iff in Hin.
      rewrite in_map_iff.
      destruct Hin as (b & Hbkf & Hbin).
      rewrite in_map_iff in Hbin.
      destruct Hbin as (a' & Hfab & Hin').
      exists a'.
      split; try assumption.
      repeat rewrite Hkeq.
      * rewrite Hfab. exact Hbkf.
      * left. reflexivity.
      * right. exact Hin'. 
    + apply IHl.
      intros a' Hin.
      apply Hkeq.
      right. exact Hin.
Qed.

Lemma preserve_nodup : 
  forall K B A (l : list A) (a_k : A -> K) (f : A -> B) (b_k : B -> K),
  NoDup (map a_k l)
    ->
  (forall a, In a l -> a_k a = b_k (f a))
    ->
  NoDup (map f l).
Proof.
  intros K B A l a_k f b_k.
  intros Hnodup Hkeq.
  apply NoDup_map_inv with (f := b_k).
  apply nodup_key with (a_k := a_k).
  - exact Hnodup.
  - exact Hkeq.
Qed.

Fixpoint map_valid {A B} (f : A -> option B) (l : list A) (acc : list B) : list B :=
  match l with
  | nil => acc
  | a :: l' =>
    match f a with
    | Some b => map_valid f l' (b :: acc)
    | None => nil
    end
  end. 

Lemma map_valid_length_permute {A B} :
  forall (f : A -> option B) l bl1 bl2,
    Permutation bl1 bl2
      ->
    length (map_valid f l bl1) = length (map_valid f l bl2).
Proof.
  intros f. induction l.
  - intros bl1 bl2 Hpermute. simpl. apply Permutation_length. exact Hpermute.
  - intros bl1 bl2 Hpermute. simpl.
    destruct (f a) as [fa |] eqn:Hfa.
    + apply IHl.
      apply perm_skip.
      exact Hpermute.
    + reflexivity.
Qed. 

Lemma map_valid_acc {A B} :
  forall (f : A -> option B) l acc b,
    length (map_valid f l (b :: acc)) >= length (map_valid f l acc).
Proof.
  intros f. induction l.
  - intros acc b. simpl. lia.
  - intros acc b. simpl.
    destruct (f a) as [fa |] eqn:Hfa.
    + assert (length (map_valid f l (fa :: b :: acc)) = length (map_valid f l (b :: fa :: acc))).
      { apply map_valid_length_permute. apply perm_swap. }
      rewrite H. apply IHl.
    + lia.
Qed.

Lemma map_valid_H {A B} :
  forall (f : A -> option B) l b bl1 bl2,
    bl2 <> nil
      ->
    Permutation bl1 bl2
      ->
    map_valid f l (b :: bl1) <> nil
      ->
    map_valid f l bl2 <> nil.
Proof.
  intros f. induction l.
  - intros b bl1 bl2 Hnnil Hperm. simpl. intros H. exact Hnnil.
  - intros b bl1 bl2. simpl.
    intros Hnnil Hperm.
    destruct (f a) as [fa |] eqn:Hfa.
    + intros H. apply IHl with (bl1 := (fa :: bl1)) (b := b).
      * easy.
      * apply perm_skip. apply Hperm.
      * rewrite <- length_zero_iff_nil in H.
        rewrite <- length_zero_iff_nil.
        rewrite map_valid_length_permute with (bl2 := (fa :: b :: bl1)).
        -- exact H.
        -- apply perm_swap.
    + intros H. exact H.
Qed. 

Lemma map_valid_as_map {A B} :
  forall (f : A -> option B) (d : B) l acc,
    map_valid f l acc <> nil
      ->
    map_valid f l acc = rev (map (option_map_default f d) l) ++ acc.
Proof.
  intros f d. induction l.
  - intros acc. intros Hnnil. simpl. reflexivity.
  - intros acc. simpl.
    destruct (f a) eqn:Hfa; try contradiction.
    intros Hnnil.
    rewrite IHl.
    + assert (option_map_default f d a = b).
      { unfold option_map_default. rewrite Hfa. reflexivity. }
      rewrite H. rewrite <- app_assoc. simpl. reflexivity.
    + exact Hnnil.
Qed.

Lemma map_valid_all_some :
  forall A B (f : A -> option B) l acc,
    map_valid f l acc <> nil
      ->
    (forall a, In a l ->
      match f a with
      | None => False
      | Some _ => True
      end 
    ).
Proof.
  intros A B f. induction l.
  - intros acc. intros H. intros a Hfalse.
    destruct Hfalse.
  - intros acc. simpl.
    destruct (f a) as [fa |] eqn:Hfa.
    + intros H.
      specialize (IHl (fa :: acc) H).
      intros a'.
      intros [Ha' | Hin].
      * subst a'. rewrite Hfa. reflexivity.
      * apply IHl. exact Hin.
    + intros Hfalse. exfalso. apply Hfalse. reflexivity.
Qed.

(* Slightly more convenient statement... *)
Lemma map_valid_spec {A B} (f : A -> option B) r l (d : B) :
    r = map_valid f l nil
      ->
    r <> nil
      ->
    r = rev (map (option_map_default f d) l)
      /\
    (forall a, In a l ->
      match f a with
      | None => False
      | Some _ => True
      end 
    ).
Proof.
  intros Hr Hnnil.
  split.
  - rewrite Hr in Hnnil.
    apply map_valid_as_map with (d := d) in Hnnil.
    rewrite Hr.
    rewrite Hnnil. rewrite app_nil_r. reflexivity.
  - apply map_valid_all_some with (acc := nil).
    rewrite <- Hr. exact Hnnil.
Qed.

Lemma map_valid_nil_ex_none :
  forall A B (f : A -> option B) l acc,
    l <> nil
      ->
    map_valid f l acc = nil
      ->
    exists a, In a l /\ f a = None.
Proof.
  intros A B f.
  induction l.
  - intros acc Hvalid. contradiction.
  - intros acc. simpl.
    destruct (f a) eqn:Hfa.
    2: { intros. exists a. split; try assumption. left. reflexivity. }
    destruct l as [| a' l].
    { intros Ha. 
      simpl. intros H; discriminate H. }
    intros _.
    assert (a' :: l <> nil) by easy.
    simpl.
    destruct (f a') as [b'|] eqn:Hfa'.
    2: { intros _. exists a'. split; try assumption. right. left. reflexivity. }
    intros Hnil.
    specialize (IHl (b :: acc) H); clear H.
    simpl in IHl. rewrite Hfa' in IHl.
    specialize (IHl Hnil).
    destruct IHl as (a_ & Ha_ & Hfa_).
    exists a_.
    split.
    + right. exact Ha_.
    + exact Hfa_.
Qed.

Fixpoint fold_left_error {Acc X} (f : Acc -> X -> option Acc) (xl : list X) (acc : Acc) : option Acc :=
  match xl with
  | nil => Some acc
  | x :: xl' => 
    match f acc x with
    | None => None
    | Some acc => fold_left_error f xl' acc
    end
  end.

(* Kinda like fun acc x => option_map_flat (fun acc => f acc x) acc *)
Definition fold_left_error_f {Acc X } (f : Acc -> X -> option Acc) (acc : option Acc) (x : X) :=
  match acc with
  | None => None
  | Some acc => f acc x
  end.

Lemma fold_left_error_as_fold_left :
  forall (Acc X : Type) (f : Acc -> X -> option Acc) xl acc,
    fold_left_error f xl acc = fold_left (fold_left_error_f f) xl (Some acc).
Proof.
  intros Acc X f. induction xl as [| x xl IH].
  - intros acc. simpl. reflexivity.
  - intros acc. simpl.
    destruct (f acc x) eqn:Hfx.
    + apply IH.
    + rewrite <- fold_left_rev_right. unfold fold_left_error_f. 
      clear. induction xl as [| x xl IH].
      * reflexivity.
      * simpl. rewrite fold_right_app. simpl.
        exact IH.
Qed.

End ListEx.

Module ZRange.
  Import ZArith.
  Import NArith.
  Import List.
  Import Lia.
  Import Sorted.

  Open Scope Z_scope.
  
  Fixpoint range_rec (s : Z) (e : Z) (n : nat) (acc : list Z) : list Z :=
    match n with
    | O => acc
    | S n' => range_rec s (e - 1) n' (e :: acc)
    end.

  Fixpoint range_rev_rec (s : Z) (e : Z) (n : nat) (acc : list Z) :=
    match n with
    | O => acc
    | S n' => range_rev_rec (s + 1) e n' (s :: acc)
    end.

   Definition nth_z {A} (n : Z) (l : list A) (l_start : Z) (d : A) :=
    if (n >=? l_start) 
      then nth (Z.to_nat (n - l_start)) l d
      else d.

  Lemma nth_z_spec {A} (l : list A) (s : Z) (d : A) (n : Z) :
    s <= n
      ->
    nth_z n l s d = nth (Z.to_nat (n - s)) l d.
  Proof.
    intros Hn.
    unfold nth_z.
    destruct (n >=? s) eqn:Hns; try lia. reflexivity.
  Qed.

  Definition shift_z (z : Z) (n : nat) :=
    Z.of_nat n + z. 

  Lemma range_rec_S :
    forall s n acc,
      range_rec s (s + Z.of_nat n) (S n) acc 
        =
      s :: range_rec (s + 1) (s + Z.of_nat n) n acc.
  Proof.
    intros s. induction n.
    - simpl. intros acc. assert (s + 0 = s) by lia.
      rewrite H. reflexivity.
    - intros acc.
      remember (Z.of_nat n) as nz.
      replace (s + Z.of_nat (S n)) with (s + nz + 1) by lia.
      simpl range_rec at 2.
      replace (s + nz + 1 - 1) with (s + nz) by lia.
      rewrite <- IHn.
      simpl.
      replace (s + nz + 1 - 1 - 1) with (s + nz - 1) by lia.
      replace (s + nz + 1 - 1) with (s + nz) by lia.
      reflexivity.
  Qed.

  Lemma range_rec_spec :
    forall s n acc,
      range_rec s (s + Z.of_nat n - 1) n acc = map (shift_z s) (seq 0 n) ++ acc.
  Proof.
    intros s. induction n.
    - simpl. reflexivity.
    - intros acc. 
      remember (Z.of_nat n) as nz.
      assert (s + Z.of_nat (S n) - 1 = s + nz) by lia.
      rewrite H; clear H.
      simpl range_rec.
      rewrite IHn. clear IHn.
      rewrite seq_S. rewrite map_app. simpl.
      assert (shift_z s n = s + nz).
      { unfold shift_z. lia. }
      rewrite H.
      clear.
      remember (map (shift_z s) (seq 0 n)) as l;
      clear n Heql.
      remember (s + nz) as n; clear.
      rewrite <- app_assoc.
      rewrite <- app_comm_cons.
      rewrite app_nil_l.
      reflexivity.
  Qed.
 
  Definition range (s : Z) (e : Z) :=
    range_rec s e (Z.to_nat (e - s + 1)) nil.

  Lemma range_cons (s e : Z) :
    s <= e
      ->
    range s e = s :: range (s + 1) e.
  Proof.
    intros Hse.
    unfold range.
    remember (Z.to_nat (e - s)) as i.
    replace (Z.to_nat (e - (s + 1) + 1)) with i by lia.
    replace (Z.to_nat (e - s + 1)) with (S i) by lia.
    assert (e = s + Z.of_nat i) by lia.
    rewrite H.
    rewrite range_rec_S.
    reflexivity.
  Qed.
  
  Open Scope nat_scope.
  Lemma map_nth_len_lt {A B} :
    forall (f : A -> B) l n (d : A) (d' : B),
      n < length l
        ->
      f (nth n l d) = nth n (map f l) d'.
  Proof.
    intros f l n d d'.
    intros Hlen.
    specialize ((nth_error_nth' l) n d Hlen) as Hnth_err.
    pose proof Hlen as Hlen_map.
    rewrite <- length_map with (f := f) in Hlen_map.
    specialize ((nth_error_nth' (map f l)) n d' Hlen_map) as Hnth_err_map.
    specialize (map_nth_error f n l Hnth_err) as Hmap_err.
    rewrite Hmap_err in Hnth_err_map.
    inversion Hnth_err_map as [H].
    reflexivity.
  Qed.

  Open Scope Z_scope.

  Lemma range_spec (s e : Z) (d : Z) :
    forall n, 
      s <= n <= e 
        ->
      nth_z n (range s e) s d = n.
  Proof.
    intros n Hn.
    unfold nth_z.
    destruct (n >=? s) eqn:Hns; try lia; clear Hns.
    unfold range.
    remember (Z.to_nat (e - s + 1)) as i.
    assert (e = s + Z.of_nat i - 1) by lia.
    rewrite H.
    rewrite range_rec_spec.
    rewrite app_nil_r.
    rewrite <- map_nth_len_lt with (d := O).
    - rewrite seq_nth.
      + unfold shift_z. lia.
      + lia.
    - rewrite length_seq. lia.
  Qed.

  Lemma range_spec_other_base (s e : Z) (d : Z) :
    forall b,
      s <= b <= e
        ->
      forall n, 
        b <= n <= e 
          ->
        nth_z n (range s e) b d = n - (b - s).
  Proof.
    intros b Hb n Hn.
    unfold nth_z.
    destruct (n >=? b) eqn:Hns; try lia; clear Hns.
    unfold range.
    remember (Z.to_nat (e - s + 1)) as i.
    assert (e = s + Z.of_nat i - 1) by lia.
    rewrite H.
    rewrite range_rec_spec.
    rewrite app_nil_r.
    rewrite <- map_nth_len_lt with (d := O).
    - rewrite seq_nth.
      + unfold shift_z. lia.
      + lia.
    - rewrite length_seq. lia.
  Qed.


  Lemma in_range (s e : Z) :
    forall n,
      s <= n <= e
        <->
      In n (range s e).
  Proof.
    intros n.
    destruct (Z_le_gt_dec s e).
    - unfold range. 
      remember (Z.to_nat (e - s + 1)) as i.
      assert (e = s + Z.of_nat i - 1) as He by lia.
      rewrite He at 2.
      rewrite range_rec_spec.
      rewrite app_nil_r.
      rewrite in_map_iff.
      split; intros H.
      + exists (Z.to_nat (n - s)).
        split.
        * unfold shift_z. lia.
        * rewrite in_seq. lia.
      + destruct H as (n' & Hshift & Hin).
        unfold shift_z in Hshift.
        rewrite in_seq in Hin.
        lia.
    - unfold range.
      replace (Z.to_nat (e - s + 1)) with O by lia.
      simpl. lia.
  Qed. 

  Lemma length_range :
    forall s e,
      length (range s e) = Z.to_nat (e - s + 1).
  Proof.
    intros s e.
    destruct (Z_lt_ge_dec e s) as [Hes | Hes].
    - unfold range.
      assert (Z.to_nat (e - s + 1) = O) by lia.
      rewrite H. simpl. reflexivity.
    - unfold range.
      remember (Z.to_nat (e - s + 1)) as i.
      assert (e = s + Z.of_nat i - 1) by lia.
      rewrite H.
      rewrite range_rec_spec.
      rewrite app_nil_r.
      rewrite length_map.
      rewrite length_seq.
      reflexivity.
  Qed.

  Definition range_rev (s e : Z) :=
    range_rev_rec s e (Z.to_nat (e - s + 1)) nil.

  Lemma range_rev_is_rev_range_rec :
    forall s e acc,
      range_rev_rec s e (Z.to_nat (e - s + 1)) acc = rev (range_rec s e (Z.to_nat (e - s + 1)) nil) ++ acc.
  Proof.
    intros s e.
    destruct (Z_gt_le_dec s e).
    - replace (Z.to_nat (e - s + 1)) with O by lia.
      reflexivity.
    - remember (Z.to_nat (e - s + 1)) as n.
      generalize dependent e.
      generalize dependent s.
      induction n.
      { intros s e Hes H0. reflexivity. }
      intros s e Hes Hsn acc.
      assert (e = s + Z.of_nat n) as He by lia.
      rewrite He at 2.
      rewrite range_rec_S.
      simpl.
      destruct (Z_gt_le_dec (s + 1) e) as [Hgt | Hle].
      { assert (s = e) by lia; subst e.
        assert (n = 0%nat) by lia; subst n.
        simpl. reflexivity. }
      specialize (IHn (s + 1) e Hle).
      rewrite IHn.
      2: { lia. }
      subst e; clear.
      rewrite <- app_assoc.
      rewrite <- app_comm_cons.
      rewrite app_nil_l.
      reflexivity.
  Qed.

  Lemma range_rev_is_rev_range :
    forall s e,
      range_rev s e = rev (range s e).
  Proof.
    intros s e. 
    unfold range_rev, range.
    rewrite range_rev_is_rev_range_rec.
    rewrite app_nil_r.
    reflexivity.
  Qed.

  Lemma range_rev_spec (s e d : Z) :
    forall n, 
      s <= n <= e 
        ->
      nth_z n (range_rev s e) s d = e - (n - s).
  Proof.
    intros n Hsne.
    rewrite range_rev_is_rev_range.
    unfold nth_z.
    destruct (n >=? s) eqn:Hns; try lia; clear Hns.
    rewrite rev_nth.
    2: { rewrite length_range. lia. }
    rewrite length_range.
    replace (Z.to_nat (e - s + 1) - (S (Z.to_nat (n - s))))%nat with (Z.to_nat (e - n)) by lia.
    rewrite <- nth_z_spec by lia.
    rewrite range_spec_other_base by lia. 
    lia.
  Qed.

End ZRange.



Module Sets.

Import Orders.
Import MSetInterface.
Import ListInd.
Import ListEx.
Import Lia.
Import MSetRBT.
Import ZArith.

Module MakeUsual (X: UsualOrderedType) <: Sets with Module E := X.
 Include Make(X).
  Definition build (values : list elt) :=
    fold_left (fun acc y => add y acc) values empty.
  
  Lemma build_spec :
    forall values (e : elt),
      In e (build values) <-> List.In e values.
  Proof.
    intros values e.
    set (P := fun (acc : t) (s : list elt) =>
      forall e, In e acc <-> List.In e s).
    enough (P (build values) (rev values)).
    { unfold P in H; clear P.
      rewrite H. rewrite <- in_rev. reflexivity. }
    unfold build. rewrite <- fold_left_rev_right.
    clear e. 
    apply fold_ind.
    - unfold P; clear P. split; intros H; try easy.
    - intros e s l.
      unfold P; clear P.
      intros IH e'.
      rewrite add_spec. rewrite IH. simpl.
      assert (e' = e <-> e = e') by (now split).
      rewrite H. reflexivity.
  Qed.
End MakeUsual.

Import MSetProperties.

Module sstr := MakeUsual OrdersEx.String_as_OT.
Module sint := MakeUsual OrdersEx.Z_as_OT.
Module sstr_prps := MSetProperties.Properties sstr.
Module sint_prps := MSetProperties.Properties sint.

Open Scope Z_scope.
Lemma exists_sint_lb :
  forall s lb,
    exists slb,
      slb <= lb /\
        forall n,
          n < slb
            ->
          ~ sint.In n s.
Proof.
  intros s lb.
  exists (Z.min (option_default Z0 (sint.min_elt s)) lb).
  destruct (sint.min_elt s) as [min|] eqn:Hmin.
  - simpl. split; try lia.
    intros n.
    intros Hlble.
    destruct (sint.mem n s) eqn:Hmem.
    + exfalso.
      rewrite sint.mem_spec in Hmem.
      apply sint.min_elt_spec2 with (x := min) in Hmem;
      try assumption.
      destruct (Z.compare_spec min n) as [Hlt|Heq|Hgt]; try contradiction; try lia.
    + rewrite <- sint.mem_spec.
      now rewrite Hmem.
  - simpl. split; try lia.
    intros n _.
    apply sint.min_elt_spec3 in Hmin.
    apply Hmin.
Qed.

Lemma exists_sint_ub :
  forall s ub,
    exists sub,
      sub >= ub /\
        forall n,
          n > sub
            ->
          ~ sint.In n s.
Proof.
  intros s ub.
  exists (Z.max (option_default Z0 (sint.max_elt s)) ub).
  destruct (sint.max_elt s) as [max|] eqn:Hmax.
  - simpl. split; try lia.
    intros n.
    intros Hlble.
    destruct (sint.mem n s) eqn:Hmem.
    + exfalso.
      rewrite sint.mem_spec in Hmem.
      apply sint.max_elt_spec2 with (x := max) in Hmem;
      try assumption.
      destruct (Z.compare_spec max n) as [Hlt|Heq|Hgt]; try contradiction; try lia.
    + rewrite <- sint.mem_spec.
      now rewrite Hmem.
  - simpl. split; try lia.
    intros n _.
    apply sint.max_elt_spec3 in Hmax.
    apply Hmax.
Qed.



End Sets.

Require MMaps.Facts.

Module Maps.
Import String.
Import List.
Import ListInd.
Import ListEx.
Import Bool.
Import Tactics.
Module smap := RBT.Make OrdersEx.String_as_OT.
Module smap_prps := Facts.Properties OrdersEx.String_as_OT smap.

Module nmap := RBT.Make OrdersEx.N_as_OT.
Module nmap_prps := Facts.Properties OrdersEx.N_as_OT nmap.

Lemma In_to_InA_Duo_eq :
  forall {A B} (x : A) (y : B) (l : list (A * B)),
    In (x, y) l <-> SetoidList.InA (Interface.Duo eq eq) (x, y) l.
Proof.
  intros A B x y l.
  split.
  - apply SetoidList.In_InA.
    unfold Interface.Duo.
    solve_equiv. 
  - intros H.
    induction l.
    + inversion H.
    + inversion H.
      * subst y0 l0.
        unfold Interface.Duo in H1.
        destruct_pairs.
        destruct_ands; simpl in *; subst.
        left. reflexivity.
      * subst y0 l0. apply IHl in H1.
        right. exact H1.
Qed.


Lemma smap_in_spec {A} (x : string) (a : A) m :
  In (x, a) (smap.bindings m) <-> smap.MapsTo x a m.
Proof.
  rewrite In_to_InA_Duo_eq.
  rewrite smap.bindings_spec1.
  reflexivity.
Qed.

Definition build_map_step {A B} (f_key : A -> string) (f : A -> option B) (a : A) (m : smap.t B) :=
  match f a with
  | Some b => smap.add (f_key a) b m
  | None => m
  end
.

(* We use fold_left because it it is tail-recursive *)
Definition build_map_rec {A B} (f_key : A -> string) (f : A -> option B) (l : list A) (init : smap.t B) :=
  fold_left (fun x y => build_map_step f_key f y x) l init.

(* However, fold_right has a nice induction principle that's easy to work with. *)
Lemma build_map_as_right :
  forall A B (f_key : A -> string) (f : A -> option B) (l : list A) init,
  build_map_rec f_key f l init = fold_right (build_map_step f_key f) init (rev l).
Proof.
  intros A B f_key f l init.
  unfold build_map_rec. rewrite fold_left_rev_right. reflexivity.
Qed.

Definition build_map {A B} (f_key : A -> string) (f : A -> option B) (l : list A) :=
  build_map_rec f_key f l smap.empty.

Lemma build_map_maps_to :
  forall A B f_key (f : A -> option B) (l : list A) x b,
  smap.MapsTo x b (build_map f_key f l)
    ->
  exists a, In a l /\ f_key a = x /\ f a = Some b.
Proof.
  intros A B f_key f l x b.

  set (P :=
    fun (s : list A) (acc : smap.t B) =>
      smap.MapsTo x b acc
        ->
      exists a, In a s /\ f_key a = x /\ f a = Some b 
  ).
  unfold build_map.
  rewrite build_map_as_right.

  enough (P (rev l) (fold_right (build_map_step f_key f) smap.empty (rev l))).
  { unfold P in *. intros Hmap. apply H in Hmap.
    clear P H. destruct Hmap as (a & Hin & Hfkey & Hfab).
    exists a. repeat split; try assumption. apply in_rev. exact Hin. }

  apply fold_ind.
  - unfold P; clear P. intros Hempty.
    rewrite <- smap.find_spec in Hempty.
    rewrite smap.empty_spec in Hempty.
    discriminate Hempty.
  - intros a bmap al. unfold P; clear P.
    intros IH.
    intros H. 
    unfold build_map_step in H.
    rewrite <- smap.find_spec in H.
    enough (smap.find x bmap = Some b \/ (f_key a = x /\ f a = Some b)) as [Hsame | Hadd].
    + clear H. simpl. rewrite smap.find_spec in Hsame.
      apply IH in Hsame.
      destruct Hsame as (a' & Hin & Hfkey & Hfb).
      exists a'.
      repeat split; trivial.
      right. assumption.
    + clear -Hadd. destruct Hadd as [Hxa Hfa]. 
      exists a.
      split; [|split].
      * left. reflexivity.
      * assumption.
      * assumption.
    + destruct (String.string_dec x (f_key a)) as [Hxa| Hxa]; destruct (f a) as [b'|] eqn:Hfa.
      * rewrite <- Hxa in H. 
        rewrite smap.add_spec1 in H.
        right. now split.
      * left. assumption.
      * rewrite smap.add_spec2 in H; try easy.
        left. assumption.
      * left. assumption.
Qed.


Definition add_to_map {U}  (elt : string * U) (m : smap.t U) :=
  match elt with
  | (x, u) => smap.add x u m
  end.

Definition param_map {U} (l : list (string * U)) (d : U) : string -> option U :=
  let map := fold_right add_to_map smap.empty l in
  fun x =>
    smap.find x map.

Lemma param_map_in {U} :
  forall (d : U) x (l : list (string * U)) (u : U), 
  Some u = (param_map l d) x
    ->
  In (x, u) l.
Proof.
  intros d x. induction l.
  - intros u. unfold param_map. simpl. intros H.
    rewrite smap.empty_spec in H; discriminate.
  - intros u. 
    unfold param_map in *.
    intros Hu. simpl in Hu.
    destruct a as [x' u'].
    destruct (x =? x')%string eqn:Hxx'.
    + rewrite String.eqb_eq in Hxx'; subst x'.
      unfold add_to_map in Hu.
      rewrite smap.add_spec1 in Hu.
      inversion Hu.
      left. reflexivity. 
    + rewrite String.eqb_neq in Hxx'.
      unfold add_to_map in Hu.
      rewrite smap.add_spec2 in Hu by easy.
      apply IHl in Hu; clear IHl.
      right. exact Hu.
Qed.

Definition opt_is_none {A} (x : string) (a : option A) : bool :=
  match a with
  | None => true
  | Some _ => false
  end.

Definition check_none {A} (m : smap.t (option A)) : bool :=
  smap.exists_ opt_is_none m.

Definition smap_unwrap {A} (d : A) (m : smap.t (option A)) : smap.t A :=
  smap.map (option_default d) m.

Definition smap_valid {A B} (d : B) (f : A -> option B) (m : smap.t A) : smap.t B :=
  let opt_map := smap.map f m in
  if check_none opt_map
    then smap.empty
    else smap_unwrap d opt_map.

Definition valid_f {A B} (d : B) (f : A -> option B) (x : (string * A)) :=
  match x with
  | (x, a) =>
    (x, option_map_default f d a)
  end.

Lemma in_smap_check_none_false :
  forall A B (d : B) (f : A -> option B) (m : smap.t A),
    (exists x, smap.In x (smap_valid d f m))
      ->
    check_none (smap.map f m) = false.
Proof.
  intros A B d f m.
  intros [x Hin].
  unfold smap_valid in Hin.
  destruct (check_none (smap.map f m));
  try reflexivity.
  destruct Hin as [a Hmap].
  assert (smap.MapsTo x a (smap.empty)).
  { exact Hmap. }
  rewrite <- smap.find_spec in H.
  rewrite smap.empty_spec in H.
  discriminate H.
Qed. 


Lemma in_smap_not_none :
  forall A B (d : B) (f : A -> option B) (m : smap.t A),
    (exists x, smap.In x (smap_valid d f m))
      ->
  forall x a, In (x, a) (smap.bindings m) -> f a <> None.
Proof.
  intros A B d f m.
  intros Hex.
  apply in_smap_check_none_false in Hex as Hnonone.
  destruct Hex as [x' Hinvalid].
  intros x a Hin.
  unfold smap_valid in Hinvalid.
  rewrite Hnonone in Hinvalid.
  unfold smap_unwrap in Hinvalid.
  unfold check_none in Hnonone.
  rewrite smap.exists_spec in Hnonone.
  rewrite <- not_true_iff_false in Hnonone.
  rewrite existsb_exists in Hnonone.
  intros Hfanone. 
  apply Hnonone.
  exists (x, None).
  split.
  - rewrite smap.map_spec. rewrite in_map_iff. 
    exists (x, a).
    split.
    + rewrite Hfanone. reflexivity.
    + exact Hin.
  - reflexivity.
Qed.

Lemma smap_valid_spec :
  forall A B (d : B) (f : A -> option B) (m : smap.t A),
    (exists x, smap.In x (smap_valid d f m))
      ->
    smap.bindings (smap_valid d f m) = map (valid_f d f) (smap.bindings m).
Proof.
  intros A B d f m Hex.
  unfold smap_valid.
  apply in_smap_check_none_false with (d := d) in Hex as Hnonone.
  rewrite Hnonone.
  unfold smap_unwrap.
  repeat rewrite smap.map_spec.
  remember (smap.bindings m) as l.
  clear Hex Hnonone Heql.
  rewrite map_map.
  apply map_ext_in.
  intros [x a].
  intros Hin.
  unfold option_default.
  unfold valid_f.
  unfold option_map_default.
  reflexivity.
Qed.

Lemma smap_valid_nonempty_input :
  forall A B (d : B) (f : A -> option B) (m : smap.t A),
    (exists e,
      In e (smap.bindings m))
        ->
      check_none (smap.map f m) = false
        ->
      smap.is_empty (smap_valid d f m) = false.
Proof.
  intros A B d f m.
  intros Hex Hcheck.
  rewrite <- not_true_iff_false.
  rewrite smap_prps.is_empty_no_binding.
  unfold smap_valid.
  rewrite Hcheck.
  unfold smap_unwrap.
  repeat rewrite smap.map_spec.
  rewrite map_map.
  intros H.
  destruct Hex as [[x a] Hin].
  specialize (H x (option_map_default f d a)).
  apply H.
  rewrite in_map_iff.
  exists (x, a).
  split.
  - reflexivity.
  - apply Hin.
Qed.

Definition add_to_map_from_prod {A} (f : string -> bool) (m : smap.t (list A)) (e : string * A) : smap.t (list A) :=
  match e with
  | (x, a) =>
    if f x then
      let prev := 
        match smap.find x m with
        | Some prev => prev
        | None => nil
        end in
      smap.add x (a :: prev) m
    else m
  end.

Definition map_from_prod_list {A} (f : string -> bool) (l : list (string * A)) : smap.t (list A) :=
  fold_left (add_to_map_from_prod f) l smap.empty.

Definition filter_pair_on_key {A} (x : string) (l : list (string * A)) : list A :=
    flat_map_option (fun a => if (fst a =? x)%string then Some (snd a) else None) l.

Lemma filter_pair_on_key_spec (A : Type) :
  forall (l : list (string * A)) x a,
    In a (filter_pair_on_key x l) <-> In (x, a) l.
Proof.
  intros l x a.
  unfold filter_pair_on_key.
  rewrite in_flat_map_option.
  split; intros H.
  - destruct H as [[x' a'] [Hin Hxa]].
    simpl in Hxa.
    destruct (x' =? x)%string eqn:Hxx'.
    + inversion Hxa. rewrite String.eqb_eq in Hxx'.
      now subst.
    + discriminate Hxa.
  - exists (x, a).
    split.
    + assumption.
    + simpl. destruct (x =? x)%string eqn:Hxx'.
      * reflexivity.
      * rewrite String.eqb_neq in Hxx'; contradiction.
Qed.

Lemma filter_pair_on_key_no_x :
  forall A (l : list (string * A)) x,
    (forall a, ~ In (x, a) l)
      <->
    filter_pair_on_key x l = nil.
Proof.
  intros A l x.
  setoid_rewrite <- filter_pair_on_key_spec.
  destruct filter_pair_on_key as [|a fl];
  split; intros H; try easy.
  specialize (H a).
  simpl in H.
  exfalso.
  apply H.
  left. reflexivity.
Qed.

Definition map_from_prod_list_P {A} (f : string -> bool) (l : list (string * A)) (m : smap.t (list A)) :=
  forall x, 
  match smap.find x m with
  | None => f x = false \/ forall a, ~ In (x, a) l
  | Some al => al <> nil /\ f x = true /\ forall a, In a al <-> In (x, a) l 
  end.

Lemma map_from_prod_list_spec :
  forall A f (l : list (string * A)),
  map_from_prod_list_P f l (map_from_prod_list f l).
Proof.
  intros A f l.
  enough (map_from_prod_list_P f (rev l) (map_from_prod_list f l)).
  {
    unfold map_from_prod_list_P in *.
    specialize in_rev as Hrev.
    intros x; specialize (H x).
    destruct (smap.find x).
    - setoid_rewrite in_rev at 2; apply H.
    - setoid_rewrite in_rev. apply H. 
  }
  unfold map_from_prod_list.
  rewrite <- fold_left_rev_right.
  apply fold_ind.
  - unfold map_from_prod_list_P.
    intros x.
    rewrite smap.empty_spec.
    right. intros a Hin.
    destruct Hin.
  - clear l. intros [x a] m l.
    unfold map_from_prod_list_P.
    intros IH.
    intros x'.
    unfold add_to_map_from_prod.
    destruct (f x) eqn:Hfx. 
    { 
      destruct (String.string_dec x x') as [Hxx' | Hxx'].
      - subst x'.
        rewrite smap.add_spec1.
        split; try easy.
        split; try assumption.
        intros a'.
        specialize (IH x).
        destruct (smap.find x m) as [l'|] eqn:Hfind.
        (* This stuff should really be automated... *)
        + specialize IH as (_ & _ & IH).
          simpl. rewrite IH.
          split; intros H; destruct H;
          try inversion H;
          try subst; try now left.
          all: try now right.
        + destruct IH as [IH|IH]; try now rewrite Hfx in IH.
          split; intros H.
          * destruct H.
            -- subst. left. reflexivity.
            -- destruct H.
          * destruct H.
            -- inversion H; subst.
              left. reflexivity.
            -- exfalso. specialize (IH a'). apply IH.
              exact H. 
      - rewrite smap.add_spec2;
        try assumption. 
        specialize (IH x').
        destruct (smap.find) as [l'|].
        + split; try apply IH.
          split; try apply IH.
          specialize IH as (_ & _ & IH).
          intros a'. rewrite IH.
          split; intros H.
          * right. assumption.
          * destruct H as [Hfalse | Hin].
            -- inversion Hfalse; subst; contradiction.
            -- exact Hin.   
        + destruct IH.
          * left. assumption.
          * right. intros a'.
            rewrite not_in_cons.
            split.
            -- intros Hfalse; inversion Hfalse; subst; contradiction.
            -- apply H.
    }
    {
      specialize (IH x').
      destruct (smap.find x' m) as [l'|].
      - split; try apply IH.
        split; try apply IH.
        intros a'.
        split; intros H.
        + right. apply IH. exact H.
        + destruct H;
          destruct IH as (IHnnil & IHf & IHin).
          * inversion H; subst.
            rewrite Hfx in IHf.
            discriminate IHf.
          * rewrite IHin. apply H.
      - destruct (String.string_dec x x') as [Hxx' | Hxx'].
        + subst x'. left. exact Hfx.
        + destruct IH as [IH|IH].
          * left. exact IH.
          * right. intros a'.
            intros [Heq | Hl].
            -- inversion Heq; subst.
              contradiction.
            -- specialize (IH a').
              apply IH. exact Hl.
    }
Qed.  

Lemma in_map_prod_list :
  forall A f (l : list (string * A)) al x,
    In (x, al) (smap.bindings (map_from_prod_list f l))
      ->
    al <> nil
      /\
    forall a, In a al <-> In a (filter_pair_on_key x l).
Proof.
  intros A f l al x.
  intros Hin.
  rewrite smap_in_spec in Hin.
  specialize map_from_prod_list_spec with (f := f) (l := l) as Hspec.
  specialize (Hspec x).
  rewrite <- smap.find_spec in Hin.
  rewrite Hin in Hspec.
  split; try apply Hspec.
  destruct Hspec as (_ & _ & Hinl).
  setoid_rewrite Hinl.
  intros a.
  rewrite filter_pair_on_key_spec. reflexivity.
Qed.

Lemma is_empty_map_exists :
  forall A (m : smap.t A),
    smap.is_empty m = false
      ->
    exists x, smap.In x m.
Proof.
  intros A m.
  intros Hempty.
  rewrite <- not_true_iff_false in Hempty.
  rewrite smap.is_empty_spec in Hempty.
  destruct (smap.exists_ (fun x y => true) m) eqn:Hx.
  + rewrite smap.exists_spec in Hx.
    rewrite existsb_exists in Hx.
    destruct Hx as [[x a] [H _]].
    rewrite In_to_InA_Duo_eq in H.
    rewrite smap.bindings_spec1 in H.
    exists x. exists a.
    exact H.
  + exfalso.
    apply Hempty.
    intros x.
    rewrite smap.exists_spec in Hx.
    rewrite <- not_true_iff_false in Hx.
    destruct (smap.find x m) eqn:Hfind; try reflexivity.
    rewrite existsb_exists in Hx.
    exfalso.
    apply Hx.
    exists (x, a).
    split; try reflexivity.
    rewrite In_to_InA_Duo_eq.
    rewrite smap.bindings_spec1.
    rewrite <- smap.find_spec.
    exact Hfind.
Qed.

Lemma find_none_bindings :
  forall A (m : smap.t A) x,
    smap.find x m = None
      ->
    forall a, ~ In (x, a) (smap.bindings m).
Proof.
  intros A m x.
  intros Hfind.
  intros a Hin.
  rewrite In_to_InA_Duo_eq in Hin.
  rewrite smap.bindings_spec1 in Hin.
  rewrite <- smap.find_spec in Hin.
  rewrite Hfind in Hin.
  discriminate Hin.
Qed.

Definition eq_key {K A} (x y : K * A) :=
  fst x = fst y.

Import SetoidList.

Lemma InA_eq_key_iff_In_map_fst {A K} :
  forall (l : list (K * A)) elt,
  In (fst elt) (map fst l) <-> InA eq_key elt l.
Proof.
  intros l elt.
  split; intros H.
  - rewrite in_map_iff in H.
    destruct H as (elt' & Helt' & Hin).
    apply In_InA with (eqA := eq_key) in Hin.
    + apply InA_eqA with (x := elt').
      * unfold eq_key. solve_equiv.
      * unfold eq_key. exact Helt'.
      * exact Hin.
    + unfold eq_key. solve_equiv.
  - induction l.
    + now rewrite InA_nil in H.
    + simpl. inversion H; subst.
      * left. symmetry. 
        assumption.
      * right. apply IHl.
        assumption.
Qed.

Lemma NoDup_fst_iff_map_fst {K A} :
  forall (l : list (K * A)),
    NoDupA eq_key l <-> NoDup (map fst l).
Proof.
  induction l.
  - split; intros H.
    + apply NoDup_nil.
    + apply NoDupA_nil.
  - simpl. rewrite NoDup_cons_iff.
    rewrite <- IHl.
    split; intros H.
    + inversion H; subst.
      split.
      * intros Hin.
        apply H2.
        apply InA_eq_key_iff_In_map_fst.
        exact Hin.
      * assumption.
    + apply NoDupA_cons.
      * intros HinA.
        apply H.
        apply InA_eq_key_iff_In_map_fst.
        exact HinA.
      * apply H.
Qed.

Lemma nodup_bindings_keys {A} : 
  forall (m : smap.t A), 
  NoDup (map fst (smap.bindings m)).
Proof.
  intros m.
  specialize (smap.bindings_spec2w m) as Hbind.
  unfold smap.eq_key in Hbind.
  remember (smap.bindings m) as l.
  clear -Hbind.
  rewrite <- NoDup_fst_iff_map_fst.
  apply Hbind.
Qed.

End Maps.

Module SortedEx.
Import List.
Import ListNotations.
Import Sorted.
Import Basics.

(** This reverse sorting comes from https://gitlab.mpi-sws.org/atrieu/stdpp/-/blob/coq-stdpp-1.2.1/theories/sorting.v?ref_type=tags Coq Std++ v1.2.1 commit 5f2a6b77c07004cb46379de3ccc07310094cbeec. Licensed under the 3-clause BSD license (https://opensource.org/licenses/BSD-3-Clause) *)
Inductive TlRel {A} (R : A -> A -> Prop) (a : A) : list A -> Prop :=
  | TlRel_nil : TlRel R a nil
  | TlRel_cons b l : R b a -> TlRel R a (l ++ b :: nil).

Lemma HdRel_reverse {A} R (l : list A) x : HdRel R x l -> TlRel (flip R) x (rev l).
Proof. 
  destruct 1.
  - apply TlRel_nil.
  - simpl. apply TlRel_cons. unfold flip. exact H.
Qed.

Lemma Sorted_snoc {A} R (l : list A) x : Sorted R l -> TlRel R x l -> Sorted R (l ++ x :: nil).
Proof.
  induction 1 as [|y l Hsort IH Hhd]; intros Htl; simpl.
  { repeat constructor. }
  constructor. apply IH.
  - inversion Htl as [|? [|??]]; subst; constructor; easy.
  - destruct Hhd; constructor; try easy.
    inversion Htl as [|? [|??]]; try easy.
    destruct l; easy.
Qed.

Lemma Sorted_reverse {A} R (l : list A) :
  Sorted R l -> Sorted (flip R) (rev l).
Proof.
  induction 1; try easy.
  simpl. apply Sorted_snoc; try assumption.
  apply HdRel_reverse; assumption.
Qed.

(** End code from Coq std++ *)

End SortedEx.
