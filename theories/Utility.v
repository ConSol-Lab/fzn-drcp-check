From Coq Require Lists.List.
From Coq Require Sorting.Sorted.
From Coq Require Sorting.Permutation.
Require Coq.ZArith.ZArith.
Require Coq.NArith.NArith.
Require Coq.Logic.FinFun.
Require Lia.
Require Coq.Structures.OrdersEx.
Require MMaps.Interface.
Require MMaps.RBT.

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

Module ListEx.
  Import List.
  Import Lia.
  Import Permutation.

Definition sub_list {A} (eq_dec : forall x y : A, {x = y}+{x <> y} ) (l1 l2 : list A) :=
  (forall a, In a l1 -> (count_occ eq_dec l1 a <= count_occ eq_dec l2 a)%nat).

Lemma sub_list_in {A} (eq_dec : forall x y : A, {x = y}+{x <> y})  :
  forall (l1 l2 : list A), sub_list eq_dec l1 l2 -> forall a, In a l1 -> In a l2.
Proof.
  intros l1 l2.
  intros Hsub.
  intros a Hin.
  unfold sub_list in Hsub.
  specialize (Hsub a Hin).
  destruct (in_dec eq_dec a l2) as [Hin2 | Hnin2].
  - exact Hin2.
  - rewrite count_occ_not_In in Hnin2.
    rewrite Hnin2 in Hsub.
    rewrite count_occ_In in Hin.
    exfalso.
    clear Hnin2.
    assert (count_occ eq_dec l1 a > 0)%nat.
    { exact Hin. }
    remember (count_occ eq_dec l1 a) as n.
    clear Heqn; clear eq_dec; clear a; clear l1; clear l2; clear A.
    lia.
Qed.

Definition eq_counts {A} (eq_dec : forall x y : A, {x = y}+{x <> y} ) (l1 l2 : list A) :=
  (forall a, (In a l1 \/ In a l2) -> (count_occ eq_dec l1 a = count_occ eq_dec l2 a)%nat).

Fixpoint remove_once {A} (eq_dec : forall x y : A, {x = y}+{x <> y}) (a : A) (l : list A) :=
  match l with
  | nil => nil
  | a' :: l' => if eq_dec a a'
                    then l'
                    else a' :: (remove_once eq_dec a l')
  end.

Lemma remove_once_one_less_count {A} (eq_dec : forall x y : A, {x = y}+{x <> y}) :
  forall l a, pred (count_occ eq_dec l a) = count_occ eq_dec (remove_once eq_dec a l) a. 
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

Ltac resolve_eq_dec_self a :=
  let T := type of a in
  match goal with
  | [ eq_dec : forall x y : T, {x = y} + {x <> y} |- _ ] =>
    let H := fresh "H" in
    destruct (eq_dec a a) as [H|H];
    [ clear H  (* clear the trivial a = a hypothesis *)
    | contradiction  (* resolve the contradictory a <> a case *)
    ]
  end.

Lemma remove_once_one_same_if_neq {A} (eq_dec : forall x y : A, {x = y}+{x <> y}) :
  forall l a a', a <> a' -> count_occ eq_dec l a' = count_occ eq_dec (remove_once eq_dec a l) a'. 
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
        resolve_eq_dec_self a.
        f_equal.
        apply IHl. exact Ha1a2.
    + destruct (eq_dec a1 a) as [| Ha1a].
      * subst a1. reflexivity.
      * simpl. destruct (eq_dec a a2).
        { subst a2. contradiction. }
        clear n.
        apply IHl. exact Ha1a2.
Qed. 

Lemma remove_once_one_In {A} (eq_dec : forall x y : A, {x = y}+{x <> y}) :
  forall l a a', In a' (remove_once eq_dec a l) -> In a' l. 
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

Lemma sub_list_if_in_nodup {A} (eq_dec : forall x y : A, {x = y}+{x <> y}) :
  forall l1 l2,
    (forall a, In a l1 -> In a l2)
      ->
    NoDup l1
      ->
    sub_list eq_dec l1 l2.
Proof.
  intros l1 l2.
  intros Hin Hnodup.
  intros a Hin1.
  assert (In a l2) by (apply Hin in Hin1; assumption).
  rewrite NoDup_count_occ' in Hnodup.
  specialize (Hnodup a Hin1). rewrite Hnodup.
  rewrite count_occ_In in H.
  assert (count_occ eq_dec l2 a > 0) by (exact H).
  lia.
Qed.

Lemma nodup_sublist {A} (eq_dec : forall x y : A, {x = y}+{x <> y}) :
  forall l1 l2,
    NoDup l2
      ->
    sub_list eq_dec l1 l2
      ->
    NoDup l1.
Proof.
  intros l1 l2. repeat rewrite NoDup_count_occ' with (decA := eq_dec). unfold sub_list. intros Hnodup Hsub.
  intros a Hin.
  pose proof Hin as Hge0.
  rewrite count_occ_In with (eq_dec := eq_dec) in Hge0.
  apply Hsub in Hin.
  destruct (in_dec eq_dec a l2) as [Hin2|Hnin2].
  + apply Hnodup in Hin2. lia.
  + rewrite count_occ_In with (eq_dec := eq_dec) in Hnin2.
    exfalso. lia.
Qed. 

Lemma filter_sublist {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) :
  forall pred (l : list A),
    sub_list eq_dec (filter pred l) l.
Proof.
  intros pred l.
  induction l.
  - simpl. intros a Hnil. destruct Hnil.
  - simpl. 
    assert (forall a', ~ In a' l -> ~ In a' (filter pred l)) as Hnotfilt.
    { intros a'. intros Hin. rewrite filter_In. destruct (pred a'); unfold not; intros H; apply Hin; apply H. }
    assert (forall a', pred a' = false -> ~ In a' (filter pred l)) as Hnotfilt2.
    { intros a' Hpred. rewrite filter_In. unfold not. intros H. destruct H as [_ Hfalse]. rewrite Hpred in Hfalse. discriminate Hfalse. }
    intros a'. destruct (pred a) eqn:Hpred; simpl; destruct (eq_dec a a') as [Haa' | Haa']; destruct (in_dec eq_dec a' l) as [Hla' | Hla']; destruct (pred a') eqn:Hpreda'; try assert (In a' l /\ pred a' = true) by (split; assumption); try rewrite <- filter_In in H; try apply IHl in H; try subst a'; try rewrite Hpreda' in Hpred; try discriminate Hpred; intros Hbad; try lia; try apply Hnotfilt in Hla' as Hla_filter'; try apply Hnotfilt2 in Hpreda'; try rewrite (count_occ_not_In eq_dec) in Hla'; try rewrite (count_occ_not_In eq_dec) in Hla_filter'; try rewrite (count_occ_not_In eq_dec) in Hpreda'; try lia.
Qed. 

Lemma count_occ_map {A B} (eq_dec_a : forall x y : A, {x = y} + {x <> y}) (eq_dec_b : forall x y : B, {x = y} + {x <> y}) :
  forall (f : A -> B) (l : list A) a,
  count_occ eq_dec_a l a <= count_occ eq_dec_b (map f l) (f a).
Proof.
  intros f. induction l.
  - intros a. simpl. reflexivity.
  - simpl. intros a'.
    destruct (eq_dec_a a a') as [Haa' | Haa'].
    + subst a'. destruct (eq_dec_b (f a) (f a)) as [_ |Hfalse]; try contradiction.
      specialize (IHl a). lia.
    + destruct (eq_dec_b (f a) (f a')) as [Hfa' | Hfa'].
      * specialize (IHl a'). lia.
      * apply IHl.
Qed.

Definition repeat_f {A} (f : A -> nat) (a : A) :=
  repeat a (f a).

Definition build_counts {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (f : A -> nat) :=
  concat (map (repeat_f f) (nodup eq_dec l)).

Lemma build_counts_zero {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) :
  forall f l a,
    ~ In a l
      ->
    count_occ eq_dec (build_counts eq_dec l f) a = 0.
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

Lemma build_counts_correct {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) :
  forall f l a,
    In a l
      ->
    count_occ eq_dec (build_counts eq_dec l f) a = f a.
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
        apply build_counts_zero with (eq_dec := eq_dec) (f := f) in Hnin. unfold build_counts in Hnin. rewrite Hnin.
        lia.
     * simpl. rewrite count_occ_app.
        unfold repeat_f at 1.
        rewrite count_occ_repeat_neq.
        -- simpl. apply IHl. exact Haa'.
        -- intros Ha_eq_a'.
          subst a'. apply Hnin.
          exact Haa'.
Qed.

Definition count_diff {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) (l_sub : list A) (a : A) :=
  count_occ eq_dec l a - count_occ eq_dec l_sub a.

Lemma sub_list_app_perm {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) :
  forall l1 l2,
    sub_list eq_dec l1 l2 <-> exists l1_diff, Permutation l2 (l1 ++ l1_diff).
Proof.
  intros l1 l2. split.
  - intros Hsub. unfold sub_list in Hsub.
    exists (build_counts eq_dec l2 (count_diff eq_dec l2 l1)).
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
  - intros H. destruct H as (l1_diff & Hperm).
    unfold sub_list.
    intros a Hin.
    rewrite Permutation_count_occ in Hperm.
    rewrite Hperm.
    rewrite count_occ_app. lia.
Qed.

Lemma sub_list_map {A B} (eq_dec_a : forall x y : A, {x = y} + {x <> y}) (eq_dec_b : forall x y : B, {x = y} + {x <> y}) :
  forall (f : A -> B) (l1 l2 : list A),
  sub_list eq_dec_a l1 l2
    ->
  sub_list eq_dec_b (map f l1) (map f l2).
Proof.
  intros f l1 l2 Hsub.
  rewrite sub_list_app_perm.
  rewrite sub_list_app_perm in Hsub.
  destruct Hsub as (l1_diff & Hperm).
  exists (map f l1_diff).
  rewrite <- map_app.
  apply Permutation_map.
  exact Hperm.
Qed.

Lemma permutation_partition {A} :
  forall (f : A -> bool) l,
  Permutation l (fst (partition f l) ++ snd (partition f l)).
Proof.
  intros f l.
  repeat rewrite partition_as_filter. simpl.
  induction l.
  - simpl. apply perm_nil.
  - simpl. destruct (f a) eqn:Hfa.
    + simpl. apply perm_skip. apply IHl.
    + simpl. remember (filter (fun x : A => negb (f x)) l) as l1; clear Heql1.
      remember (filter f l) as l2; clear Heql2.
      apply Permutation_cons_app.
      exact IHl.
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

Lemma nodup_map (A B : Type) (eq_dec : forall x y : A, {x = y}+{x <> y}) (eq_dec_b : forall x y : B, {x = y}+{x <> y}) :
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
  intros f l Hnodup.
  intros a1 a2 Hin1 Hin2 Hf.
  destruct (eq_dec a1 a2) as [Heq | Hneq].
  - exact Heq.
  - exfalso.
    apply in_split in Hin1.
    destruct Hin1 as [l1 [l2 Hl]].
    subst l.
    apply in_app_or in Hin2.
    destruct Hin2 as [Hin2 | Hin2].
    + apply in_split in Hin2.
      destruct Hin2 as [l3 [l4 Hl]].
      subst l1.
      repeat rewrite map_app in Hnodup.
      simpl in Hnodup.
      rewrite (NoDup_count_occ eq_dec_b) in Hnodup.
      specialize (Hnodup (f a1)).
      repeat rewrite count_occ_app in Hnodup.
      rewrite count_occ_cons_eq in Hnodup; try easy.
      rewrite count_occ_cons_eq in Hnodup; try easy. 
      lia.
    + destruct Hin2 as [Hfalse | Hin2]; try contradiction.
      apply in_split in Hin2.
      destruct Hin2 as [l3 [l4 Hl]].
      subst l2.
      repeat rewrite map_app in Hnodup.
      simpl in Hnodup.
      repeat rewrite map_app in Hnodup.
      simpl in Hnodup.
      rewrite (NoDup_count_occ eq_dec_b) in Hnodup.
      specialize (Hnodup (f a1)).
      repeat rewrite count_occ_app in Hnodup.
      rewrite count_occ_cons_eq in Hnodup; try easy.
      repeat rewrite count_occ_app in Hnodup.
      rewrite count_occ_cons_eq in Hnodup; try easy. 
      lia.
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

End ListEx.


Module NatEx.
  Import Lia.

  Lemma S_pred_gt_0 :
    forall (n : nat), n > 0 -> S (pred n) = n.
  Proof.
    intros n Hngt.
    lia.
  Qed.

  Lemma S_lt :
    forall n m, S n <= S m -> n <= m.
  Proof.
    intros n m H.
    lia.
  Qed.
  
End NatEx.


Module ZRange.
  Import ZArith.
  Import NArith.
  Import FinFun.
  Import List.
  Import Lia.
  Import Sorted.

Definition is_succ (n : Z) (m : Z) :=
  n = Z.succ m.

Definition succ_seq (l : list Z) :=
  Sorted is_succ l.

Lemma succ_seq_sorted_le (l : list Z) :
  succ_seq l -> StronglySorted Z.gt l.
Proof.
  intros Hsucc.
  assert (Sorted Z.gt l).
  {
    unfold succ_seq in Hsucc.
    induction l.
    - apply Sorted_nil.
    - inversion Hsucc; subst a0; subst l0.
      apply IHl in H1.
      apply Sorted_cons.
      + exact H1.
      + inversion H2.
        * apply HdRel_nil.
        * apply HdRel_cons.
          clear Hsucc; clear IHl; clear H1; clear H2; clear H0.
          unfold is_succ in H.
          lia.
  }
  apply Sorted_StronglySorted.
  - unfold Relations_1.Transitive.
    intros.
    (* TODO: replace with the actual lemma *)
    lia.
  - exact H.
Qed.
  

Open Scope Z_scope.
Definition is_range (s : Z) (e : Z) (l : list Z) :=
  s <= e
    /\
  (forall n, s <= n <= e <-> In n l)
    /\
  succ_seq l.

Lemma is_range_In (s e : Z) (l : list Z) :
  is_range s e l
    ->
  forall n, In n l <-> s <= n <= e.
Proof.
  intros Hrange.
  intros n.
  unfold is_range in Hrange.
  symmetry. apply Hrange.
Qed.

Lemma is_range_endpoints :
  forall l s e a a',
    is_range s e (a :: a' :: l)
      ->
    a = e /\ a' = e - 1.
Proof.
  intros l s e a a'.
  intros Hrange.
  unfold is_range in *.
  destruct Hrange as [Hse [Hin Hsucc]].
  destruct (a =? e) eqn:Hae.
  2: { 
    rewrite Z.eqb_neq in Hae. 
    assert (In a (a :: a' :: l)) as Hain.
    { simpl. left. reflexivity. }
    rewrite <- Hin in Hain.
    assert (s <= e <= e) as Hsee by lia.
    rewrite Hin in Hsee.
    unfold succ_seq in Hsucc.
    apply succ_seq_sorted_le in Hsucc.
    inversion Hsucc; subst a0; subst l0.
    exfalso.
    rewrite Forall_forall in H2.
    assert (In e (a' :: l)).
    { destruct Hsee; try contradiction. exact H. }
    apply H2 in H.
    clear Hin; clear Hsucc; clear H1; clear H2; clear Hsee.
    lia.
  }
  rewrite Z.eqb_eq in Hae; subst a.
  assert (a' = e - 1).
  {
    inversion Hsucc.
    inversion H2.
    unfold is_succ in H4.
    rewrite H4.
    lia.
  }
  subst a'.
  split; reflexivity.
Qed.

Lemma is_range_implies_pred_range :
  forall l s e a a',
    is_range s e (a :: a' :: l)
      ->
    is_range s (e - 1) (e - 1 :: l).
Proof.
  intros l s e a a'.
  intros Hrange.
  assert (is_range s e (a :: a' :: l)) as Haa' by assumption.
  apply is_range_endpoints in Haa'.
  destruct Haa' as [Ha Ha'].
  subst a; subst a'.
  unfold is_range in *.
  destruct Hrange as [Hse [Hin Hsucc]].
  assert (In (e - 1) (e :: e - 1 :: l)).
  { simpl; right; left; reflexivity. }
  rewrite <- Hin in H.
  split.
  + apply H.
  + split.
    * intros n. split.
      -- intros Hn. 
        assert (s <= n <= e) as Hsne by lia.
        rewrite Hin in Hsne.
        destruct Hsne as [| Hsne]; try lia.
        exact Hsne.
      -- intros Hinless.
        assert (In n (e :: e - 1 :: l)) as Hinall.
        { destruct Hinless.
          - subst n; simpl; right; left; reflexivity.
          - simpl; right; right; exact H0. }
        rewrite <- Hin in Hinall.
        assert (n <= e - 1) as Hnminus1.
        {
          apply succ_seq_sorted_le in Hsucc.
          inversion Hsucc; subst l0; subst a; clear H2.
          rewrite Forall_forall in H3.
          apply H3 in Hinless.
          clear Hin; clear Hse; clear Hsucc; clear H; clear H3; clear Hinall.
          lia.
        }
        destruct Hinall as [Hsn _].
        split.
        ++ exact Hsn.
        ++ exact Hnminus1.
    * inversion Hsucc.
      exact H2.
Qed.

Lemma is_range_1el_s_is_e :
  forall s e a, 
    is_range s e (a :: nil)
      ->
    a = s
      /\
    s = e.
Proof.
  intros s e a.
  intros Hrange.
  destruct Hrange as [Hse_le [Hn Hsucc]].
  assert (s <= s <= e) as Hsse by lia.
  assert (s <= e <= e) as Hsee by lia.
  rewrite Hn in Hsse.
  rewrite Hn in Hsee.
  destruct Hsse as [Hsa | Hsa]; try destruct Hsa.
  destruct Hsee as [Hea | Hea]; try destruct Hea.
  split; reflexivity.
Qed.
        
Lemma is_range_length :
  forall l s e,
    is_range s e l
      ->
    length l = S (Z.to_nat (e - s)).
Proof.
  induction l.
  - intros s e Hrange.
    unfold is_range in Hrange.
    destruct Hrange as [Hse_le [Hn _]].
    assert (s <= s <= e) by lia.
    rewrite Hn in H. destruct H.
  - intros s e.
    intros Hrange.
    destruct l as [| a' l].
    + apply is_range_1el_s_is_e in Hrange.
      destruct Hrange as [Ha He].
      subst e; subst a.
      simpl.
      lia.
    + assert (is_range s e (a :: a' :: l)) as Haa' by assumption.
      assert (is_range s e (a :: a' :: l)) as Hslte by assumption.
      apply is_range_endpoints in Haa'.
      destruct Haa' as [Ha Ha'].
      subst a; subst a'.
      apply is_range_implies_pred_range in Hrange.
      apply IHl in Hrange.
      clear IHl.
      unfold is_range in Hslte.
      destruct Hslte as [_ [Hn _]].
      assert (In (e - 1) (e :: e - 1 :: l)).
      { simpl; right; left; reflexivity. }
      rewrite <- Hn in H; clear Hn.
      simpl in *.
      rewrite Hrange; clear Hrange.
      lia.
Qed.

Lemma nth_cons {A} :
  forall (l : list A) n (d : A) (a : A),
    nth n l d = nth (S n) (a :: l) d.
Proof.
  intros l n d a.
  simpl. 
  reflexivity.
Qed.

Lemma range_nth :
  forall l s e n d,
    s <= e - Z.of_nat n
      ->
    is_range s e l
      ->
    nth n l d = e - Z.of_nat n.
Proof.
  induction l.
  - intros s e n d.
    intros Hs_low Hrange.
    destruct Hrange as [Hse [Hin Hsucc]].
    assert (s <= s <= e) as Hsse by lia.
    rewrite Hin in Hsse. destruct Hsse.
  - intros s e n d.
    intros Hsne Hrange.
    destruct l as [| a' l].
    + apply is_range_1el_s_is_e in Hrange.
      destruct Hrange as [Ha He].
      subst e; subst a.
      assert (n = 0)%nat by lia.
      subst n.
      simpl.
      lia.
    + apply is_range_endpoints in Hrange as Hendpoints.
      apply is_range_implies_pred_range in Hrange as Hpred_range.
      destruct Hendpoints as [Ha Ha'].
      subst a; subst a'.
      destruct (n =? 0)%nat eqn:Hn0.
      {
        rewrite Nat.eqb_eq in Hn0; subst n.
        simpl. lia. 
      }
      rewrite Nat.eqb_neq in Hn0.
      apply IHl with (n := pred n) (d := d) in Hpred_range as Hnth; try lia.
      clear IHl; clear Hpred_range.
      destruct n; try contradiction.
      rewrite <- nth_cons.
      assert (pred (S n) = n) by reflexivity; rewrite H in Hnth; clear H.
      rewrite Hnth.
      lia.
Qed.

Lemma nth_error_some_len_ltn {A} :
  forall (l : list A) n a,
    nth_error l n = Some a
      ->
    (n < length l)%nat.
Proof.
  induction l.
  - intros. rewrite nth_error_nil in H. discriminate H.
  - simpl. intros n a' Hnth.
    destruct n.
    + lia.
    + rewrite nth_error_S in Hnth. simpl in Hnth.
      apply IHl in Hnth.
      lia.
Qed.

Lemma range_nth_error {A} :
  forall (fz : A -> Z) l s e n a,
    ZRange.is_range s e (map fz l)
      ->
    nth_error (map fz l) n = Some (fz a)
      ->
    fz a = e - Z.of_nat n.
Proof.
  intros fz l s e n a.
  intros Hrange Hnth.
  apply is_range_length in Hrange as Hlen.
  assert (n < length (map fz l))%nat.
  { apply nth_error_some_len_ltn in Hnth. assumption. }
  apply (range_nth (map fz l) s e n Z0) in Hrange as Hrange_nth;
  destruct Hrange as [Hse [Hin Hsucc]].
  2: { lia. }
  apply nth_error_nth with (d := Z0) in Hnth.
  rewrite <- Hnth.
  rewrite <- Hrange_nth.
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
Lemma range_f_l {A} :
  forall (f : Z -> A) s e l n (d : A),
    s <= e - Z.of_nat n
      ->
    is_range s e l
      ->
    f (e - Z.of_nat n) = nth n (map f l) d.
Proof.
  intros f s e l n d.
  intros Hs_low Hrange.
  apply range_nth with (l := l) (d := 0) in Hs_low as Hrange_nth; try assumption.
  assert (n < length l)%nat.
  { 
    apply is_range_length in Hrange as Hlength.
    lia.
  }
  rewrite <- Hrange_nth.
  apply map_nth_len_lt.
  exact H.
Qed.



Fixpoint build_range_rec (s : Z) (n : nat) : list Z :=
  match n with
  | O => s :: nil
  | S n' => (s + Z.of_nat n) :: (build_range_rec s n')
  end.

Definition build_range_size (s : Z) (n : nat) : list Z :=
  match n with
  | O => nil
  | S n' => build_range_rec s n'
  end.

Definition build_range (s : Z) (e : Z) : list Z :=
  build_range_size s (Z.to_nat (e - s + 1)).

Lemma build_range_s :
  forall l size,
  build_range_size l (S size) = (l + Z.of_nat size) :: build_range_size l size.
Proof.
  intros l size.
  unfold build_range_size.
  destruct size.
  - simpl. assert (l + 0 = l) by lia. rewrite H. reflexivity.
  - simpl. reflexivity. 
Qed.

Lemma build_range_interval :
  forall s size,
    (size >= 1)%nat ->
    (forall n : Z,
    s <= n <= s + Z.of_nat size - 1 <->
    In n (build_range_size s size)).
Proof.
  intros s size Hsize.
  induction size.
  - exfalso. lia.
  - destruct (size =? 0)%nat eqn:H0.
    {
      rewrite Nat.eqb_eq in H0; subst size; clear Hsize.
      simpl in *; clear IHsize.
      assert (s + 1 - 1 = s).
      { lia. }
      rewrite H; clear H.
      intros n.
      split.
      - intros H.
        assert (n = s).
        { lia. }
        subst s.
        left. reflexivity.
      - intros H.
        destruct H; try contradiction.
        subst s.
        split; reflexivity.
    }
    intros n.
    assert (size >= 1)%nat as IH.
    { rewrite Nat.eqb_neq in H0. lia. }
    clear H0; apply IHsize with (n := n) in IH; clear IHsize; clear Hsize.
    assert (s + Z.of_nat (S size) - 1 = s + Z.of_nat size).
    { lia. }
    rewrite H; clear H.
    split.
    -- intros H. rewrite build_range_s.
      destruct (n =? s + Z.of_nat size) eqn:Hs.
      ++ rewrite Z.eqb_eq in Hs; subst n.
        simpl. left. reflexivity.
      ++ rewrite Z.eqb_neq in Hs.
        assert (s <= n <= s + Z.of_nat size - 1) as IHn by lia.
        rewrite IH in IHn; clear IH.
        simpl. right. exact IHn.
    -- intros H. rewrite build_range_s in H.
      destruct H as [Hn | Hin].
      ++ subst n. clear IH. lia.
      ++ rewrite <- IH in Hin; clear IH.
        lia.
Qed.

Lemma build_range_size_correct : 
  forall l size,
      (size >= 1)%nat ->
      is_range l (l + Z.of_nat size - 1) (build_range_size l size).
Proof.
  intros l size Hsize.
  unfold is_range.
  split.
  - lia.
  - induction size.
    + exfalso. lia.
    + split.
      { apply build_range_interval. exact Hsize. }
      destruct (size =? 0)%nat eqn:H0.
      {
        rewrite Nat.eqb_eq in H0; subst size; clear Hsize.
        simpl in *; clear IHsize.
        unfold succ_seq. 
        apply Sorted_cons.
        - apply Sorted_nil.
        - apply HdRel_nil.
      }
      (* I don't think this is actually necessary... *)
      destruct (size =? 1)%nat eqn:H1.
      { 
        rewrite Nat.eqb_eq in H1; subst size; clear Hsize.
        simpl in *; clear IHsize.
        unfold succ_seq.
        apply Sorted_cons.
        - apply Sorted_cons.
          + apply Sorted_nil.
          + apply HdRel_nil.
        - apply HdRel_cons.
          unfold is_succ. 
          reflexivity.
      }
      assert (size >= 2)%nat as Hsize2.
      { rewrite Nat.eqb_neq in H0. rewrite Nat.eqb_neq in H1. lia. }
      assert (size >= 1)%nat as IH by lia.
      clear H0; clear H1; apply IHsize in IH; clear IHsize; clear Hsize.
      destruct IH as [_ IHsucc].
      rewrite build_range_s.
      assert (exists size', S (S size') = size).
      { exists (pred (pred size)). lia. }
      destruct H as [size' Hsize'].
      unfold succ_seq.
      apply Sorted_cons.
      * apply IHsucc.
      * rewrite <- Hsize'.
        rewrite build_range_s.
        apply HdRel_cons.
        unfold is_succ. lia.
Qed.

Lemma build_range_correct : 
  forall s e,
      s <= e
        ->
      is_range s e (build_range s e).
Proof.
  intros s e.
  intros Hse.
  unfold build_range.
  specialize (build_range_size_correct s (Z.to_nat (e - s + 1))) as Hsize_correct.
  assert ((s + Z.of_nat (Z.to_nat (e - s +
  1)) - 1) = e) by lia.
  rewrite H in Hsize_correct; clear H.
  apply Hsize_correct; clear Hsize_correct.
  lia.
Qed.

Lemma build_range_In_bounds :
  forall s e n,
    In n (build_range s e) -> s <= e.
Proof.
  intros s e n.
  intros Hin.
  unfold build_range in Hin.
  destruct (s <=? e) eqn:Hse.
  - rewrite <- Z.leb_le. exact Hse.
  - assert (Z.to_nat (e - s + 1) = O).
    { lia. }
    rewrite H in Hin. simpl in Hin.
    contradiction.
Qed.


(* Lemma build_range_nodup :
  forall s e,
    NoDup (build_range s e).
Proof.
  intros s e.
  unfold build_range.
  unfold shift_list.
  apply Injective_map_NoDup.
  - apply shift_inj.
  - apply list_helper_correct.
Qed. *)

Open Scope nat_scope.
Fixpoint has_n_true (n : nat) (l : list bool) (current : nat) : bool :=
  if (n <=? current)
    then true
    else
      match l with
      | nil => false
      | b :: l' =>
        if b
          then has_n_true n l' (S current) 
          else has_n_true n l' 0 
      end
.


End ZRange.

Module Maps.
Import String.
Import List.
Import ListInd.
Module smap := RBT.Make OrdersEx.String_as_OT.

Definition build_map_step {A B} (f_key : A -> string) (f : A -> B) (a : A) (m : smap.t B) :=
  smap.add (f_key a) (f a) m
.

Definition build_map_rec {A B} (f_key : A -> string) (f : A -> B) (l : list A) (init : smap.t B) :=
  fold_left (fun x y => build_map_step f_key f y x) l init.
(* 
Definition exists_unique {A} (a : A) (l : list A) (P : A -> Prop) :=
  exists a, In a l /\ P a /\
    forall a', In a' l /\ P a /\ a = a'. *)
(* forall vs sol x atoms_from_var, smap.MapsTo x atoms_from_var (vars_to_atoms vs) ->
    exists v, In v vs /\ var_name v = x /\ atoms_hold_for_var atoms_from_var sol v.
P *)

Lemma build_map_as_right :
  forall A B (f_key : A -> string) (f : A -> B) (l : list A) init,
  build_map_rec f_key f l init = fold_right (build_map_step f_key f) init (rev l).
Proof.
  intros A B f_key f l init.
  unfold build_map_rec. rewrite fold_left_rev_right. reflexivity.
Qed.

Definition build_map {A B} (f_key : A -> string) (f : A -> B) (l : list A) :=
  build_map_rec f_key f l smap.empty.

Lemma build_map_maps_to :
  forall A B f_key (f : A -> B) (l : list A) x b,
  smap.MapsTo x b (build_map f_key f l)
    ->
  exists a, In a l /\ f_key a = x /\ f a = b.
Proof.
  intros A B f_key f l x b.

  set (P :=
    fun (s : list A) (acc : smap.t B) =>
      smap.MapsTo x b acc
        ->
      exists a, In a s /\ f_key a = x /\ f a = b 
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
    destruct (String.string_dec x (f_key a)) as [Hxa| Hxa].
    + rewrite <- Hxa in *.
      rewrite smap.add_spec1 in H.
      inversion H.
      exists a.
      split; [|split].
      * left. reflexivity.
      * rewrite Hxa. reflexivity.
      * reflexivity.
    + rewrite smap.add_spec2 in H.
      2: { symmetry. exact Hxa. }
      rewrite smap.find_spec in H.
      apply IH in H.
      destruct H as (a' & Hin & Hfkey & Hfb).
      exists a'.
      repeat split; try assumption.
      right. exact Hin.
Qed.





(* Definition P {A B} (f_key : A -> string) (f : A -> B) (l : list A) (a : smap.t B) :=
  NoDup (map f_key l)
    ->
  forall x b, In (x, b) (smap.bindings a)
    ->
  exists a, In a l /\ f_key a = x /\ f a = b.
 *)
(* Lemma initialize_smap {A B} :
  forall (f_key : A -> string) (f : A -> B) (l : list A),
    NoDup (map f_key l)
      ->
    forall x b, In (x, b) (smap.bindings (build_map_rec f_key f l smap.empty))
      ->
    exists a, In a l /\ f_key a = x /\ f a = b /\ smap.MapsTo x 
   *)


Definition add_to_map {U}  (elt : string * U) (m : smap.t U) :=
  match elt with
  | (x, u) => smap.add x u m
  end.

Definition param_map {U} (l : list (string * U)) (d : U) : string -> U :=
  let map := fold_right add_to_map smap.empty l in
  fun x =>
    match smap.find x map with
    | Some u => u
    | None => d
    end.


Lemma param_map_in {U} :
  forall (d : U) x (l : list (string * U)) (u : U), 
  u = (param_map l d) x
    ->
  In x (map fst l)
    ->
  In (x, u) l.
Proof.
  intros d x. induction l.
  - intros u. intros H Hin.
    destruct Hin.
  - intros u. 
    unfold param_map in *.
    intros Hu. simpl in Hu.
    destruct a as [x' u'].
    intros Hin.
    simpl in Hin.
    destruct Hin as [Hxx' | Hxinl].
    + subst x'.
      unfold add_to_map in Hu.
      rewrite smap.add_spec1 in Hu.
      subst u'.
      left. reflexivity.
    + destruct (x =? x')%string eqn:Hxx'.
      { rewrite String.eqb_eq in Hxx'; subst x'.
        unfold add_to_map in Hu.
        rewrite smap.add_spec1 in Hu.
        subst u'.
        left. reflexivity. }
      rewrite String.eqb_neq in Hxx'.
      unfold add_to_map in Hu.
      rewrite smap.add_spec2 in Hu.
      * apply IHl in Hu; clear IHl.
        -- right. exact Hu.
        -- exact Hxinl.
      * intros Hxix'.
        apply Hxx'.
        symmetry. exact Hxix'.
Qed.
       
End Maps.