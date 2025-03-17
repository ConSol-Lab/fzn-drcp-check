From Coq Require Lists.List.
Require Coq.ZArith.ZArith.
Require Coq.Logic.FinFun.
Require Lia.

Module ListEx.
  Import List.
  Import Lia.

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
  Import FinFun.
  Import List.
  Import Lia.

Lemma not_sn_le_n :
  forall n,
    ~ (S n <= n).
Proof.
  induction n.
  - intros H. inversion H.
  - intros H. apply le_S_n in H. apply IHn.
    exact H.
Qed.


Fixpoint build_list_helper (n : nat) : list nat :=
  match n with
  | 0 => 0 :: nil
  | S n' => n :: (build_list_helper n')
  end.

Lemma list_helper_correct : 
  forall N, 
    build_list_helper N <> nil /\
    NoDup (build_list_helper N) /\
    forall n, n <= N <-> In n (build_list_helper N).
Proof.
  intros N.
  induction N.
  - simpl. repeat split.
    + intros Hnnil. discriminate Hnnil.
    + apply NoDup_cons.
      * easy.
      * apply NoDup_nil.
    + left. inversion H. reflexivity.
    + intros H.
      destruct H.
      { subst n. reflexivity. }
      { contradiction. }
  - destruct IHN as [IHnonil [IHnodup IHin]].
    repeat split.
    + simpl. intros Hnil.
      discriminate Hnil.
    + simpl. apply NoDup_cons.
      * intros HSNin.
        rewrite <- IHin in HSNin.
        apply not_sn_le_n in HSNin.
        contradiction.
      * exact IHnodup.
    + intros Hlt.
      simpl.
      inversion Hlt.
      { left. reflexivity. }
      { subst m. right. apply IHin. exact H0. }
    + intros Hin.
      simpl in Hin.
      destruct Hin as [HSNn | Hin].
      { rewrite HSNn. reflexivity. }
      { rewrite <- IHin in Hin. apply le_S in Hin. exact Hin. }
Qed.

Definition shift_nat (c : Z) (n : nat) : Z := (Z.of_nat n) + c.

Lemma shift_inj : forall c,
  Injective (shift_nat c).
Proof.
  intros c.
  unfold Injective.
  intros n m Hshift.
  unfold shift_nat in Hshift.
  lia.
Qed.

Definition shift_list (shift : Z) (range : list nat) : list Z :=
  map (shift_nat shift) range.

Open Scope Z_scope.

Lemma shift_correct : 
  forall shift N Nz,
    Nz = (Z.of_nat N) ->
      forall n, shift <= n <= (Nz + shift) <-> In n (shift_list shift (build_list_helper N)).
Proof.
  intros shift N Nz.
  intros HNz.
  intros n.
  destruct (list_helper_correct N) as [_ [_ Hhelper]].
  unfold shift_list.
  rewrite in_map_iff.
  setoid_rewrite <- Hhelper.
  unfold shift_nat.
  split.
  - intros Hn.
    exists (Z.to_nat (n - shift)).
    lia.
  - intros Hex. destruct Hex as [x [Hx]].
    lia.
Qed.

(* Alternative: replace this by something that proves termination: see e.g. http://adam.chlipala.net/cpdt/html/Cpdt.GeneralRec.html https://stackoverflow.com/questions/10292421/error-in-defining-ackermann-in-coq *)
Definition build_range (start_incl : Z) (end_incl : Z) : list Z :=
  shift_list start_incl (build_list_helper (Z.abs_nat (end_incl - start_incl))).

Lemma build_range_correct : 
  forall s e,
    s <= e ->
      forall n, s <= n <= e <-> In n (build_range s e).
Proof.
  intros s e Hslte n.
  unfold build_range.
  specialize (shift_correct s (Z.abs_nat (e - s)) (e - s)) as Hshift.
  assert (e = e - s + s) as He.
  { lia. }
  rewrite He at 1.
  apply Hshift.
  lia.
Qed.

Lemma build_range_nodup :
  forall s e,
    NoDup (build_range s e).
Proof.
  intros s e.
  unfold build_range.
  unfold shift_list.
  apply Injective_map_NoDup.
  - apply shift_inj.
  - apply list_helper_correct.
Qed.

End ZRange.