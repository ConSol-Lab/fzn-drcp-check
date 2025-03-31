From Coq Require Lists.List.
From Coq Require Sorting.Sorted.
Require Coq.ZArith.ZArith.
Require Coq.NArith.NArith.
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
  Import NArith.
  Import FinFun.
  Import List.
  Import Lia.
  Import Sorted.

Lemma not_sn_le_n :
  forall n,
    ~ (S n <= n).
Proof.
  induction n.
  - intros H. inversion H.
  - intros H. apply le_S_n in H. apply IHn.
    exact H.
Qed.


(* Fixpoint build_list_helper (n : nat) : list nat :=
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
Qed. *)

(* Alternative: replace this by something that proves termination: see e.g. http://adam.chlipala.net/cpdt/html/Cpdt.GeneralRec.html https://stackoverflow.com/questions/10292421/error-in-defining-ackermann-in-coq *)
(* Definition build_range (start_incl : Z) (end_incl : Z) : list Z :=
  shift_list start_incl (build_list_helper (Z.abs_nat (end_incl - start_incl))). *)

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
    + simpl in *.
      destruct (s =? e) eqn:Hse.
      {
        rewrite Z.eqb_eq in Hse; subst e.
        clear Hrange; clear IHl.
        lia.
      }
      rewrite Z.eqb_neq in Hse.
      clear IHl.
      destruct Hrange as [Hse_le [Hn Hsucc]].
      assert (s <= s <= e) as Hsse by lia.
      assert (s <= e <= e) as Hsee by lia.
      rewrite Hn in Hsse.
      rewrite Hn in Hsee.
      destruct Hsse as [Hsse | Hsse]; try destruct Hsse.
      destruct Hsee as [Hsee | Hsee]; try destruct Hsee.
      contradiction.
    + destruct l as [| a'' l].
      { admit. }
      (* destruct (a =? a') eqn:Haa'.
      {
        clear IHl.
        exfalso. 
        rewrite Z.eqb_eq in Haa'.
        subst a'.
        destruct Hrange as [_ [_ Hsucc]].
        inversion Hsucc; subst a0; subst l0.
        inversion H2; subst b; subst l0.
        unfold is_succ in H0.
        clear Hsucc; clear H1; clear H2.
        lia.
      }
      rewrite Z.eqb_neq in Haa'. *)
      assert (is_range s (e - 1) l).
      {
        clear IHl.
        unfold is_range in *.
        destruct Hrange as [Hse [Hin Hsucc]].
        destruct (a =? e) eqn:Hae.
        2: { 
          rewrite Z.eqb_neq in Hae. 
          assert (In a (a :: a' :: a'' :: l)) as Hain.
          { simpl. left. reflexivity. }
          rewrite <- Hin in Hain.
          assert (s <= e <= e) as Hsee by lia.
          rewrite Hin in Hsee.
          unfold succ_seq in Hsucc.
          apply succ_seq_sorted_le in Hsucc.
          inversion Hsucc; subst a0; subst l0.
          exfalso.
          rewrite Forall_forall in H2.
          assert (In e (a' :: a'' :: l)).
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
        assert (In a'' (e :: e - 1 :: a'' :: l)).
        { simpl; right; right; left; reflexivity. }
        rewrite <- Hin in H.
        assert (a'' = e - 2).
        {
          inversion Hsucc.
          inversion H2.
          inversion H7.
          unfold is_succ in H9.
          lia.
        }
        subst a''.
        split.
        * lia.
        * split.
          { 
            intros n. split.
            - intros Hn. 
              assert (s <= n <= e) as Hne by lia.
              rewrite Hin in Hne.
              destruct Hne as [Hne | Hne]; try lia.
              destruct Hne as [Hne | Hne]; try lia.
              destruct Hne as [Hne | Hne]; try lia.
        
        destruct (a' =? e - 1) eqn:Hae'.
        2: { 
          rewrite Z.eqb_neq in Hae'. 
          
          unfold 
          assert (In a' (e :: a' :: l)) as Hain.
          { simpl. right. left. reflexivity. }
          rewrite <- Hin in Hain.
          assert (s <= s <= e) as Hsse by lia.
          rewrite Hin in Hsse.
          exfalso.

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



        destruct (s =? e) eqn:Hse_eq.
        {
          rewrite Z.eqb_eq in Hse_eq; subst e; clear Hse.
          exfalso.
          assert (a <> a').
          {
            unfold succ_seq in Hsucc.
            inversion Hsucc; subst a0; subst l0.
            inversion H2; subst b; subst l0.
            unfold is_succ in H0.
            rewrite H0.
            lia.
          }
          assert (In a (a :: a' :: l)) as Hain.
          { simpl. left. reflexivity. }
          assert (In a' (a :: a' :: l)) as Hain'.
          { simpl. right. left. reflexivity. }
          rewrite <- Hin in Hain.
          rewrite <- Hin in Hain'.
          clear Hin; clear Hsucc.
          lia. 
        }
        rewrite Z.eqb_neq in Hse_eq.
        split.
        - clear Hin; clear Hsucc. lia.
        - split.
          + intros n.
            split.
            * intros Hn.



    }
  
  
  induction l.
  - 
  - simpl.



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

Inductive 

End ZRange.