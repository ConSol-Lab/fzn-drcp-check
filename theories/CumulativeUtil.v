Require Coq.NArith.NArith.
Require Coq.Strings.String.
Require Coq.Lists.List.
Require Checker.Utility.
Require Import Checker.Cumulative.
Require Lia.

Module ResourceSum.
  Import NArith.
  Import List.
  Import Lia.
  Import Utility.ListEx.
  Import Utility.NatEx.
  Import String.
  
  Open Scope N_scope.

  Definition sum_acc := (list (string * N) * N * bool)%type. 

  Definition f_capacity (capacity : N) (combined : list (string * N)) (new : N) : sum_acc :=
    (combined, new, new <=? capacity).

  Definition resource_sum_f (capacity : N) (acc : sum_acc) (a : (string * N)) : sum_acc :=
    match acc with
    | (_, _, false) => acc
    | (summed, current, _) =>
      f_capacity capacity (a :: summed) (current + (snd a))
    end
  .


Lemma resource_sum_f_correct : forall c a acc,
  match acc with
  | (summed, current, false) => resource_sum_f c acc a = (summed, current, false)
  | (summed, current, true) => 
    match resource_sum_f c acc a with
    | (summed_after, new, false) => 
      summed_after = a :: summed
        /\
      new = current + snd a
        /\
      new > c
    | (summed_after, new, true) =>
      summed_after = a :: summed
        /\
      new = current + snd a
        /\
      new <= c
    end
  end
  .
Proof.
  intros c a acc.
  destruct acc as [[s n] below].
  destruct below.
  - destruct (resource_sum_f c (s, n, true) a) as [[s_after n_after] below] eqn:Hres.
    unfold resource_sum_f in Hres.
    unfold f_capacity in Hres.
    destruct below.
    + inversion Hres.
      repeat split.
      rewrite <- N.leb_le.
      exact H2.
    + inversion Hres.
      repeat split.
      rewrite N.leb_nle in H2.
      lia.
  - unfold resource_sum_f. reflexivity.
Qed.

Definition res_sum_fold (capacity : N) (l : list (string * N)) acc :=
    fold_left (resource_sum_f capacity) l acc
  .

Lemma n_sum_add :
  forall l n,
  n_sum_rec l n = n_sum l + n.
Proof.
  intros l.
  induction l as [| n l].
  - simpl. reflexivity.
  - intros n'. simpl. unfold n_sum. simpl.
    specialize (IHl (n' + n)) as Hnusage.
    specialize (IHl n) as Husage.
    rewrite Hnusage.
    rewrite Husage.
    lia.
Qed.

Lemma res_sum_fold_correct :
  forall c l summed sum_result b (acc : sum_acc),
    match acc with
    | (acc_summed, acc_n, acc_b) =>
    (res_sum_fold c l acc = (summed, sum_result, b)) -> 
      ((acc_b = false -> b = false)
        /\
      (xn_sum acc_summed = acc_n -> xn_sum summed = sum_result )
        /\
      (forall a', In a' summed -> ((In a' summed \/ In a' acc_summed) /\ ((count_occ xn_eq_dec summed a' <= count_occ xn_eq_dec l a' + count_occ xn_eq_dec acc_summed a')%nat))) 
        /\
      if b 
        then 
          xn_sum l + acc_n = sum_result
            /\
          (acc_n <= c -> sum_result <= c)
        else
          if acc_b 
            then sum_result > c
            else acc_n > c -> sum_result > c
          )
      end.
Proof.
  intros c l summed sum_result b.
  induction l.
  - intros acc. destruct acc as [[acc_summed acc_n] acc_b]. intros Hres.
    simpl in *. inversion Hres.
    repeat split.
    + intros H. exact H.
    + intros H. exact H.
    + right. exact H.
    + reflexivity. 
    + destruct b.
      * split. { reflexivity. } { intros H. exact H. }
      * intros Hsum. exact Hsum.
  - intros acc. 
    specialize (resource_sum_f_correct c a acc) as Hresource_sum.
    destruct acc as [[acc_summed acc_n] acc_b] eqn:Hacc.
    rewrite <- Hacc in *.
    simpl in *.
    intros Hres.
    specialize (IHl (resource_sum_f c acc a)).
    destruct (resource_sum_f c acc a) as [[fl fs] fb] eqn:Hf.
    specialize (IHl Hres).
    repeat split.
    + intros Haccb.
      subst acc_b.
      inversion Hresource_sum.
      subst fb. subst fs. subst fl.
      destruct IHl as [IHfalse _].
      apply IHfalse.
      reflexivity.
    + destruct IHl as [_ [IHl _]].
      destruct acc_b.
      * destruct fb.
        { 
          intros Haccusage.
          destruct Hresource_sum as [Hfl [Hfs Hfslec]].
          subst fl. subst fs.
          apply IHl. unfold xn_sum in *; unfold n_sum.
          simpl. rewrite n_sum_add. rewrite Haccusage.
          reflexivity.
        }
        {
          intros Haccusage.
          destruct Hresource_sum as [Hfl [Hfs Hfslec]].
          subst fl. subst fs.
          apply IHl. unfold xn_sum in *; unfold n_sum.
          simpl. rewrite n_sum_add. rewrite Haccusage.
          reflexivity.
        }
      * inversion Hresource_sum.
        subst fl. subst fs. subst fb.
        exact IHl.
    + destruct IHl as [_ [_ [IHinl _]]].
      specialize (IHinl a' H).
      destruct IHinl as [IHin IHcount].
      destruct IHin as [IHin | IHinfl].
      { left. exact H. }
      { left. exact H. }
    + destruct IHl as [_ [_ [IHinl _]]].
      specialize (IHinl a' H).
      destruct IHinl as [IHinfl IHcount].
      destruct acc_b; destruct fb; inversion Hresource_sum.
      * destruct Hresource_sum as [Hfl [Hfs Hfslec]].
        subst fl. subst fs. simpl in IHinfl.
        simpl in *.
        destruct (xn_eq_dec a a').
        { subst a'. lia. }
        { apply IHcount. }
      * destruct Hresource_sum as [Hfl [Hfs Hfslec]].
        subst fl. subst fs. simpl in IHinfl.
        simpl in *.
        destruct (xn_eq_dec a a').
        { subst a'. lia. }
        { apply IHcount. }
      * subst fl. subst fs.
        destruct (xn_eq_dec a a').
        { subst a'. lia. }
        { apply IHcount. }
    + unfold xn_sum in *.
      simpl in *.
      destruct IHl as [Hbfalse [_ [_ IHsums]]].
      destruct acc_b eqn:Hacc_b.
      * destruct b.
        { 
          destruct IHsums as [IHsum IHle].
          destruct fb.
          - destruct Hresource_sum as [Hfl [Hfs Hfslec]].
            subst fl. subst fs.
            split.
            + rewrite <- IHsum.
              unfold n_sum. simpl.
              repeat rewrite n_sum_add.
              lia.
            + intros Haccle. apply IHle.
              exact Hfslec.
          - assert (false = false) as Hfalse by reflexivity.
            apply Hbfalse in Hfalse.
            discriminate Hfalse.
        }
        {
          destruct fb.
          - intros. exact IHsums. 
          - destruct Hresource_sum as [Hfl [Hfs Hfslec]].
            subst fl. subst fs.
            apply IHsums.
            exact Hfslec.
        } 
      * inversion Hresource_sum.
        subst fl. subst fs. subst fb. clear Hresource_sum.
        destruct b.
        {
          assert (false = false) as Hfalse by reflexivity.
          apply Hbfalse in Hfalse.
          discriminate Hfalse.
        }
        {
         exact IHsums. 
        }
Qed.

Lemma n_sum_gt :
  forall l i n, In n l -> n_sum_rec l i >= n.
Proof.
  intros l i a Hin.
  induction l as [| a'].
  - destruct Hin.
  - simpl.
    destruct Hin.
    + subst a'. rewrite n_sum_add. lia.
    + apply IHl in H.
      rewrite n_sum_add in *. lia.
Qed.

Lemma xn_sum_remove_once :
  forall l xn, In xn l -> xn_sum (remove_once xn_eq_dec xn l)  = xn_sum l - (snd xn).
Proof.
  induction l.
  - intros a Hnil. destruct Hnil.
  - intros a' Hin.
    simpl.
    destruct (xn_eq_dec a' a).
    + subst a'.
      unfold xn_sum; unfold n_sum; simpl. repeat rewrite n_sum_add. lia.
    + simpl. 
      assert (In a' l).
      {
       simpl in Hin. destruct Hin.
       - symmetry in H. contradiction.
       - exact H.
      }
      assert (In a' l) as Hainl by assumption.
      apply IHl in H. unfold xn_sum in *; unfold n_sum in *; simpl in *. repeat rewrite n_sum_add in *. 
      assert (n_sum (map snd (remove_once xn_eq_dec a' l)) = n_sum (map snd l) - snd a') as Husage_remove.
      { lia. }
      rewrite Husage_remove.
      specialize (n_sum_gt (map snd l) N0 (snd a')) as Hgt.
      assert (In (snd a') (map snd l)) as Hinlsnd.
      {
        rewrite in_map_iff. exists a'.
        split; try assumption.
        reflexivity.
      }
      apply Hgt in Hinlsnd.
      clear Husage_remove; clear H; clear Hgt; clear n; clear IHl; clear Hin; clear Hainl.
      rewrite n_sum_add in Hinlsnd.
      lia.
Qed.

Lemma xn_sum_sub_list :
  forall l1 l2, sub_list xn_eq_dec l1 l2 -> xn_sum l1 <= xn_sum l2.
Proof.
  induction l1.
  - intros l2 Hsub. unfold xn_sum; unfold n_sum. simpl. lia. 
  - intros l2 Hsub.
    assert (count_occ xn_eq_dec l2 a > 0)%nat as Hcounta.
    {
      unfold sub_list in Hsub.
      specialize (Hsub a).
      assert (In a (a :: l1)) as Hcounta.
      { simpl; left; reflexivity. }
      apply Hsub in Hcounta; clear Hsub.
      simpl in *.
      destruct (xn_eq_dec a a).
      2: contradiction.
      clear IHl1; clear e.
      lia.
    }
    assert (sub_list xn_eq_dec l1 (remove_once xn_eq_dec a l2)).
    {
      clear IHl1.
      unfold sub_list in *.
      intros a' Hin.
      assert (In a' (a :: l1)).
      { simpl. right. exact Hin. }
      apply Hsub in H; clear Hsub.
      simpl in *.
      destruct (xn_eq_dec a a').
      - subst a'. 
        rewrite <- remove_once_one_less_count.
        apply S_lt.
        rewrite S_pred_gt_0.
        + exact H.
        + exact Hcounta.
      - rewrite <- remove_once_one_same_if_neq with (a := a).
        + exact H.
        + assumption.
    }
    apply IHl1 in H; clear IHl1.
    assert (In a l2) as Hainl2.
    { rewrite count_occ_In. exact Hcounta. }
    rewrite xn_sum_remove_once in H; try assumption.
    assert (In (snd a) (map snd l2)) as Hinl2snd.
    {
      rewrite in_map_iff. exists a.
      split; try assumption.
      reflexivity.
    } 
    specialize (n_sum_gt (map snd l2) N0 (snd a) Hinl2snd) as Husagegt.
    unfold xn_sum in *; unfold n_sum in *.
    simpl. repeat rewrite n_sum_add in *.
    clear Hsub; clear Hcounta; clear Hainl2.
    lia.
Qed.

Lemma xn_sum_sub_list_gtn :
  forall l1 l2 n, sub_list xn_eq_dec l1 l2 -> xn_sum l1 > n -> xn_sum l2 > n.
Proof.
  intros l1 l2 n.
  intros Hsub Hl1n.
  specialize (xn_sum_sub_list l1 l2 Hsub) as H.
  lia.
Qed.

Lemma xn_sum_sub_list_gen :
  forall l1 l2 n, sub_list xn_eq_dec l1 l2 -> xn_sum l1 >= n -> xn_sum l2 >= n.
Proof.
  intros l1 l2 n.
  intros Hsub Hl1n.
  specialize (xn_sum_sub_list l1 l2 Hsub) as H.
  lia.
Qed.

Lemma xn_sum_capacity_not_in :
  forall l1 l2 n x xn, 
    sub_list xn_eq_dec l1 l2
      ->
    xn_sum l2 <= n
      ->
    ~ (In (x, xn) l1)
      ->
    xn_sum l1 + xn > n
      ->
    ~ (In (x, xn) l2).
Proof.
  intros l1 l2 n x xn.
  intros Hsub Hsum Hnotin Hgt.
  destruct (in_dec xn_eq_dec (x, xn) l2) as [Hinl2 | Hninl2].
  - exfalso.
    assert (sub_list xn_eq_dec ((x, xn) :: l1) l2).
    {
      unfold sub_list.
      intros a.
      intros Hain.
      simpl.
      destruct Hain.
      - subst a.
        unfold sub_list in Hsub.
        destruct (xn_eq_dec (x, xn) (x, xn)) as [Heq | Hneq].
        + clear Heq. rewrite (count_occ_In xn_eq_dec) in Hinl2.
          rewrite (count_occ_not_In xn_eq_dec) in Hnotin.
          rewrite Hnotin.
          lia.
        + contradiction.
      - destruct (xn_eq_dec (x, xn) a) as [Heq | Hneq].
        + subst a. contradiction.
        + apply Hsub. exact H. 
    }
    apply xn_sum_sub_list_gtn with (n := n) in H.
    + contradiction.
    + clear Hsub; clear Hsum; clear Hnotin; clear Hinl2; clear H.
      unfold xn_sum in *.
      simpl in *.
      unfold n_sum in *.
      simpl in *.
      rewrite n_sum_add in *.
      lia.
  - exact Hninl2.
Qed.


Definition res_sum (capacity : N) (l : list (string * N)) :=
  res_sum_fold capacity l (nil, N0, true)
.

Lemma res_sum_correct :
  forall c l,
    match res_sum c l with
    | (summed, sum_result, b) =>
      xn_sum summed = sum_result
        /\
        (forall a', In a' summed -> (In a' summed /\ ((count_occ xn_eq_dec summed a' <= count_occ xn_eq_dec l a')%nat))) 
        /\
      if b
        then 
          sum_result <= c
            /\
          xn_sum l = sum_result
        else sum_result > c
    end.
Proof.
  intros c l.
  destruct (res_sum c l) as [[summed sum_result] b] eqn:Hres.
  specialize (res_sum_fold_correct c l summed sum_result b (nil, N0, true)) as H.
  unfold res_sum in Hres.
  simpl in H.
  specialize (H Hres).
  destruct H as [Hfalse [Hsumr [Hin Hsums]]].
  repeat split.
  - apply Hsumr.
    unfold xn_sum. simpl. reflexivity.
  - exact H.
  - specialize (Hin a' H).
    destruct Hin as [_ Hcount].
    lia.
  - destruct b.
    + destruct Hsums as [Hsum Hle].
      split.
      * apply Hle. lia.
      * rewrite <- Hsum.
        lia.
    + exact Hsums.
Qed.

End ResourceSum.