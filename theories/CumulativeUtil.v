Require Coq.NArith.NArith.
Require Coq.Strings.String.
Require Coq.Lists.List.
Require Checker.Utility.
Require Import Checker.Cumulative.
Require Lia.

Module XNSum.
  Import Bool.
  Import NArith.
  Import List.
  Import Lia.
  Import Utility.ListEx.
  Import Utility.NatEx.
  Import String.
  
  Open Scope N_scope.

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
        
        unfold xn_sum; unfold n_sum; simpl. repeat rewrite n_sum_add.  lia.
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
      (In (x, xn) l2)
        ->
      False.
  Proof.
    intros l1 l2 n x xn.
    intros Hsub Hsum Hnotin Hgt Hinl2.
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
  Qed.

  Lemma xn_sum_add_le :
    forall l1 l2 x xn, 
      sub_list xn_eq_dec l1 l2
        ->
      ~ (In (x, xn) l1)
        ->
      (In (x, xn) l2)
        ->
      xn_sum l1 + xn <= xn_sum l2.
  Proof.
    intros l1 l2 x xn.
    intros Hsub Hnin1 Hin2.
    destruct (xn_sum l1 + xn <=? xn_sum l2) eqn:H.
    { rewrite <- N.leb_le. assumption. }
    exfalso.
    eapply xn_sum_capacity_not_in.
    - exact Hsub.
    - instantiate (1 := xn_sum l2). reflexivity.
    - exact Hnin1.
    - rewrite <- not_true_iff_false in H.
      rewrite N.leb_le in H.
      lia.
    - exact Hin2.
  Qed.
  
End XNSum.

Module RunOfN.
  Import Bool.
  Import PeanoNat.
  Import List.
  Import Lia.
  (* Note: we don't care if it traverses the whole list when it finds a valid one, since that is only in the error path. In general it will have to traverse the whole list to ensure there is a conflict since we expect to validate many more inferences than we reject *)
  Fixpoint has_n_true_rec (n : nat) (current : nat) (l : list bool) : bool :=
    match l with
    | true :: l' => has_n_true_rec n (S current) l'
    | false :: l' => (n <=? current) || (has_n_true_rec n 0 l')
    | nil => n <=? current
    end
  .

  Fixpoint run_size (l : list bool) : nat :=
    match l with
    | nil => O
    | false :: l' => O
    | true :: l' => S (run_size l')
    end.

  Definition run_at (n : nat) (l : list bool) : nat :=
    run_size (skipn n l). 

  Lemma run_size_lt_n :
    forall l n current,
      has_n_true_rec n current l = false
        ->
      run_size l + current < n.
  Proof.
    induction l.
    - intros n current Hhasn.
      simpl in *.
      rewrite <- not_true_iff_false in Hhasn. rewrite Nat.leb_le in Hhasn.
      lia.
    - simpl. destruct a.
      + intros n current Hhasn.
        specialize (IHl n (S current)).
        apply IHl in Hhasn; clear IHl.
        lia.
      + intros n current Hhasn.
        rewrite orb_false_iff in Hhasn.
        destruct Hhasn as [Hncurrent Hhasn].
        rewrite <- not_true_iff_false in Hncurrent.
        rewrite Nat.leb_le in Hncurrent.
        clear IHl.
        lia.
  Qed.

  Lemma run_size_le_length : 
    forall l,
      run_size l <= length l.
  Proof.
    induction l.
    - simpl. reflexivity.
    - simpl. destruct a; lia.
  Qed.


  Fixpoint max_runs (l : list bool) : nat :=
    match l with
    | nil => O
    | _ :: l' => max (run_size l) (max_runs l')
    end
  .

  Lemma skip_lt_max_runs :
    forall l k,
      run_size (skipn k l) <= max_runs l.
  Proof.
    induction l; induction k.
    - rewrite skipn_nil. simpl. reflexivity.
    - rewrite skipn_nil. simpl. reflexivity.
    - specialize (IHl 0).
      rewrite skipn_O in *.
      simpl.
      destruct a.
      + lia.
      + lia.
    - rewrite skipn_cons.
      simpl.
      assert (run_size (skipn k l) <= max_runs l) by (apply IHl).
      destruct a.
      + lia.
      + lia.
  Qed. 

  Lemma max_runs_all :
    forall l n,
      max_runs l < n
        ->
      (forall k, run_at k l < n).
  Proof.
    intros l n Hmax.
    intros k.
    unfold run_at.
    specialize (skip_lt_max_runs l k) as H.
    lia.
  Qed.

  Lemma nth_false_run_lt :
    forall l n,
      n >= 1
        ->
      ((exists k,
        k < n /\ nth k l false = false)
        <->
      run_size l < n).
  Proof.
    induction l.
    - intros n Hn. split.
      + intros. simpl. lia.
      + intros Hnil. simpl in Hnil.
        exists 0.
        split.
        * exact Hnil.
        * simpl. reflexivity.
    - intros n. 
      split.
      + simpl. intros Hk.
        destruct Hk as [k [Hkn Hkfalse]].
        destruct a.
        * destruct k; try discriminate Hkfalse.
          clear H; assert (n >= 2) as Hn2 by lia.
          assert (pred n >= 1) as Hpn1 by lia.
          specialize (IHl (pred n) Hpn1).
          assert (exists k, k < pred n /\ nth k l false = false).
          {
          exists k.
          split.
          - lia.
          - exact Hkfalse. 
          }
          rewrite IHl in H.
          lia.
        * lia.
      + simpl. destruct a.
        * intros Hrun.
          clear H; assert (n >= 2) as Hn2 by lia.
          assert (pred n >= 1) as Hpn1 by lia.
          assert (run_size l < pred n) by lia.
          rewrite <- (IHl (pred n) Hpn1) in H; clear IHl.
          destruct H as [k [Hkn Hkfalse]].
          exists (S k).
          split.
          -- lia.
          -- exact Hkfalse.
        * intros Hlt0; clear Hlt0.
          exists 0.
          split.
          -- lia.
          -- reflexivity.
  Qed.

  Lemma max_runs_max_lin :
    forall l n start,
      has_n_true_rec n start l = false
        -> 
      max_runs l < n.
  Proof.
    induction l.
    - intros n start.
      intros Hhasn. simpl in *.
      rewrite <- not_true_iff_false in Hhasn.
      rewrite Nat.leb_le in Hhasn.
      lia.
    - simpl. destruct a.
      + intros n start Hhasn.
        assert (max_runs l < n).
        { apply IHl with (start := S start).
        exact Hhasn. }
        enough (S (run_size l) < n) as Hrun by lia.
        clear H; clear IHl.
        specialize (run_size_lt_n l n (S start)) as H.
        apply H in Hhasn; clear H.
        lia.
      + intros n start Hhasn.
        rewrite orb_false_iff in Hhasn.
        destruct Hhasn as [Hnstart Hhasn].
        assert (max_runs l < n).
        {
        apply IHl with (start := 0).
        exact Hhasn.
        }
        lia.
  Qed.

  Lemma has_n_true_rec_if_max_runs_lt :
    forall l n start,
      max_runs l < n - start
        ->
      has_n_true_rec n start l = false.
  Proof.
    induction l.
    - intros n start; simpl; rewrite <- not_true_iff_false.
      rewrite Nat.leb_le.
      lia.
    - simpl. destruct a.
      + intros n start.
        intros Hmax.
        assert (max_runs l < n - start) as Hmaxr by lia.
        assert (S (run_size l) < n - start) as Hrunsz by lia.
        clear Hmax.
        apply IHl in Hmaxr; clear IHl.
        generalize dependent n.
        generalize dependent start.
        (* Useful lemma? *)
        induction l.
        {
          simpl. intros start n.
          repeat rewrite <- not_true_iff_false.
          repeat rewrite Nat.leb_le.
          lia.  
        }
        {
          intros start n. simpl.
          destruct a.
          - intros H1 H2.
            apply IHl.
            + exact H1.
            + lia.
          - repeat rewrite orb_false_iff.
            intros [Hnstart Hntrue].
            intros Hnstart1.
            split.
            * clear IHl Hntrue. rewrite <- not_true_iff_false in *. rewrite Nat.leb_le in *.
              lia.
            * exact Hntrue.
        }
      + intros n start.
        rewrite orb_false_iff.
        rewrite <- not_true_iff_false at 1.
        rewrite Nat.leb_le.
        assert (~ n <= start <-> n > start) by lia; rewrite H; clear H.
        rewrite max_r; try lia.
        intros Hmaxr.
        split.
        * lia.
        * apply IHl.
          lia.
  Qed.

  Definition has_n_true (n : nat) (l : list bool) :=
    has_n_true_rec n 0 l.

  Lemma has_n_true_iff_max_runs :
    forall n l, has_n_true n l = false <-> max_runs l < n.
  Proof.
    intros n l.
    split.
    - apply max_runs_max_lin.
    - intros H.
      apply has_n_true_rec_if_max_runs_lt.
      lia.
  Qed.
  
  Lemma exists_run_then_n_true :
    forall n l,
      (exists k, run_at k l >= n)
        -> 
      has_n_true n l = true.
  Proof.
    intros n l Hhasn.
    destruct (has_n_true n l) eqn:Hhasntrue.
    { reflexivity. }
    exfalso.
    rewrite has_n_true_iff_max_runs in Hhasntrue.
    destruct Hhasn as [k Hrunat].
    enough (run_at k l < n) by lia; clear Hrunat.
    apply max_runs_all, Hhasntrue.
  Qed.

  Lemma has_n_true_all_runs :
    forall n l,
      has_n_true n l = false
        ->
      (forall k, run_at k l < n).
  Proof.
    intros n l Hhasn.
    intros k.
    apply max_runs_all.
    apply max_runs_max_lin with (start := 0).
    apply Hhasn.
  Qed.

  Lemma run_at_exists :
    forall l k n,
    k + n <= length l
      ->
    run_at k l < n
      ->
    exists i,
      k <= i < k + n
        /\
      nth i l true = false.
  Proof.
    intros l k n.
    intros Hlength.
    intros Hrun_at.
    assert (n >= 1) as Hn1 by lia.
    unfold run_at in Hrun_at.
    rewrite <- nth_false_run_lt in Hrun_at;
    try assumption.
    destruct Hrun_at as (i & Hiltn & Hinth).
    exists (k + i).
    split.
    - lia.
    - rewrite nth_skipn in Hinth.
      rewrite nth_indep with (d' := false).
      + assumption.
      + lia.
  Qed.

  Lemma run_at_nth :
    forall l k n,
      length l >= k + n
        ->
      (forall i,
        k <= i < k + n
          ->
        nth i l true = true)
        ->
      run_at k l >= n.
  Proof.
    induction l as [| b l IH].
    - intros k n.
      unfold run_at. rewrite skipn_nil. simpl.
      intros H0 _.
      lia.
    - intros k n. simpl.
      intros Hlen H.
      destruct k.
      + destruct b.
        * destruct n.
          { lia. }
          assert (forall i, 0 <= i < n -> nth i l true = true) as Hnth.
          {
            intros i. specialize (H (S i)).
            simpl in H.
            intros Hi.
            apply H.
            lia.
          }
          clear H.
          specialize (IH 0 n).
          assert (length l >= 0 + n) as Hlen_n by lia.
          specialize (IH Hlen_n); clear Hlen_n.
          specialize (IH Hnth).
          clear Hnth.
          unfold run_at in *. rewrite skipn_O in *.
          simpl. lia.
        * unfold run_at.
          rewrite skipn_O. simpl.
          specialize (H 0).
          destruct n; lia.
      + unfold run_at. rewrite skipn_cons.
        apply IH.
        * lia.
        * intros i.
          intros Hi.
          specialize (H (S i)); simpl in H.
          apply H.
          lia.
  Qed. 
End RunOfN.
