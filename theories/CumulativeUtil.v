Require Coq.NArith.NArith.
Require Coq.Strings.String.
Require Coq.Lists.List.
Require Checker.Utility.
Require Coq.Sorting.Permutation.
Require Coq.Classes.Morphisms.
Require Checker.Spec.
Require Lia.

Module BuildCumul.
  Import Spec.ConstraintDefinitions.
  Import NArith.
  Import List.
  Import Lia.
  Import Morphisms.
  Open Scope N_scope.

  Definition activities_pos_duration (activities : list Activity) := filter (fun act => 1 <=? act.(activity_duration)) activities.

  Lemma activities_pos_duration_correct :
    forall activities,
      Forall (fun act => act.(activity_duration) >= 1) (activities_pos_duration activities).
  Proof.
    intros activities.
    rewrite Forall_forall; intros act.
    unfold activities_pos_duration.
    rewrite filter_In.
    intros [_ Hpos].
    rewrite N.leb_le in Hpos.
    lia.
  Qed.

  Definition build_cumulative (activities : list Activity) (cap : N) : CumulativeConstraint :=
    {|
      capacity := cap ;
      activities := activities_pos_duration activities;
      valid_durations := activities_pos_duration_correct activities;
    |}.
End BuildCumul.

Module NSum.
  Import NArith.
  Import List.
  Import Lia.
  Import Permutation.
  Import Morphisms.
  Open Scope N_scope.
  
  Fixpoint n_sum_rec (l : list N) (current : N) : N :=
    match l with
    | nil => current
    | n :: l' => n_sum_rec l' (current + n)
    end.

  Definition n_sum (l : list N) : N :=
    n_sum_rec l N0.

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

  Lemma n_sum_cons :
    forall l n,
      n_sum (n :: l) = n + n_sum l.
  Proof.
    intros l n.
    unfold n_sum. simpl. setoid_rewrite n_sum_add.
    lia.
  Qed.

  Lemma n_sum_app :
    forall l1 l2,
      n_sum (l1 ++ l2) = n_sum l1 + n_sum l2.
  Proof.
    induction l1.
    - intros l2. simpl. reflexivity.
    - intros l2.
      simpl. repeat rewrite n_sum_cons.
      rewrite IHl1. lia.
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

  Lemma n_fold_is_n_sum :
    forall ns i,
    fold_left N.add ns i = n_sum ns + i.
  Proof.
    induction ns.
    - reflexivity.
    - intros i. simpl. rewrite IHns.
      rewrite n_sum_cons.
      lia.
  Qed.

  Lemma n_sum_perm :
    forall l l',
      Permutation l l'
        ->
      n_sum l = n_sum l'.
  Proof.
    induction l.
    - intros l. intros Hperm.
      apply Permutation_nil in Hperm; subst l.
      reflexivity.
    - intros l'. intros Hperm.
      assert (In a l').
      { apply Permutation_in with (l := (a :: l)).
        - exact Hperm.
        - left. reflexivity. }
      apply in_split in H.
      destruct H as (l1 & l2 & Hl1l2); subst l'.
      apply Permutation_cons_app_inv in Hperm.
      apply IHl in Hperm.
      rewrite n_sum_cons.
      rewrite Hperm.
      setoid_rewrite n_sum_app.
      rewrite n_sum_cons.
      lia.
  Qed.

  (** When we have somewhere `n_sum l` and also `H : Permutation l l'`, this allows us to convert `n_sum l` into `n_sum l'` using `rewrite H`. *)
  Instance n_sum_Proper : Proper (@Permutation N ==> eq) n_sum.
  Proof.
    unfold Proper, respectful.
    intros l l' Hperm.
    apply n_sum_perm.
    exact Hperm.
  Qed.
End NSum.

Module XNSum.
  Import Bool.
  Import NArith.
  Import List.
  Import Lia.
  Import Utility.ListEx.
  Import Utility.SubList.
  Import String.
  Import Permutation.
  Import NSum.
  
  Open Scope N_scope.

  (** This was originally used by the cumulative checker when it still relied on the variable identifier to match a BoundedActivity with an Activity. It can be removed if not used anywhere by 2026. *)
  
  Definition xn_sum (l : list (string * N)) : N :=
    n_sum (map snd l).

  Lemma xn_eq_dec :
    forall x y : (string * N), {x = y}+{x <> y}.
  Proof.
    intros x y. decide equality.
    - apply N.eq_dec.
    - apply String.string_dec.
  Qed.

  Lemma xn_sum_perm :
    forall l l',
      Permutation l l' -> xn_sum l = xn_sum l'.
  Proof.
    induction l as [|xn l].
    - intros l' H. apply Permutation_nil in H.
      subst l'. reflexivity.
    - intros l' Hperm.
      assert (In xn l') as Hin'.
      { apply Permutation_in with (l := (xn :: l)).
        - exact Hperm.
        - left. reflexivity. }
      apply in_split in Hin'.
      destruct Hin' as (l1 & l2 & Hl1l2); subst l'.
      apply Permutation_cons_app_inv in Hperm.
      apply IHl in Hperm; clear IHl.
      revert Hperm.
      unfold xn_sum.
      repeat rewrite map_app.
      repeat rewrite n_sum_app.
      unfold n_sum. simpl. setoid_rewrite n_sum_add.
      lia.
  Qed.

  Lemma xn_sum_sub_list :
    forall l1 l2, sublist l1 l2 -> xn_sum l1 <= xn_sum l2.
  Proof.
    intros l1 l2.
    unfold sublist.
    intros (diff & Hperm).
    apply xn_sum_perm in Hperm.
    rewrite <- Hperm.
    unfold xn_sum. rewrite map_app. rewrite n_sum_app.
    lia.
  Qed.

  Lemma xn_sum_add_le :
    forall l1 l2 x xn, 
      sublist l1 l2
        ->
      ~ (In (x, xn) l1)
        ->
      (In (x, xn) l2)
        ->
      xn_sum l1 + xn <= xn_sum l2.
  Proof.
    intros l1 l2 x xn.
    unfold sublist.
    intros (diff & Hperm).
    apply xn_sum_perm in Hperm as Hl2sum.
    rewrite <- Hl2sum.
    unfold xn_sum.
    rewrite map_app.
    rewrite n_sum_app.
    intros Hnin1 Hin2.
    enough (xn <= n_sum (map snd diff)) by lia.
    enough (In (x, xn) diff).
    - apply in_split in H.
      destruct H as (diff1 & diff2 & Hdiff).
      clear -Hdiff.
      subst diff.
      rewrite map_app. simpl.
      rewrite n_sum_app.
      unfold n_sum. simpl.
      setoid_rewrite n_sum_add.
      lia.
    - symmetry in Hperm.
      apply Permutation_in with (x := (x, xn)) in Hperm.
      + apply in_app_or in Hperm.
        destruct Hperm as [Hinl1 | Hindiff]; try contradiction.
        exact Hindiff.
      + exact Hin2.
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
(* 

  Fixpoint has_interval_of_n (n : N) (current : N) (l : list (bool * N)) :=
    match l with
    | (true, _) =>  *)
End RunOfN.
