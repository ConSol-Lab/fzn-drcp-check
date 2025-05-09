
Require Import Coq.Logic.FinFun.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import String.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Arith.PeanoNat.
Require Import Bool.

Require Import Checker.Nogood.
Require Import Checker.Cumulative.
Require Checker.CumulativeUtil.
Import CumulativeUtil.ResourceSum.
Require Import Checker.Utility.
Import ListEx.
Import Sets.
Require Import Lia.
Require Checker.Utility.
Require Import Checker.Deduction.
Require Import Checker.Domain.
Require Import Checker.DomainVar.
Require Import Checker.DomainVarOld.
Require Import Checker.Atomic.
Require Import Checker.Variable.

Import Utility.Maps.
Open Scope N_scope.

Theorem res_sum_semantics :
  forall c l,
    match res_sum c l with
    | (_, sum_result, true) =>
      xn_sum l = sum_result  
        /\     
        xn_sum l <= c
    | (summed, sum_result, false) =>
    xn_sum summed = sum_result
        /\
        xn_sum summed > c
        /\
      sub_list xn_eq_dec summed l
        /\
        xn_sum l > c
    end.
Proof.
  intros c l.
  specialize (res_sum_correct c l) as H.
  destruct (res_sum c l) as [[summed sum_result] b].
  destruct b.
  - destruct H as [Hsum_result [Hin [Hle Husage]]].
    split.
    + exact Husage.
    + rewrite Husage. exact Hle.
  - destruct H as [Hsum_result [Hin Hgt]].
    assert (sub_list xn_eq_dec summed l) as Hsub.
    {
      unfold sub_list.
      intros a Hinsummed.
      apply Hin. exact Hinsummed.
    }
    repeat split.
    + rewrite Hsum_result. reflexivity.
    + rewrite Hsum_result. exact Hgt.
    + exact Hsub. 
    + specialize (xn_sum_sub_list summed l Hsub) as Husagelt.
      repeat rewrite usage_sum_add in *.
      rewrite <- Hsum_result in Hgt.
      lia.
Qed.

Open Scope N_scope.
Lemma exceeds_at_t_dec_false :
  forall (c : CumulativeConstraint) (a : string -> Z),
  (exists t, 
    (c.(horizon_start) <= t <= c.(horizon_end))%Z
      /\
    usage_sum (activities_at_t (activity_list c a) t) > c.(capacity))
    ->
  cumulative_decide c a = false.
Proof.
  intros c a Hex.
  destruct Hex as [t [Hhorizon Husage]].
  destruct (cumulative_decide c a) eqn:Hdecide; try reflexivity.
  exfalso. unfold cumulative_decide in Hdecide.
  rewrite forallb_forall in Hdecide.
  specialize (Hdecide t).
  specialize c.(horizon_consistent) as Hrange.
  apply (ZRange.build_range_correct (horizon_start c) (horizon_end c)) in Hrange.
  unfold ZRange.is_range in Hrange.
  destruct Hrange as [_ [Ht _]].
  rewrite Ht in Hhorizon.
  apply Hdecide in Hhorizon as Husagelt.
  clear Hhorizon; clear Hdecide.
  rewrite N.leb_le in Husagelt.
  contradiction.
Qed.

Open Scope Z_scope.

Definition mandatory_active (lb : Z) (ub : Z) (t : Z) (p_time : N) :=
  (ub <=? t) && (t <? (lb + (Z.of_N p_time))).

Definition constraint_to_param_map (c : CumulativeConstraint) : string -> (N * N) :=
  let params := map (fun elt =>
    match elt with
    | mkActDef x p u => (x, (p, u))
    end) c.(activities) in
  param_map params (N0, N0).

Definition constraint_to_vars (c : CumulativeConstraint) : list string :=
  map def_x c.(activities).

Definition constraint_to_vs (c : CumulativeConstraint) : sstr.t :=
  sstr.build (constraint_to_vars c).

Definition domain_to_bound (param_map : string -> (N * N)) (dom : string * Domain) :=
  match dom with
  | (x, dom) =>
    match dom.(d_lb) with
    | Some lb =>
      match dom.(d_ub) with
      | Some ub =>
        let size := Z.to_N (ub - lb) in
          Some (x, (lb, size), (param_map x))
      | _ => None
      end
    | _ => None
    end
  end.

Definition domains_to_bounds (doms : list (string * Domain)) (param_map : string -> (N * N)) : list (string * zn_interval * (N * N)) :=
  flat_map_option (domain_to_bound param_map) doms.

Definition inferred_cumulative_bounds (c : CumulativeConstraint) (fact : Deduction.Inference) :=
  let vs := constraint_to_vs c in
  match infer_domains (Some vs) fact with
  | None => (nil, None)
  | Some (domains, prop_var) =>
    (domains_to_bounds (smap.bindings domains) (constraint_to_param_map c), prop_var)
  end.

Definition interval_to_bounds (i : zn_interval) : (Z * Z)%type :=
  let (lb, size) := i in
    (lb, lb + (Z.of_N size)).

Definition activity_bounds_is_active (t : Z) (activity : string * zn_interval * (N * N)) : option (string * N) :=
  match activity with
  | (x, i, (p_time, usage)) =>
    match interval_to_bounds i with
    | (lb, ub) =>
      if mandatory_active lb ub t p_time
        then Some (x, usage)
        else None
    end
  end.

Definition activities_bounds_active_at (t : Z) (activities : list (string * zn_interval * (N * N))) :=
  flat_map_option (activity_bounds_is_active t) activities.

Open Scope N_scope.

Definition resource_profile_t (capacity : N) (activities : list (string * zn_interval * (N * N))) (t : Z) : (Z * N) :=
  match res_sum capacity (activities_bounds_active_at t activities) with
  (_, usage, _) => (t, usage)
  end
.

Inductive profile_result :=
| profile_usages (u : list (Z * N))
| profile_conflict (t : Z).

Fixpoint resource_profile (capacity : N) (activities : list (string * zn_interval * (N * N))) (times : list Z) : profile_result := 
  match times with
  | nil => profile_usages nil
  | t :: tl' => 
    match res_sum capacity (activities_bounds_active_at t activities) with
    | (_, usage, true) => 
      match resource_profile capacity activities tl' with
      | profile_usages u => profile_usages ((t, usage) :: u)
      | profile_conflict c => profile_conflict c
      end
    | (_, _, false) => profile_conflict t
    end
  end.
  

Definition is_as_range {A} (f : A -> Z) (s : Z) (e : Z) (l : list A) :=
  ZRange.is_range s e (map f l).


Open Scope Z_scope.
Lemma resource_profile_as_range :
  forall times c activities s e,
    ZRange.is_range s e times
      ->
    match resource_profile c activities times with
    | profile_usages u => is_as_range fst s e u
    | _ => True
    end
    .
Proof.
  intros times c act.
  induction times.
  - intros. 
    simpl.
    unfold ZRange.is_range in H.
    destruct H as [Hse [Hn _]].
    assert (s <= s <= e)%Z as Hsse by lia.
    rewrite Hn in Hsse. destruct Hsse.
  - intros s e.
    intros Htimes_range.
    destruct (resource_profile c act times) eqn:Hprofile_base.
    + 
      unfold is_as_range. simpl.
      destruct (res_sum c
      (activities_bounds_active_at a
      act)) as [[usages usage] valid].
      destruct valid.
      2: { reflexivity. }
      rewrite Hprofile_base.
      simpl.
      destruct times as [| a' times].
      { simpl in Hprofile_base. inversion Hprofile_base as [Hu]; subst u. simpl. exact Htimes_range. }
      simpl in Hprofile_base.
      destruct (res_sum c
      (activities_bounds_active_at a'
      act)) as [[usages' usage'] valid'].
      destruct valid'.
      2: { discriminate Hprofile_base. }
      destruct (resource_profile c act times) as [u' |].
      2: { discriminate Hprofile_base. }
      inversion Hprofile_base; subst u; clear Hprofile_base.
      simpl.
      apply ZRange.is_range_endpoints in Htimes_range as Haa'.
      destruct Haa' as [Ha Ha'].
      subst a; subst a'.
      apply ZRange.is_range_implies_pred_range in Htimes_range as Hpred_range.  
      specialize (IHtimes s (e - 1) Hpred_range).
      destruct IHtimes as [Hse [Hn Hsucc]].
      split; [|split].
      * lia.
      * intros n. split.
        {
          intros Hsne.
          destruct (n =? e) eqn:Hne.
          { rewrite Z.eqb_eq in Hne; subst n.
            simpl. left. reflexivity. }
          rewrite Z.eqb_neq in Hne.
          assert (s <= n <= e - 1) as Hsne1 by lia.
          rewrite Hn in Hsne1.
          right. exact Hsne1.
        }
        {
          intros Hin. 
          destruct Hin as [He | Hin]. 
          - subst n. lia.
          - rewrite <- Hn in Hin.
            lia.
        }
      * unfold ZRange.succ_seq.
        apply Sorted_cons.
        -- exact Hsucc.
        -- apply HdRel_cons.
          unfold ZRange.is_succ.
          lia.
    + simpl. rewrite Hprofile_base.
      destruct (res_sum c
      (activities_bounds_active_at a
      act)).
      destruct p. destruct b; reflexivity.
Qed.


Open Scope N_scope.
Lemma resource_profile_correct :
  forall capacity activities times,
    match resource_profile capacity activities times with
    | profile_usages u =>
      forall t usage, In (t, usage) u ->
        In t times /\
        xn_sum (activities_bounds_active_at t activities) >= usage
    | profile_conflict t_false =>
      In t_false times /\
      xn_sum (activities_bounds_active_at t_false activities) > capacity
    end.
Proof.
  induction times as [| t times IHtimes].
  - simpl. intros t Hfalse. contradiction.
  - specialize (res_sum_semantics capacity (activities_bounds_active_at t activities)) as Hres_sum.
    destruct (resource_profile capacity activities times) as [| t_false] eqn:Hprofile_base.
    + simpl.
      destruct (res_sum capacity
      (activities_bounds_active_at t
      activities)) as [[summed usage_base] valid] eqn:Hresult.
      destruct valid.
      * rewrite Hprofile_base.
        intros t' usage.
        intros Hin.
        destruct Hin.
        { 
          inversion H; subst t'; subst usage_base.
          split.
          - left. reflexivity.
          - lia.
        }
        {
          apply IHtimes in H.
          destruct H as [Hin Hsum].
          split.
          - right. exact Hin.
          - exact Hsum. 
        }
      * split.
        -- left. reflexivity.
        -- apply Hres_sum.
    + simpl.
      destruct (res_sum capacity
      (activities_bounds_active_at t
      activities)) eqn:Hresult.
      destruct p; destruct b.
      * rewrite Hprofile_base.
        split.
        -- right. apply IHtimes.
        -- apply IHtimes.
      * split.
        -- left. reflexivity.
        -- apply Hres_sum.
Qed.

Open Scope Z_scope.

Definition c_var_with_x (x : string) (v : Var) :=
  (x =? var_name v)%string.

Definition make_activity (a : string * zn_interval * (N * N)) (vs : list string) (sol : string -> Z) :=
  match a with
  | (x, (lb, size), (p, u)) =>
      mkAct x (sol x) p u
  end.

Definition in_horizon (a : Activity) (c : CumulativeConstraint) :=
  c.(horizon_start) <= a.(start) /\ a.(start) + Z.of_N a.(p_time) <= c.(horizon_end).

Definition task_in_constraint (a : string * zn_interval * (N * N)) (c : CumulativeConstraint) (sol : string -> Z) :=
  let act := (make_activity a (constraint_to_vars c) sol) in
    In act (activity_list c sol)
      /\
    match a with
    | (x, (lb, size), (p, u)) =>
      lb <= act.(start) <= lb + Z.of_N size
    end.

Definition horizon_length (c : CumulativeConstraint) :=
  Z.to_N (c.(horizon_end) - c.(horizon_start)).

Lemma task_valid_processing :
  forall x lb size p u c sol,
    task_in_constraint (x, (lb, size), (p, u)) c sol
      ->
    (p >= 1)%N.
Proof.
  intros x lb size p u c sol.
  intros Htask.
  destruct Htask as [Hin _].
  unfold activity_list in Hin.
  unfold activity_list_inner in Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as (a & Hact & Hinvs).
  specialize c.(valid_p_times) as Hprocess.
  specialize (Hprocess a Hinvs).
  destruct a as [ax ap au]; simpl in Hact.
  inversion Hact; subst; clear Hact.
  apply Hprocess.
Qed.

Open Scope N_scope.

Definition bound_name {U} (bound : string * zn_interval * U) :=
  match bound with
  | (x, _, _) => x
  end.

Definition unique_bounds {U} (bounds : list (string * zn_interval * U)) :=
  NoDup (map bound_name bounds).

Lemma a_u_dec (U : Type) (u_dec : forall x y : U, {x = y}+{x <> y}) :
  forall x y : string * zn_interval * U, {x = y}+{x <> y}.
Proof.
  repeat decide equality.
Qed.

Definition valid_bounds (bounds : list (string * zn_interval * (N * N))) (c : CumulativeConstraint) (sol : string -> Z) :=
  forall a, In a bounds -> task_in_constraint a c sol.

Lemma eq_dec_bounds :
  forall x y : string * zn_interval * (N * N), {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Qed.

Lemma activity_bounds_nodup :
forall t bounds,
  unique_bounds bounds
    ->
  NoDup (activities_bounds_active_at t bounds).
Proof.
  intros t bounds Hunique. 
  unfold activities_bounds_active_at. 
  rewrite flat_map_option_as_filter_map with (d := (""%string, N0)).
  apply NoDup_map_inv with (f := fst).
  remember
    (filter
      (filter_f_option
      (activity_bounds_is_active
      t)) bounds) as l.
  apply nodup_key with (a_k := bound_name).
  - unfold unique_bounds in Hunique.
    apply nodup_sublist with (l2 := (map bound_name bounds)) (eq_dec := String.string_dec).
    + exact Hunique.
    + eapply sub_list_map.
      subst l.
      apply filter_sublist.
      Unshelve.
      repeat decide equality. 
  - intros a Hin. subst l. rewrite filter_In in Hin.
    destruct Hin as (Hinbounds & Hfilteropt).
    unfold option_map_default.
    unfold filter_f_option in Hfilteropt.
    destruct (activity_bounds_is_active t a) as [bnd |] eqn:Hbnd.
    + unfold activity_bounds_is_active in Hbnd.
      destruct a as [[x i] [p u]].
      destruct (interval_to_bounds i) as [lb ub].
      destruct (mandatory_active lb ub t p).
      * destruct bnd as [x' n].
        inversion Hbnd; subst x'. simpl. reflexivity.
      * discriminate Hbnd.
    + discriminate Hfilteropt.
Qed.

Lemma valid_bounds_mandatory_sublist :
  forall constr sol bounds t,
  valid_bounds bounds constr sol
    ->
  unique_bounds bounds
    ->
  sub_list xn_eq_dec (activities_bounds_active_at t bounds) ((map act_to_xn (activities_at_t (activity_list constr sol) t))).
Proof.
  intros constr sol bounds t.
  intros Hvalid Hunique.
  apply sub_list_if_in_nodup.
  - intros a Hin.
    rewrite in_map_iff.
    pose proof Hin as Hin2.
    unfold activities_bounds_active_at in Hin.
    rewrite in_flat_map_option in Hin.
    destruct Hin as [a' [Hinbounds Hinres]].
    destruct a' as [[x [lb size]] [p u]] eqn:Ha'.
    unfold activity_bounds_is_active in Hinres.
    destruct (interval_to_bounds (lb, size)) as [lb' ub] eqn:Hibounds. unfold interval_to_bounds in Hibounds; inversion Hibounds; subst lb'; symmetry in H1; clear Hibounds.
    destruct (mandatory_active lb ub t p) eqn:Hmand.
    2: discriminate Hinres.
    inversion Hinres; subst a; clear Hinres. 
    apply Hvalid in Hinbounds.
    unfold task_in_constraint in Hinbounds.
    rewrite <- Ha' in *.
    remember (make_activity a' (constraint_to_vars constr) sol) as act.
    destruct Hinbounds as [Hact Hstart].
    exists act.
    split.
    + rewrite Heqact. rewrite Ha'. unfold make_activity. unfold act_to_xn. simpl. reflexivity.
    + unfold mandatory_active in Hmand.
      unfold activities_at_t.
      rewrite filter_In. split.
      * exact Hact.
      * assert (p_time act = p) as Hp.
        {
         rewrite Heqact. rewrite Ha'. unfold make_activity.
         simpl. reflexivity. 
        }
        rewrite Hp.
        unfold is_active_at.
        rewrite andb_true_iff; rewrite andb_true_iff in Hmand.
        rewrite Z.leb_le in Hmand; rewrite Z.leb_le.
        rewrite Z.ltb_lt; rewrite Z.ltb_lt in Hmand.
        lia. 
  - apply activity_bounds_nodup.
    exact Hunique.
Qed.

Definition default_bound :=
  (""%string, (Z0, N0), (N0, N0)).

Open Scope nat_scope.

(* Note: we don't care if it traverses the whole list when it finds a valid one, since that is only in the error path. In general it will have to traverse the whole list to ensure there is a conflict since we expect to validate many more inferences than we reject *)
Fixpoint has_n_true_rec (n : nat) (current : nat) (l : list bool) : bool :=
  match l with
  | true :: l' => has_n_true_rec n (S current) l'
  | false :: l' => (n <=? current) || (has_n_true_rec n 0 l')
  | nil => n <=? current
  end
.

Open Scope nat_scope.
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

Open Scope nat_scope.

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

Definition has_n_true (n : nat) (l : list bool) :=
  has_n_true_rec n 0 l.

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

Open Scope Z_scope.

Lemma nth_error_exists {A} :
  forall l n,
    (n < length l)%nat
      ->
    exists (a : A), nth_error l n = Some a.
Proof.
  induction l.
  - intros n Hn. simpl in Hn. lia.
  - intros n Hlen.
    destruct (n =? 0)%nat eqn:Hn0.
    + rewrite Nat.eqb_eq in Hn0. subst n.
      exists a. simpl. reflexivity.
    + rewrite Nat.eqb_neq in Hn0.
      destruct n; try contradiction.
      specialize (IHl n).
      simpl in Hlen.
      assert (n < length l)%nat by lia.
      apply IHl in H.
      destruct H as [a' Hnth].
      exists a'.
      rewrite nth_error_S. simpl.
      exact Hnth.
Qed.

Lemma run_at_seq_fk_false {A} :
  forall l s e n i (fz : A -> Z) (fb : A -> bool),
    (n >= 1)%nat
      ->
    (n <= length l)%nat
      ->
    (i <= length l - n)%nat
      ->
    is_as_range fz s e l
      ->
    (run_at i (map fb l) < n)%nat
      ->
    (exists a,
      e - Z.of_nat i - Z.of_nat n + 1 <= fz a <= e - Z.of_nat i
        /\
      In a l
        /\
      fb a = false
    ).
Proof.
  intros l s e n i fz fb.
  intros Hn1 Hnlen Hi Hasrange Hrun.
  assert (n <= length (skipn i l))%nat.
  { 
    rewrite length_skipn.
    lia.
  }
  rewrite length_skipn in H.
  rewrite <- length_map with (f := fz) in H.
  rewrite ZRange.is_range_length with (s := s) (e := e) in H.
  2: apply Hasrange.
  rewrite <- (nth_false_run_lt (skipn i (map fb l)) n) in Hrun; try assumption.
  destruct Hrun as [k [Hkn Hkfalse]].
  assert ((i + k) < length l)%nat as Hnth_a by lia.
  apply nth_error_exists in Hnth_a.
  destruct Hnth_a as [a Hnth_a].
  apply map_nth_error with (f := fz) in Hnth_a as Hfza.
  exists a.
  apply ZRange.range_nth_error with (s := s) (e := e) in Hfza.
  2: assumption.
  split.
  - lia.
  - split.
    + apply nth_error_In in Hnth_a.
      exact Hnth_a.
    + rewrite nth_skipn in Hkfalse.
      assert (i + k < length (map fb l))%nat as Hfb.
      { rewrite length_map. lia. }
      apply nth_error_nth' with (d := false) in Hfb.
      rewrite Hkfalse in Hfb.
      apply map_nth_error with (f := fb) in Hnth_a.
      rewrite Hnth_a in Hfb.
      inversion Hfb.
      reflexivity.
Qed.

Open Scope Z_scope.
Definition active_list (start_time : Z) (p_time : N) (times : list Z) : list bool :=
  map (is_active_at start_time p_time) times.

Open Scope N_scope.

(* A good optimization would be to somehow not go over the entire constraint horizon and to only check between the lower and upper bounds. *)
Definition can_be_active_at_t (capacity : N) (activity : string * zn_interval * (N * N)) (profile_entry : (Z * N)) : bool :=
  match profile_entry with
  | (t, profile_usage) =>
  (* If it is mandatory active (not nil), we will have checked it already in the resource profile, so it's definitely fine *)
    match activity_bounds_is_active t activity with
    | None => 
      match activity with
      | (_, (lb, size), (p_time, usage)) =>
        (lb <=? t)%Z
          &&
        (t <? lb + Z.of_N size + Z.of_N p_time)%Z
          && 
        (profile_usage + usage <=? capacity)
      end
    | _ => true
    end
  end
.

Lemma can_be_active_at_t_false :
  forall t profile_usage c x lb size p u,
    can_be_active_at_t c (x, (lb, size), (p, u)) (t, profile_usage) = false
      ->
    (activity_bounds_is_active t (x, (lb, size), (p, u)) = None)
      /\
    ((profile_usage + u > c) \/ (t < lb \/ t >= lb + Z.of_N size + Z.of_N p)%Z).
Proof.
  intros t p_u c x lb size p u.
  intros Hfalse.
  unfold can_be_active_at_t in Hfalse.
  destruct (activity_bounds_is_active t (x, (lb, size), (p, u))).
  - discriminate Hfalse. 
  - split.
    + reflexivity.
    + repeat rewrite andb_false_iff in Hfalse.
      repeat rewrite <- not_true_iff_false in Hfalse.
      repeat rewrite Z.leb_le in Hfalse.
      rewrite N.leb_le in Hfalse.
      lia. 
Qed.

Open Scope Z_scope.

Definition make_active_list (capacity : N) (profile : list (Z * N)) (activity : string * zn_interval * (N * N)) : list bool :=
  map (can_be_active_at_t capacity activity) profile.

Definition cannot_schedule_activity_w_profile (capacity : N) (profile : list (Z * N)) (activity : string * zn_interval * (N * N)) : bool :=
  match activity with
  | (_, _, (duration, _)) =>
    negb (has_n_true (N.to_nat duration) (make_active_list capacity profile activity))
  end.

Definition cumulative_checker (inference : Deduction.Inference) (constraint : CumulativeConstraint) : bool :=
  let times := (ZRange.build_range constraint.(horizon_start) constraint.(horizon_end)) in
  match inferred_cumulative_bounds constraint inference with
  | (nil, _) => false
  | (bounds, prop_var) => 
    match resource_profile (constraint.(capacity)) bounds times with
    | profile_usages r_profile => 
      existsb (cannot_schedule_activity_w_profile (constraint.(capacity)) r_profile) bounds 
    | _ => true
    end
  end
.

Lemma neg_atomic : forall sol inference, satisfies_nogood inference sol = false -> inference_negated inference sol.
Proof.
  intros sol inference Hsat.
  unfold inference_negated. intros atomic.
  apply unsat_nogood.
  exact Hsat.
Qed.

Open Scope Z_scope.

Lemma cumulative_forall :
  forall sol c,
    Is_true (cumulative_decide c sol)
      ->
    forall t, 
      c.(horizon_start) <= t <= c.(horizon_end)
        ->
      (usage_sum (activities_at_t (activity_list c sol) t) <= c.(capacity))%N.
Proof.
  intros sol c.
  intros Htrue.
  intros t Ht.
  apply Is_true_eq_true in Htrue.
  unfold cumulative_decide in Htrue.
  rewrite forallb_forall in Htrue.
  assert (In t (ZRange.build_range (horizon_start c) (horizon_end c))).
  { apply ZRange.build_range_correct.
    - apply c.(horizon_consistent).
    - exact Ht. }
  apply Htrue in H; clear Htrue.
  rewrite <- N.leb_le.
  exact H.
Qed.

Definition t_in_horizon (constr : CumulativeConstraint) (t : Z) :=
  horizon_start constr <= t <= horizon_end constr.

Definition activity_active_at (act : Activity) (t : Z) :=
  (start act) <= t < (start act) + Z.of_N (p_time act).

Lemma exists_cannot_schedule :
  forall constr sol bounds ,
    cumulative_decide constr sol = true
      ->
    unique_bounds bounds
      ->
    valid_bounds bounds constr sol
      ->
    (exists (act : Activity) t_false,
      horizon_start constr <= t_false <=
      horizon_end constr
        /\
      In act (activity_list constr sol)
        /\
      (start act) <= t_false < (start act) + Z.of_N (p_time act)
        /\
      ~ In (act.(a_name), act.(usage)) (activities_bounds_active_at t_false bounds)
        /\
      (xn_sum (activities_bounds_active_at t_false bounds) + act.(usage) > constr.(capacity))%N)
      ->
    False.
Proof.
  intros constr sol bounds.
  intros Htrue Hunique Hvalid.
  intros H.
  destruct H as [act [t_false [Hhor [Hin [Ht [Hnot_man Hexceeds]]]]]].
  apply xn_sum_capacity_not_in with (x := act.(a_name)) (l2 := (map act_to_xn (activities_at_t (activity_list constr sol) t_false))) in Hexceeds.
  - apply Hexceeds.
  - apply valid_bounds_mandatory_sublist.
    + exact Hvalid.
    + exact Hunique.
  - apply cumulative_forall.
    + rewrite Htrue. reflexivity.
    + exact Hhor.
  - exact Hnot_man.
  - rewrite in_map_iff.
    exists act.
    split.
    + unfold act_to_xn. reflexivity.
    + unfold activities_at_t.
      rewrite filter_In.
      split.
      * exact Hin.
      * unfold is_active_at.
        lia.
Qed.

Definition is_horizon_range (constr : CumulativeConstraint) (times : list Z) :=
  ZRange.is_range constr.(horizon_start) constr.(horizon_end) times.

(* Idea: smart specialize... so you don't have to manually instantiate it *)

Lemma resource_profile_conflict :
  forall sol constr bounds times t_c,
    cumulative_decide constr sol = true
      ->
    valid_bounds bounds constr sol
      ->
    unique_bounds bounds
      ->
    is_horizon_range constr times
      ->
    resource_profile constr.(capacity) bounds times = profile_conflict t_c
      ->
    False.
Proof.
  intros sol constr bounds times t_c.
  intros Hsol Hvalid Hunique Hhorizon Hprofile. 
  enough (cumulative_decide constr sol = false) as Hconstr_false.
  { rewrite Hconstr_false in Hsol. discriminate Hsol. }
  apply exceeds_at_t_dec_false.
  exists t_c.
  specialize (resource_profile_correct (constr.(capacity)) bounds times) as Hcorrect.
  rewrite Hprofile in Hcorrect.
  split.
  + apply Hhorizon. apply Hcorrect.
  + apply xn_sum_sub_list_gtn with (l1 := activities_bounds_active_at t_c bounds).
    * apply valid_bounds_mandatory_sublist.
      -- exact Hvalid.
      -- exact Hunique.
    * apply Hcorrect.
Qed.

Lemma inferred_bounds_correct constr fact bounds prop_var:
  forall sol,
    bounds <> nil
      ->
    inferred_cumulative_bounds constr fact = (bounds, prop_var)
      ->
    (valid_bounds bounds constr sol
      ->
    False)
      ->
    inference_valid sol fact.
Proof.
  intros sol Hnnil Hinfer_bounds Hvalid.
  unfold inferred_cumulative_bounds in Hinfer_bounds.
  destruct infer_domains as [[doms prop_var']|] eqn:Hinfer.
  2: { inversion Hinfer_bounds; subst. contradiction. }
  clear Hnnil.
  inversion Hinfer_bounds; subst prop_var'; rename H0 into Hbounds.
  apply infer_domains_correct with (vs := (Some (constraint_to_vs constr))) (doms := doms) (xconsq := prop_var); try assumption.
  clear -Hvalid Hbounds Hinfer.
  intros Hdom_holds.
  apply Hvalid; clear Hvalid.
  subst bounds.
  unfold valid_bounds, domains_to_bounds.
  intros a.
  rewrite in_flat_map_option.
  intros ([x dom] & Hin & Htobound).
  apply infer_domains_vs with (x := x) (dom := dom) in Hinfer;
  try assumption.
  rewrite smap_in_spec in Hin.
  apply (Hdom_holds x dom) in Hin; clear Hdom_holds.
  unfold domain_to_bound in Htobound.
  destruct dom as [lb ub holes] eqn:Hdom;
  destruct lb as [lb|]; destruct ub as [ub|]; try easy; simpl in Htobound.
  inversion Htobound; subst; clear Htobound.
  destruct Hin as (Hub & Hlb & _).
  unfold task_in_constraint. simpl.
  destruct constraint_to_param_map as [p u] eqn:Hparams.
  split.
  - clear -Hinfer Hparams.
    unfold constraint_to_param_map in Hparams.
    symmetry in Hparams.
    apply param_map_in in Hparams.
    + unfold activity_list.
      unfold activity_list_inner.
      rewrite in_map_iff.
      exists (mkActDef x p u).
      simpl. split; try reflexivity.
      rewrite in_map_iff in Hparams.
      destruct Hparams as (act & Hact_def & Hin).
      destruct act; inversion Hact_def; subst.
      exact Hin.
    + clear -Hinfer. 
      unfold constraint_to_vs in Hinfer.
      rewrite sstr.build_spec in Hinfer.
      rewrite map_map.
      rewrite in_map_iff.
      unfold constraint_to_vars in Hinfer.
      rewrite in_map_iff in Hinfer.
      destruct Hinfer as (a & Hax & Hin).
      exists a.
      destruct a; subst.
      split; try reflexivity.
      exact Hin.
  - simpl. lia.
Qed.

Lemma bounds_unique :
  forall constr fact prop_var bounds,
  inferred_cumulative_bounds constr fact = (bounds, prop_var)
    ->
  unique_bounds bounds.
Proof.
  intros c fact prop_var bounds.
  unfold inferred_cumulative_bounds.
  destruct infer_domains as [[doms prop_var']|].
  2: { intros H; inversion H; subst. unfold unique_bounds. apply NoDup_nil. }
  intros H; inversion H; subst; clear H.
  unfold unique_bounds.
  unfold domains_to_bounds.
  remember (smap.bindings doms) as l.
  rewrite flat_map_option_as_filter_map with (d := default_bound).
  apply nodup_key with (a_k := fst).
  - apply nodup_sublist with (l2 := (map fst l)) (eq_dec := String.string_dec ).
    + subst l. apply nodup_bindings_keys. 
    + rewrite sub_list_app_perm.
      remember (filter_f_option
        (domain_to_bound
        (constraint_to_param_map
        c))) as f.
      specialize (partition_as_filter) with (f := f) (l := l) as Hpartfilt.
      exists (map fst (snd (partition f l))).
      rewrite <- map_app.
      apply Permutation.Permutation_map.
      assert (filter f l = fst (partition f l)).
      { rewrite Hpartfilt. simpl. reflexivity. }
      rewrite H.
      apply permutation_partition.
  - intros a Hin.
    unfold option_map_default.
    rewrite filter_In in Hin.
    unfold filter_f_option in Hin.
    destruct (domain_to_bound
      (constraint_to_param_map c) a) eqn:Hto_bound.
    + unfold domain_to_bound in Hto_bound.
      destruct a as [x' dom].
      destruct (d_lb dom); destruct (d_ub dom); try discriminate Hto_bound.
      destruct p as [[x]].
      inversion Hto_bound; subst x.
      simpl. reflexivity.
    + destruct Hin as [_ Hfalse].
      discriminate Hfalse.
Qed.

Lemma checker_cumulative :
  forall fact sol constr,
  Is_true (cumulative_decide constr sol)
  -> Is_true (cumulative_checker fact constr)
  -> inference_valid sol fact.
Proof.
  intros fact sol constr.
  intros Hconstr Hchecked.
  apply Is_true_eq_true in Hchecked.
  unfold cumulative_checker in Hchecked.
  destruct (inferred_cumulative_bounds constr fact) as [bounds' prop_var] eqn:Hbounds.
  destruct bounds' as [|b bounds'].
  { discriminate Hchecked. }
  remember (b :: bounds') as bounds.
  apply inferred_bounds_correct with (constr := constr) (bounds := bounds) (prop_var := prop_var); try assumption.
  { rewrite Heqbounds. easy. }
  apply bounds_unique in Hbounds as Hunique.
  clear -Hunique Hconstr Hchecked.
  intros Hvalid.
  
  remember (horizon_start constr) as h_start;
  remember (horizon_end constr) as h_end;
  remember (ZRange.build_range h_start h_end) as times.
  assert (ZRange.is_range h_start h_end times) as Htimesrange.
  {
    rewrite Heqtimes. apply ZRange.build_range_correct.
    rewrite Heqh_start; rewrite Heqh_end.
    apply constr.(horizon_consistent). 
  }
  clear Heqtimes.

  specialize (resource_profile_correct (capacity constr) bounds times) as Hr_profile_correct.

  destruct (resource_profile (capacity constr)
  bounds times) as [r_profile |] eqn:Hprofile.
  {
    apply exists_cannot_schedule with (constr := constr) (sol := sol) (bounds := bounds).
    - apply Is_true_eq_true in Hconstr. exact Hconstr.
    - apply Hunique.
    - apply Hvalid.
    - apply existsb_exists in Hchecked.
      destruct Hchecked as [a [Hbound Hcannot_sched]].
      pose proof Hbound as Hinbound.
      apply Hvalid in Hbound.
      unfold task_in_constraint in Hbound.
      destruct a as [[x [lb size]] [p u]] eqn:Ha.
      destruct Hbound as [Hstart Hinactivity].
      rewrite <- Ha in *.
      remember (make_activity a (constraint_to_vars constr) sol) as act.
      exists act.
      unfold cannot_schedule_activity_w_profile in Hcannot_sched.
      rewrite Ha in Hcannot_sched.
      rewrite negb_true_iff in Hcannot_sched.
      specialize has_n_true_all_runs as Hruns.

      remember (capacity constr) as c.
      specialize (resource_profile_as_range times c bounds h_start h_end) as Hr_profile_range.
      rewrite Hprofile in Hr_profile_range.

      apply Hvalid in Hinbound as Htask.
      apply Hr_profile_range in Htimesrange as Hprofilerange.
      unfold is_as_range in Hprofilerange.
      apply ZRange.is_range_length in Hprofilerange.
      rewrite length_map in Hprofilerange.
      destruct Hinactivity as [Hacthor Hactbounds].
      unfold in_horizon in Hacthor.

      remember (Z.to_nat (h_end - ((start act) + Z.of_N p) + 1)) as i.
      apply (run_at_seq_fk_false r_profile) with (fb := (can_be_active_at_t c a)) (n := (N.to_nat p)) (i := i) in Hr_profile_range.
      + destruct Hr_profile_range as [[t_false p_usage] [Ht [Hprofile_in Hfalse]]].
        apply Hr_profile_correct in Hprofile_in; clear Hr_profile_correct.
        destruct Hprofile_in as [Httimes Htusage].

        rewrite Heqi in Ht; subst i.
        simpl in Ht.
        assert (p_time act = p) as Hp.
        {
          rewrite Heqact. rewrite Ha. unfold make_activity.
          simpl. reflexivity.
        }
        admit.
        (*subst p; subst h_start; subst h_end;
        pose proof Ht as Ht'; clear Ht;
        assert (start act <= t_false < start act + Z.of_N (p_time act)) as Ht by lia; clear Ht'.
        exists t_false.
        split. { apply Htimesrange. apply Httimes. }
        split. { exact Hstart. }
        split. { exact Ht. }
        rewrite Ha in Hfalse.
        apply can_be_active_at_t_false in Hfalse.
        destruct Hfalse as [Hman_nil Hfalse].
        assert (p_usage + u > c)%N as Husage.
        {
          destruct Hfalse as [Husage | [Htoutlb | Houtub]].
          - exact Husage.
          - lia.
          - lia. 
        }
        clear Hfalse.
        split.
        {
          unfold activities_bounds_active_at.
          rewrite in_flat_map_option.
          unfold not.
          intros [a_man [Ha_man_bounds Hman]].
           
          pose proof Ha_man_bounds as Ha_man_inbounds.
          
          apply Hvalid in Ha_man_bounds.

          destruct a_man as [[x' [lb' size']] [p' u']].
          unfold activity_bounds_is_active in Hman.
          destruct (interval_to_bounds (lb', size')) as [lb_b ub'] eqn:Hbound_lb.
          destruct (mandatory_active lb_b ub' t_false p') eqn:His_man.
          2: { discriminate Hman. }
          inversion Hman; subst x'; subst u'.
          apply nodup_map with (a1 := a) (a2 := (a_name act, (lb', size'), (p', usage act))) in Hunique.
          - rewrite Ha in Hunique. inversion Hunique.
            subst lb'; subst size'; subst p'; clear Hunique.
            unfold activity_bounds_is_active in Hman_nil.
            rewrite Hbound_lb in Hman_nil.
            rewrite His_man in Hman_nil.
            discriminate Hman_nil. 
          - repeat decide equality.
          - exact String.string_dec.
          - exact Hinbound.
          - exact Ha_man_inbounds.
          - rewrite Heqact. rewrite Ha. unfold make_activity. simpl. reflexivity.
        }
        assert (usage act = u) as Hu.
        {
          rewrite Heqact. rewrite Ha. unfold make_activity. simpl. reflexivity. 
        }
        rewrite Hu. lia. *)
      + enough (p >= 1)%N by lia.
        rewrite Ha in Htask.
        apply task_valid_processing in Htask.
        lia.
      + enough (p <= horizon_length constr)%N as Hhor_len.
        { unfold horizon_length in Hhor_len.
        lia. }
        rewrite Ha in Htask.
        apply task_valid_processing in Htask.
        admit.
      + rewrite Ha in Htask.
        apply task_valid_processing in Htask.
        subst h_end; subst h_start.
        rewrite Hprofilerange.
        rewrite Heqi.
        admit.
      + apply Htimesrange.
      + apply Hruns.
        rewrite Ha.
        apply Hcannot_sched.
  }
  - apply resource_profile_conflict with (sol := sol) in Hprofile.
    + apply Hprofile.
    + apply Is_true_eq_true. exact Hconstr.
    + exact Hvalid.
    + exact Hunique.
    + subst h_start; subst h_end. apply Htimesrange.
Admitted. 
 
(* Definition mkAtm (x : string) (atm_comparator : AtomicComparator) (atm_value : Z) := *)
(*   {| *)
(*     var := interval {| name := x; lower_bound := Z0; size := 50 |} ;  *)
(*     comparator := atm_comparator ;  *)
(*     value := atm_value *)
(*   |}. *)

(* Definition mkInf (lhs : list Atomic) (rhs : option Atomic) := *)
(*   let lhs_neg := (map atomic_not lhs) in *)
(*     lhs_neg ++ *)
(*     match rhs with *)
(*     | None => nil *)
(*     | Some rhs => rhs :: nil *)
(*     end. *)

Open Scope string.

(* Mandatory conflict *)    
Compute 
  let constr := build_cumulative 
    (
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 3%N; def_u := 1%N; |} ::
      nil
    ) 
    1%N Z0 20%N in
  let fact := 
    {| 
      i_premises :=
        ("x", mk_atm_ge 0) ::
        ("x", mk_atm_le 2) ::
        ("y", mk_atm_ge 1) ::
        ("y", mk_atm_le 3) :: nil ;
      i_consequent := None
    |}
  in
  (Bool.eqb (cumulative_checker fact constr) true).

(* 1-step *)
Compute 
  let constr := build_cumulative 
    (
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 1%N; def_u := 1%N; |} ::
      nil
    ) 
    1%N Z0 20%N in
  let fact := 
    {| 
      i_premises :=
        ("x", mk_atm_ge 0) ::
        ("x", mk_atm_le 2) ::
        ("y", mk_atm_ge 2) :: 
        ("y", mk_atm_le 2) :: nil ;
      i_consequent := None
    |}
  in
  cumulative_checker fact constr.

(* TODO This does not work unless I have a working negation *)
Compute 
  let constr := build_cumulative 
    (
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 1%N; def_u := 1%N; |} ::
      nil
    ) 
    1%N Z0 20%N in
  let fact := 
    {| 
      i_premises :=
        ("x", mk_atm_ge 0) ::
        ("x", mk_atm_le 2) ::
        ("y", mk_atm_ge 2) :: nil ;
      i_consequent := Some ("y", mk_atm_ge 3)
    |}
  in
  cumulative_checker fact constr.

(* Multi-step simple *)
Compute 
  let constr := build_cumulative 
    (
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 1%N; def_u := 1%N; |} ::
      nil
    ) 
    1%N Z0 20%N in
  let fact := 
    {| 
      i_premises :=
        ("x", mk_atm_ge 0) ::
        ("x", mk_atm_le 2) ::
        ("y", mk_atm_ge 2) ::
        ("y", mk_atm_le 3) :: nil ;
      i_consequent := None
    |}
  in
  cumulative_checker fact constr.

Compute 
  let constr := build_cumulative 
    (
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 1%N; def_u := 1%N; |} ::
      nil
    ) 
    1%N Z0 20%N in
  let fact := 
    {| 
      i_premises :=
        ("x", mk_atm_ge 0) ::
        ("x", mk_atm_le 2) ::
        ("y", mk_atm_ge 2) :: nil ;
      i_consequent := Some ("y", mk_atm_ge 4)
    |}
  in
  cumulative_checker fact constr.

(* Multi-step hole *)
Compute 
  let constr := build_cumulative 
    (
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 2%N; def_u := 1%N; |} ::
      nil
    ) 
    1%N Z0 20%N in
  let fact := 
    {| 
      i_premises :=
        ("x", mk_atm_ge 0) ::
        ("x", mk_atm_le 2) ::
        ("y", mk_atm_ge 1) ::
        ("y", mk_atm_le 3) :: nil ;
      i_consequent := None
    |}
  in
  cumulative_checker fact constr.
Compute 
  let constr := build_cumulative 
    (
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 2%N; def_u := 1%N; |} ::
      nil
    ) 
    1%N Z0 20%N in
  let fact := 
    {| 
      i_premises :=
        ("x", mk_atm_ge 0) ::
        ("x", mk_atm_le 2) ::
        ("y", mk_atm_ge 1) :: nil ;
      i_consequent := Some ("y", mk_atm_ge 4)
    |}
  in
  cumulative_checker fact constr.
