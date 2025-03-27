
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Require Import Bool.
Require Import String.
Require Import Checker.Nogood.
Require Import Checker.Cumulative.
Require Checker.CumulativeUtil.
Import CumulativeUtil.ResourceSum.
Require Import Checker.Utility.
Import ListEx.
Require Import Lia.
Require Import Checker.Atomic.
Require Import Checker.Variable.
Require Checker.Utility.
Require Import Checker.Domain.

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

Open Scope Z_scope.


Lemma h_true_with_false :
  forall b (H : b = true),
    b = false -> False.
Proof.
  intros b H Hfalse. rewrite Hfalse in H.
  discriminate H.
Qed.

Open Scope N_scope.
Lemma exceeds_at_t_dec_false :
  forall (c : CumulativeConstraint) (a : Assignment),
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
  rewrite ZRange.build_range_correct in Hhorizon.
  2: apply c.(horizon_consistent).
  apply Hdecide in Hhorizon as Husagelt.
  clear Hhorizon; clear Hdecide.
  rewrite N.leb_le in Husagelt.
  contradiction.
Qed.

Open Scope Z_scope.
Definition var_has_bounds (a : Assignment) (v : Var) (lb : Z) (ub : Z) :=
  lb <= (a.(find_value) v) <= ub.

(* Here, you might think the implication goes both ways, but I was shown this cannot be, so reconsider! *)
Lemma active_at :
  forall t (activities : list Activity),
    forall a lb ub, In a activities ->
      lb <= a.(start) <= ub ->
      ub <= t < (lb + (Z.of_N a.(p_time)))
      ->
      In a (activities_at_t activities t).
Proof.
  intros t activities a lb ub.
  intros Hl Hbounds Ht.
  unfold activities_at_t.
  rewrite filter_In.
  split.
  - exact Hl.
  - unfold is_active_at.
    rewrite andb_true_iff.
    repeat rewrite Z.leb_le.
    lia.
Qed.

Definition mandatory_active (lb : Z) (ub : Z) (t : Z) (p_time : N) :=
  (ub <=? t) && (t <? (lb + (Z.of_N p_time))).


Definition constraint_to_intervals (c : CumulativeConstraint) : list (string * zn_interval * (N * N)) :=
  map (fun elt =>
    match elt with
    | (v, p, u) =>
      match v with
      | interval v =>
        (v.(name), (v.(lower_bound), N.of_nat v.(size)), (p, u))
      end
    end
  ) c.(vs).

Definition inferred_cumulative_bounds (c : CumulativeConstraint) (inference : list Atomic) :=
  apply_atomics_to_variables (constraint_to_intervals c) (map atomic_not inference).

Definition inference_negated (inference : list Atomic) (sol : Assignment) :=
  forall atomic, In atomic (map atomic_not inference) ->
    Is_true (test_atomic_assignment atomic sol).

Definition activity_bounds_is_active (t : Z) (activity : string * zn_interval * (N * N)) : list (string * N) :=
  match activity with
  | (x, i, (p_time, usage)) =>
    match interval_to_bounds i with
    | (lb, ub) =>
      if mandatory_active lb ub t p_time
        then (x, usage) :: nil
        else nil
    end
  end.


Definition activities_bounds_active_at (t : Z) (activities : list (string * zn_interval * (N * N))) :=
  nodup xn_eq_dec (flat_map (activity_bounds_is_active t) activities).

Fixpoint find_overloaded_t_with_mandatory (capacity : N) (ts : list Z) (activities : list (string * zn_interval * (N * N))) := 
  match ts with
  | nil => None
  | t :: ts' =>
    match res_sum capacity (activities_bounds_active_at t activities) with
    | (summed, result, false) => Some (t, summed, result)
    | _ => find_overloaded_t_with_mandatory capacity ts' activities
    end
  end
.

(* Definition i_mandatory_active_at (t : Z) (i : (string * zn_interval * (N * N))) := 
  match i with
  | (_, (lb, size), (p_time, _)) =>
     mandatory_active lb (lb + Z.of_N size) t p_time = true
  end. *)

Definition interval_to_usage (i : (string * zn_interval * (N * N))) : N :=
  match i with
  | (_, _, (_, usage)) => usage
  end.

Open Scope N_scope.

Lemma overload_props :
  forall capacity ts activities,
    match find_overloaded_t_with_mandatory capacity ts activities with
    | None => True
    | Some (t, _, _) => xn_sum (activities_bounds_active_at t activities) > capacity /\ In t ts
    end.
Proof.
  intros c ts activities.
  destruct (find_overloaded_t_with_mandatory c ts activities) as [[[t summed] result] |] eqn:Hres.
  - unfold find_overloaded_t_with_mandatory in Hres.
    induction ts as [| ts_t ts].
    + discriminate Hres.
    + specialize (res_sum_semantics c (activities_bounds_active_at ts_t activities)) as Hres_sum.
      destruct (res_sum c (activities_bounds_active_at ts_t activities)) as [[rs_summed rs_result] rs_b].
      destruct rs_b.
      * apply IHts in Hres; clear IHts.
        destruct Hres as [Hgt Hin].
        split.
        -- exact Hgt.
        -- simpl. right. exact Hin.
      * clear IHts. inversion Hres. subst ts_t; subst rs_summed; subst rs_result. destruct Hres_sum as [_ [_ [Hsub Hgt]]].
        split.
        -- exact Hgt.
        -- simpl. left. reflexivity.
  - reflexivity.
Qed. 

Definition resource_profile_t (capacity : N) (activities : list (string * zn_interval * (N * N))) (t : Z) : (Z * N) :=
  match res_sum capacity (activities_bounds_active_at t activities) with
  (_, usage, _) => (t, usage)
  end
.

Definition resource_profile (capacity : N) (activities : list (string * zn_interval * (N * N))) (times : list Z) := 
  map (resource_profile_t capacity activities) times
.

Lemma resource_profile_correct :
  forall capacity activities times usage t,
    In (t, usage) (resource_profile capacity activities times) ->
      In t times /\
      xn_sum (activities_bounds_active_at t activities) >= usage.
Proof.
  intros c activities times usage t.
  intros Hin.
  unfold resource_profile in Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [t' [Hprofile Hintimes]].
  unfold resource_profile_t in Hprofile.
  specialize (res_sum_semantics c (activities_bounds_active_at t' activities)) as Hres_sum.
  destruct (res_sum c
  (activities_bounds_active_at t'
  activities)) as [[summed sum_result] b].
  inversion Hprofile. subst t'; subst sum_result; clear Hprofile.
  remember (activities_bounds_active_at t activities) as active; clear Heqactive.
  split.
  - exact Hintimes.
  - clear Hintimes. destruct b.
    + destruct Hres_sum as [Hisusage]. lia.
    + destruct Hres_sum as [Husage [_ [Hsub _]]].
      rewrite <- Husage.
      specialize (xn_sum_sub_list summed active Hsub) as Hsub_sum.
      lia.
Qed.

Definition can_be_active_at_t (capacity : N) (profile_usage : N) (activity : string * zn_interval * (N * N)) (time : Z) : bool :=
  match activity with
  | (_, _, (_, usage)) =>
    match activity_bounds_is_active time activity with
    | nil => true
    | _ => profile_usage + usage <? capacity
    end
  end
.

Open Scope nat_scope.
Fixpoint has_hole_of_size (l : list bool) (size : nat) : bool :=
  if size =? 0
    then true
    else
      match l with
      | nil => false
      | b :: l' =>
        if b
          then has_hole_of_size l' (pred size)
          else has_hole_of_size l' size
      end
.

Open Scope Z_scope.
Definition make_active_list_f (capacity : N) (activity : string * zn_interval * (N * N)) (profile_entry : (Z * N)) : list bool :=
  match activity with
  | (_, (lb, size), _) =>
    match profile_entry with
    | (t, profile_usage) =>
      if (t >=? lb) && (t <=? (lb + Z.of_N size))
        then (can_be_active_at_t capacity profile_usage activity t) :: nil
        else nil
    end
  end
.

Definition make_active_list (capacity : N) (profile : list (Z * N)) (activity : string * zn_interval * (N * N)) : list bool :=
  flat_map (make_active_list_f capacity activity) profile.

Definition cannot_schedule_activity_w_profile (capacity : N) (profile : list (Z * N)) (activity : string * zn_interval * (N * N)) : bool :=
  match activity with
  | (_, _, (duration, _)) =>
    negb (has_hole_of_size (make_active_list capacity profile activity) (N.to_nat duration))
  end.

Definition var_empty_domain (v : Var) (sol : Assignment) :=
  exists n m,
    n < m
      /\
    m <= sol.(find_value) v <= n.

Definition ex_var_empty_domain (sol : Assignment) :=
  exists (v : Var),
    var_empty_domain v sol.

Definition cumulative_checker (inference : list Atomic) (constraint : CumulativeConstraint) : bool :=
  let times := (ZRange.build_range constraint.(horizon_start) constraint.(horizon_end)) in
  match inferred_cumulative_bounds constraint inference with
  | None => false
  | Some bounds => 
    match find_overloaded_t_with_mandatory (constraint.(capacity)) times bounds with
    | None => 
      let r_profile := resource_profile (constraint.(capacity)) bounds times in
      existsb (cannot_schedule_activity_w_profile (constraint.(capacity)) r_profile) bounds 
    | Some _ => true
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
(* Lemma checker_true_finds_overloaded_t :
  forall fact sol constr,
  inference_negated fact sol ->
  cumulative_checker fact constr = true
  ->
  exists t,
    horizon_start constr <= t <= horizon_end constr /\
    (usage_sum
    (activities_at_t (activity_list constr sol) t) >
    capacity constr)%N.
Proof.
  intros fact sol constr.
  intros Hinf Hchecked.
  unfold cumulative_checker in Hchecked.
  destruct (inferred_cumulative_bounds constr fact) as [bounds |] eqn:Hbounds.
  - specialize (overload_props constr.(capacity) (ZRange.build_range constr.(horizon_start) constr.(horizon_end)) bounds) as Hoverload.
    destruct (find_overloaded_t_with_mandatory (capacity constr)
    (ZRange.build_range (horizon_start constr)
    (horizon_end constr)) bounds) as [[[t usages_t] _] |].
    {
     exists t.
     destruct Hoverload as [Hsum Hinhorz].
     split.
     - rewrite ZRange.build_range_correct.
      + exact Hinhorz.
      + exact constr.(horizon_consistent).
    - clear Hinhorz; clear Hchecked; clear usages_t.
      unfold usage_sum.
      apply xn_sum_sub_list_gtn with (l1 := (activities_bounds_active_at t bounds)).
      + clear Hsum.
        apply sub_list_if_in_nodup.
        * intros a Hin.
          rewrite in_map_iff.
          assert (In a (activities_bounds_active_at t bounds)) as Hin2 by assumption.
          unfold activities_bounds_active_at in Hin.
          rewrite nodup_In in Hin.
          rewrite in_flat_map in Hin.
          destruct Hin as [a' [Hinbounds Hinres]].
          destruct a' as [[x [lb size]] [p u]] eqn:Ha'.
          unfold activity_bounds_is_active in Hinres.
          destruct (interval_to_bounds (lb, size)) as [lb' ub] eqn:Hibounds. unfold interval_to_bounds in Hibounds; inversion Hibounds; subst lb'; symmetry in H1; clear Hibounds.
          destruct (mandatory_active lb ub t p) eqn:Hmand.
          2: destruct Hinres.
          simpl in Hinres. destruct Hinres; try contradiction. subst a.
          unfold inferred_cumulative_bounds in Hbounds.
          rewrite <- Ha' in Hinbounds.
          specialize (apply_atomics_correct (N * N) ((constraint_to_intervals constr)) (map atomic_not fact) bounds Hbounds a' Hinbounds) as Happly.
          rewrite Ha' in Happly; clear Hinbounds; clear Ha'; clear a'.
          destruct Happly as [lb_init [size_init [Hinis [atoms_applied [Hatomsin Hatomproof]]]]].
          unfold constraint_to_intervals in Hinis.
          rewrite in_map_iff in Hinis.
          destruct Hinis as [[[v p'] u'] [His Hinc]].
          destruct v; inversion His.
          subst p'; subst u'.
          exists (mkAct x (sol.(find_value) (interval var)) p u). split.
          { simpl. subst x. reflexivity. }
          apply active_at with (lb := lb) (ub := ub).
          -- unfold activity_list. unfold activity_list_inner. rewrite in_map_iff.
            exists (interval var, p, u).
            split.
            ++ unfold activity_list_inner_f. subst x.
            reflexivity.
            ++ exact Hinc.
          -- simpl. subst ub.
            apply atomic_proof_correct with (x := x) (atoms := atoms_applied) (lb_init := lb_init) (size_init := size_init); try assumption.
            intros atom Hinapplied.
            apply Hinf.
            apply Hatomsin.
            exact Hinapplied.
          -- simpl. unfold mandatory_active in Hmand.
            apply andb_true_iff in Hmand.
            rewrite Z.leb_le in Hmand.
            rewrite Z.ltb_lt in Hmand.
            exact Hmand. 
        * unfold activities_bounds_active_at. 
          (* TODO: try and get rid of this, but it only really matters for performance *)
          apply NoDup_nodup.
      + exact Hsum.
    }
    { discriminate Hchecked. }
  - discriminate Hchecked.
Qed. *)



(* Definition empty_domain (x : string) (sol : Assignment) :=
  exists n m,
    n < m ->
      forall v,
        var_name v = x ->
          (sol.(find_value) v) >= n

. *)



Lemma empty_domain_is_false :
  forall sol,
    ex_var_empty_domain sol -> False.
Proof.
  intros sol. unfold not. intros Hempty.
  unfold ex_var_empty_domain in Hempty; unfold var_empty_domain in Hempty.
  destruct Hempty as [v [n [m Hempty]]].
  lia.
Qed.

Lemma checker_not_cumulative :
  forall fact sol constr,
  Is_true (cumulative_decide constr sol)
  -> Is_true (cumulative_checker fact constr)
  -> inference_negated fact sol
  -> False.
Proof.
  intros fact sol constr.
  intros Hconstr Hchecked Hneg.
  apply Is_true_eq_true in Hchecked.
  

  (* apply sufficient_false.
  apply Is_true_eq_true in Hchecked.
  apply checker_true_finds_overloaded_t with (fact := fact); assumption. *)
Admitted.

Lemma is_true_false_not :
  forall b, Is_true b -> b = false -> False.
Proof.
  intros. unfold Is_true in H.
  rewrite H0 in H. exact H.
Qed.

Lemma is_true_not_false :
  forall b, (b = false -> False) -> Is_true b.
Proof.
  intros. destruct b.
  - reflexivity.
  - simpl. apply H. reflexivity.
Qed.

Lemma cumulative_checker_valid :
  forall fact sol constr,
  Is_true (cumulative_decide constr sol) ->
  Is_true (cumulative_checker fact constr) ->
  Is_true (satisfies_nogood fact sol).
Proof.
  intros fact sol constr.
  intros Hcumul Hchecked.
  apply is_true_not_false.
  intros Hsat.
  apply neg_atomic in Hsat.
  apply checker_not_cumulative with (fact := fact) (sol := sol) (constr := constr); assumption.
Qed.


