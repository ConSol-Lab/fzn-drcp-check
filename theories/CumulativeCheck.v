
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

Definition is_as_range {A} (f : A -> Z) (s : Z) (e : Z) (l : list A) :=
  ZRange.is_range s e (map f l).


Open Scope Z_scope.
Lemma resource_profile_as_range :
  forall times s e c activities,
    ZRange.is_range s e times
      ->
    is_as_range fst s e (resource_profile c activities times).
Proof.
  induction times.
  - intros. unfold ZRange.is_range in H.
    destruct H as [Hse [Hn _]].
    assert (s <= s <= e)%Z as Hsse by lia.
    rewrite Hn in Hsse. destruct Hsse.
  - intros s e c act.
    intros Htimes_range.
    unfold is_as_range. unfold resource_profile.
    simpl. assert (forall (t : Z), fst (resource_profile_t c act t) = t).
    {
      intros t.
      unfold resource_profile_t. destruct (res_sum c(activities_bounds_active_at t act)) as [[_ u] _].
      simpl.
      reflexivity.
    }
    rewrite H.
    destruct times as [| a' times].
    { simpl. exact Htimes_range. }
    simpl.
    rewrite H. 
    apply ZRange.is_range_endpoints in Htimes_range as Haa'.
    destruct Haa' as [Ha Ha'].
    subst a; subst a'.
    apply ZRange.is_range_implies_pred_range in Htimes_range as Hpred_range.
    specialize (IHtimes s (e - 1) c act Hpred_range).
    unfold resource_profile in IHtimes.
    destruct IHtimes as [Hse [Hn Hsucc]].
    split.
    + lia.
    + simpl in Hn. simpl in Hsucc.
      rewrite H in Hn. rewrite H in Hsucc.
      split.
      {
        intros n. split.
        - intros Hsne.
          destruct (n =? e) eqn:Hne.
          { rewrite Z.eqb_eq in Hne; subst n.
            simpl. left. reflexivity. }
          rewrite Z.eqb_neq in Hne.
          assert (s <= n <= e - 1) as Hsne1 by lia.
          rewrite Hn in Hsne1.
          destruct Hsne1.
          + subst n. simpl. right. left. reflexivity.
          + simpl. right. right. assumption.
        - intros Hin.
          destruct Hin as [He | Hin]. 
          + subst n. lia.
          + simpl in Hin. rewrite <- Hn in Hin.
            lia.
    }
    unfold ZRange.succ_seq.
    apply Sorted_cons.
    * exact Hsucc.
    * apply HdRel_cons.
      unfold ZRange.is_succ.
      lia.
Qed.


Open Scope N_scope.
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

Open Scope Z_scope.

      



Definition c_var_with_x (x : string) (elt : (Var * N * N)) :=
  match elt with
  | (v, _, _) =>
    (x =? var_name v)%string
  end.

Definition x_start_time (x : string) (c : CumulativeConstraint) (sol : Assignment) : Z :=
  match (find (c_var_with_x x) c.(vs)) with
  | None => Z0
  | Some (v, _, _) => sol.(find_value) v
  end.

Definition make_activity (a : string * zn_interval * (N * N)) (c : CumulativeConstraint) (sol : Assignment) :=
  match a with
  | (x, (lb, size), (p, u)) =>
      mkAct x (x_start_time x c sol) p u
  end.

Lemma activity_list_in_vs :
  forall c a sol,
    In a (activity_list c sol)
      ->
    forall v,
      var_name v = a.(a_name)
        ->
      In (v, a.(p_time), a.(usage)) c.(vs).
Proof.
  intros c a sol.
  intros Hin.
  intros v'.
  unfold activity_list in Hin.
  unfold activity_list_inner in Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [[[v p] u] [Hinner Hin]].
  unfold activity_list_inner_f in Hinner.
  destruct v.
  rewrite <- Hinner.
  simpl.
  intros Hname.
  remember (interval var) as v.
  specialize c.(x_determine_var) as Hdeterm.
  unfold x_determines_var in Hdeterm.
  apply Hdeterm with (v2 := v') in Hin as Hvv'.
  2: { rewrite Heqv. simpl. symmetry. exact Hname. }
  subst v'.
  exact Hin.
Qed.

Lemma activity_list_in_vs_ex :
  forall c a sol,
    In a (activity_list c sol)
      ->
    exists v,
      var_name v = a.(a_name)
        /\
      In (v, a.(p_time), a.(usage)) c.(vs).
Proof.
  intros c a sol.
  intros Hin.
  unfold activity_list in Hin.
  unfold activity_list_inner in Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [[[v p] u] [Hinner Hin]].
  exists v.
  unfold activity_list_inner_f in Hinner.
  destruct v.
  rewrite <- Hinner.
  simpl.
  split.
  - reflexivity.
  - exact Hin.
Qed.

Definition task_in_constraint (a : string * zn_interval * (N * N)) (c : CumulativeConstraint) (sol : Assignment) :=
  let act := (make_activity a c sol) in
    In act (activity_list c sol)
      /\
    match a with
    | (x, (lb, size), (p, u)) =>
      lb <= act.(start) <= lb + Z.of_N size
    end.

Lemma two_tasks_in_constraint_x_eq (a1 a2 : string * zn_interval * (N * N)) (c : CumulativeConstraint) (sol : Assignment) :
  task_in_constraint a1 c sol
    ->
  task_in_constraint a2 c sol
    ->
  match a1 with
  | (x, i1, _) =>
    match a2 with 
    | (x', i2, _) =>
      x = x'
        ->
      make_activity a1 c sol = make_activity a2 c sol
    end
  end.
Proof.
  intros Ha1 Ha2.
  destruct a1 as [[x [lb size]] [p u]].
  destruct a2 as [[x' [lb' size']] [p' u']].
  intros Hxx'.
  subst x'.
  unfold task_in_constraint in Ha1, Ha2.
  unfold make_activity in *.
  simpl in *.
  destruct Ha1 as [Hinl1 Hbound1].
  destruct Ha2 as [Hinl2 Hbound2].
  apply activity_list_in_vs_ex in Hinl1, Hinl2.
  simpl in *.
  destruct Hinl1 as [v [Hnamev Hin]].
  destruct Hinl2 as [v' [Hnamev' Hin']].
  specialize c.(x_determine_params) as Hc_determ.
  unfold x_determines_params in Hc_determ.
  apply Hc_determ with (v2 := v') (p2 := p') (u2 := u') in Hin.
  inversion Hin; subst v'; subst p'; subst u'.
  - reflexivity.
  - exact Hin'.
  - rewrite Hnamev. rewrite Hnamev'. reflexivity.
Qed.
  

Open Scope N_scope.



Definition unique_bounds (bounds : list (string * zn_interval * (N * N))) :=
  forall a1 a2,
    In a1 bounds -> In a2 bounds
    -> bound_name a1 = bound_name a2
    -> a1 = a2. 

Definition valid_bounds (bounds : list (string * zn_interval * (N * N))) (c : CumulativeConstraint) (sol : Assignment) :=
  forall a, In a bounds -> task_in_constraint a c sol.

Lemma valid_bounds_mandatory_sublist :
  forall constr sol bounds t,
  valid_bounds bounds constr sol
    ->
  sub_list xn_eq_dec (activities_bounds_active_at t bounds) ((map act_to_xn (activities_at_t (activity_list constr sol) t))).
Proof.
  intros constr sol bounds t.
  intros Hvalid.
  apply sub_list_if_in_nodup.
  - intros a Hin.
    rewrite in_map_iff.
    pose proof Hin as Hin2.
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
    apply Hvalid in Hinbounds.
    unfold task_in_constraint in Hinbounds.
    rewrite <- Ha' in *.
    remember (make_activity a' constr sol) as act.
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
  - unfold activities_bounds_active_at. 
    (* TODO: try and get rid of this, but it only really matters for performance *)
    apply NoDup_nodup.
Qed.

Lemma bounds_sum_implies_usage :
  forall constr sol bounds usage t,
  valid_bounds bounds constr sol
    ->
  xn_sum (activities_bounds_active_at t bounds) >= usage
    ->
  usage_sum (activities_at_t (activity_list constr sol) t) >= usage.
Proof.
  intros constr sol bounds usage t.
  intros Hvalid Hsum.
  unfold usage_sum.
  apply xn_sum_sub_list_gen with (l1 := (activities_bounds_active_at t bounds)).
  - apply valid_bounds_mandatory_sublist. exact Hvalid.
  - exact Hsum.
Qed.

Lemma constraint_to_intervals_unique :
  forall c,
    unique_bounds (constraint_to_intervals c).
Proof.
  intros c.
  unfold unique_bounds.
  intros a1 a2.
  intros Hin1 Hin2.
  intros Hname.
  destruct a1 as [[x1 [lb1 size1]] [p1 u1]].
  destruct a2 as [[x2 [lb2 size2]] [p2 u2]].
  unfold bound_name in Hname.
  subst x2.
  unfold constraint_to_intervals in Hin1, Hin2.
  rewrite in_map_iff in Hin1, Hin2.
  destruct Hin1 as [[[v1 p1'] u1'] [H1 Hin1]].
  destruct v1 as [v1]. inversion H1.
  subst lb1; subst size1; subst p1'; subst u1'; clear H1.
  destruct Hin2 as [[[v2 p2'] u2'] [H2 Hin2]].
  destruct v2 as [v2]. inversion H2.
  subst lb2; subst size2; subst p2'; subst u2'; clear H2.
  specialize c.(x_determine_params) as Hdeterm.
  unfold x_determines_params in Hdeterm.
  apply Hdeterm with (v2 := (interval v2)) (p2 := p2) (u2 := u2) in Hin1 as Hv1v2.
  - inversion Hv1v2. reflexivity.
  - exact Hin2.
  - simpl. rewrite H0. rewrite H1. reflexivity.
Qed.

Open Scope Z_scope.
Lemma inferred_cumulative_bounds_valid :
  forall (c : CumulativeConstraint) inference sol bounds,
    inference_negated inference sol
    -> inferred_cumulative_bounds c inference = Some bounds
    -> valid_bounds bounds c sol /\ unique_bounds bounds.
Proof.
  intros c inference sol bounds.
  intros Hneg Hbounds.
  unfold inferred_cumulative_bounds in Hbounds.
  unfold valid_bounds.
  split. 
  { intros a.
    intros Hinbounds. specialize (apply_atomics_correct (N * N) ((constraint_to_intervals c)) (map atomic_not inference) bounds Hbounds a Hinbounds) as Happly.
    destruct a as [[x [lb a_size]] [p u]] eqn:Ha.
    destruct Happly as [lb_init [size_init [Hinis [atoms_applied [Hatomsin Hatomproof]]]]].
    unfold task_in_constraint.
    unfold constraint_to_intervals in Hinis.
    rewrite in_map_iff in Hinis.
    destruct Hinis as [[[v v_process] v_usage] [Hv Hvinc]].
    destruct v.
    inversion Hv. subst x; subst lb_init; subst size_init; subst v_process; subst v_usage; clear Hv.
    assert (find_value sol (interval var) = x_start_time (name var) c sol) as Hvalue_x.
    {
      unfold x_start_time.
      destruct (find (c_var_with_x (name var)) (vs c)) as [ [[v' p'] u'] |] eqn:Hfind.
      - apply find_some in Hfind.
        destruct Hfind as [Hinvs Hcvar].
        unfold c_var_with_x in Hcvar.
        destruct (name var =? var_name v')%string eqn:Hnamev'.
        2: { discriminate Hcvar. }
        rewrite String.eqb_eq in Hnamev'.
        apply sol.(find_value_eq_name).
        rewrite <- Hnamev'.
        reflexivity.
      - exfalso. apply find_none with (x := ((interval var, p, u))) in Hfind.
        + unfold c_var_with_x in Hfind. rewrite String.eqb_neq in Hfind. simpl in Hfind. contradiction.
        + exact Hvinc.
    }
    split.
    - unfold make_activity.
      unfold activity_list. unfold activity_list_inner.
      rewrite in_map_iff.
      exists (interval var, p, u).
      split.
      + unfold activity_list_inner_f.
        
        rewrite Hvalue_x.
        reflexivity.
      + exact Hvinc.
    - unfold make_activity. simpl.
      rewrite <- Hvalue_x.
      apply atomic_proof_correct with (lb_init := (lower_bound var)) (size_init := (N.of_nat (size var))) (atoms := atoms_applied) (x := name var); try easy.
      intros atom Hinapplied.
      apply Hneg.
      apply Hatomsin.
      exact Hinapplied.
  }
  {
    unfold unique_bounds.
    intros a1 a2. intros Hin1 Hin2 Hname.
    unfold apply_atomics_to_variables in Hbounds.
  }
Qed.
(*     
    exists (interval var). simpl. reflexivity.
    - intros v' Hname_eq.
      specialize (c.(unique_vars) (interval var) v' p u Hvinc) as Hunique.
      rewrite Hname_eq in Hunique. simpl in Hunique.
      assert (name var = name var) as Hvv' by reflexivity.
      apply Hunique in Hvv'; subst v'.
      split.
      + exact Hvinc.
      + apply atomic_proof_correct with (lb_init := (lower_bound var)) (size_init := (N.of_nat (size var))) (atoms := atoms_applied) (x := name var); try easy.
        intros atom Hinapplied.
        apply Hneg.
        apply Hatomsin.
        exact Hinapplied.
Qed. *)





(* Lemma task_in_constraint_start_time_eq :
forall a c sol,
  match a with
  | (x, _, (p, u)) =>
    task_in_constraint a c sol ->
    forall (v : Var),
      var_name v = x
      -> x_start_time x c sol = sol.(find_value) v
  end.
Proof.
  intros a c sol.
  destruct a as [[x [lb a_size]] [p u]] eqn:Ha.
  intros Htask.
  intros v Hname.
  specialize sol.(find_value_eq_name) as Heq_value.
  unfold x_start_time.
  destruct (find (c_var_with_x x) (vs c)) as [[[v' v_p'] v_u'] |] eqn:Hfind.
  - apply find_some in Hfind.
    apply Heq_value.
    destruct Hfind as [_ Hvar_eq].
    unfold c_var_with_x in Hvar_eq.
    rewrite String.eqb_eq in Hvar_eq.
    rewrite Hname. rewrite <- Hvar_eq. reflexivity.
  - exfalso. apply find_none with (x := (v, p, u)) in Hfind.
    + unfold c_var_with_x in Hfind.
      rewrite String.eqb_neq in Hfind. rewrite Hname in Hfind.
      contradiction.
    + unfold task_in_constraint in Htask.
      destruct Htask as [[v' Hnamev'] Htask].
      apply Htask. exact Hname.
Qed.  *)
        
(* Lemma task_in_constraint_active_period :
  forall a c sol,
    match a with
    | (x, (lb, size), (p_time, _)) =>
      task_in_constraint a c sol ->
        exists s,
          lb <= s <= lb + Z.of_N size
            /\
          forall t, 
            s <= t < s + Z.of_N p_time
            -> is_active_at s p_time t = true
    end.
Proof.
  intros a c sol.
  destruct a as [[x [lb a_size]] [p u]] eqn:Ha.
  intros Htask.
  unfold task_in_constraint in Htask.
  destruct Htask as [s [Hbound Hactivity]].
  exists s.
  split.
  - exact Hbound.
  - intros t. intros Ht.
    unfold is_active_at.
    lia.
Qed. *)

Open Scope nat_scope.

(* Fixpoint has_n_true (n : nat) (reset : nat) (current : nat) (l : list bool) : bool :=
  match l with
  | nil => n <=? current
  | b :: l' =>
    if b
      then has_n_true n reset (S current) l'
      else has_n_true n reset reset l'
  end
.

Fixpoint max_n_true (reset : nat) (current : nat) (l : list bool) : nat :=
  match l with
  | nil => current
  | b :: l' =>
    if b
      then max_n_true reset (S current) l'
      else max current (max_n_true reset reset l') 
  end
.

Lemma max_n_true_lt_has_n_true :
  forall n reset l current,
    reset <= n
      ->
    has_n_true n reset current l = false
      ->
    max_n_true reset current l <= n \/ .
Proof.
  intros n reset l current.
  intros Hreset.
  generalize dependent current; generalize dependent l.
  induction l.
  - intros current Hhasn.
    simpl in *.
    rewrite <- not_true_iff_false in Hhasn.
    rewrite Nat.leb_le in Hhasn.
    lia.
  - simpl. destruct a.
    + intros current Hhasn.
      apply IHl. exact Hhasn.
    + intros current Hhasn.
      assert (max_n_true reset reset l <= n).
      { apply IHl. exact Hhasn. }
      assert (current <= n).
      {
        
      } *)

(* Note: we don't care if it traverses the whole list when it finds a valid one, since that is only in the error path. In general it will have to traverse the whole list to ensure there is a conflict since we expect to validate many more inferences than we reject *)
Fixpoint has_n_true_rec (n : nat) (current : nat) (l : list bool) : bool :=
  match l with
  | true :: l' => has_n_true_rec n (S current) l'
  | false :: l' => (n <=? current) || (has_n_true_rec n 0 l')
  | nil => n <=? current
  end
.

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

Open Scope N_scope.
Definition max_n_foldf (b : bool) (acc : (N * N)) : (N * N) :=
  match acc with 
  | (current, max) =>
    match b with
    | true => (current + 1, max)
    | false => (0, if (max <? current) then current else max)
    end
  end.



Definition max_n_fold (l : list bool) :=
  fold_right max_n_foldf (0, 0) l.



(* Lemma fold_ind_left {X} :
  forall (Acc:Type)(P : list X -> Acc -> Type)(f : Acc -> X -> Acc)(i : Acc)(s:list X),
  P nil i ->
  (forall x a s',
    P s' a -> P (x :: s') (f a x)) ->
  P s (fold_left f s i).
Proof.
  intros Acc P f i s Hnil Hstep.
  induction s as [| x s IH].
  - simpl. exact Hnil.
  - simpl. specialize (Hstep x (fold_left f s i)).
    apply Hstep.
    exact IH.
Qed. *)

Open Scope nat_scope.
Fixpoint run_size (l : list bool) : nat :=
  match l with
  | nil => O
  | false :: l' => O
  | true :: l' => S (run_size l')
  end.

(* Fixpoint run_size_rest (l : list bool) : (nat * list bool) :=
  match l with
  | nil => (O, nil)
  | false :: l' => O
  | true :: l' => S (run_size l')
  end. *)

Definition run_at (n : nat) (l : list bool) : nat :=
  run_size (skipn n l). 

Fixpoint max_n_true (current : nat) (l : list bool) : nat :=
  match l with
  | nil => current
  | b :: l' =>
    if b
      then max_n_true (S current) l'
      else max current (max_n_true 0 l') 
  end
.

Lemma has_0_true :
  forall l start,
    has_n_true_rec 0 start l = true.
Proof.
  induction l.
  - intros. simpl. reflexivity.
  - intros start. simpl.
    destruct a.
    + apply IHl.
    + reflexivity.
Qed.

(* Fixpoint has_n_true (n : nat) (current : nat) (l : list bool) : bool :=
  match l with
  | nil => n <=? current
  | b :: l' =>
    if b
      then has_n_true n (S current) l'
      else has_n_true n 0 l'
  end
. *)

(* Lemma max_n_true_lt_has_n_true :
  forall l n current,
    has_n_true n current l = false
      ->
    run_size l <=  *)

Lemma max_n_true_lt_has_n_true :
  forall l n current,
    has_n_true_rec n current l = false
      ->
    max_n_true current l < n.
Proof.
  induction l.
  - intros n current Hhasn.
    simpl in *.
    rewrite <- not_true_iff_false in Hhasn. rewrite Nat.leb_le in Hhasn.
    lia.
  - simpl. destruct a.
    + intros n current Hhasn.
      apply IHl.
      exact Hhasn.
      (* intros n Hhasn.
      specialize (IHl (pred n)). *)
      (* assert (has_n_true (pred n) 0 l = false).
      {
        (* Does not hold in general! *)
      } *)
      (* specialize (IHl n (S current)).
      apply IHl in Hhasn.
      destruct 
      apply IHl. exact Hhasn. *)
    + intros n current Hhasn.
      rewrite orb_false_iff in Hhasn.
      destruct Hhasn as [Hncurrent Hhasn].
      rewrite <- not_true_iff_false in Hncurrent.
      rewrite Nat.leb_le in Hncurrent.
      assert (max_n_true 0 l < n).
      { apply IHl. exact Hhasn. }
      lia.
Qed.

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

Lemma run_le_left : 
  forall l n,
    run_at n l <= length l - n.
Proof.
  intros l n.
  unfold run_at.
  specialize (length_skipn n l) as Hskiplen.
  rewrite <- Hskiplen.
  apply run_size_le_length.
Qed.

Lemma max_run_lt_start :
  forall l s1 s2,
  s1 <= s2
    ->
  max_n_true s1 l <= max_n_true s2 l.
Proof.
  induction l.
  - intros s1 s2 H. simpl. exact H.
  - intros s1 s2 H. simpl. destruct a.
    + apply IHl. lia.
    + clear IHl. lia.
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

(* Lemma skip_lt_max_runs :
  forall l k,
    max_runs (skipn k l) <= max_runs l.
Proof.
  induction l; induction k.
  - rewrite skipn_nil. simpl. reflexivity.
  - rewrite skipn_nil. simpl. reflexivity.
  - rewrite skipn_O. reflexivity.
  - rewrite skipn_cons.
    simpl.
    assert (max_runs (skipn k l) <= max_runs l) by (apply IHl).
    destruct a.
    + lia.
    + lia.
Qed.  *)

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
Lemma run_at_seq_no_bound :
  forall s e n i l (f : Z -> bool),
    (n >= 1)%nat
      ->
    (n <= length l)%nat
      ->
    (i <= length l - n)%nat
      ->
    ZRange.is_range s e l
      ->
    (run_at i (map f l) < n)%nat
      ->
    (exists k, 
      e - Z.of_nat i - Z.of_nat n + 1 <= k <= e - Z.of_nat i
        /\
      f k = false
    ).
Proof.
  intros s e n i l f.
  intros Hn1 Hnlen Hi Hrange Hrun.
  assert (n <= length (skipn i l))%nat.
  { 
    rewrite length_skipn.
    lia.
  }
  rewrite length_skipn in H.
  rewrite ZRange.is_range_length with (s := s) (e := e) in H; try assumption.
  rewrite <- (nth_false_run_lt (skipn i (map f l)) n) in Hrun; try assumption.
  destruct Hrun as [k [Hkn Hkfalse]].
  exists (e - Z.of_nat (i + k)).
  split.
  - lia.
  - rewrite nth_skipn in Hkfalse.
    rewrite ZRange.range_f_l with (s := s) (l := l) (d := false); try assumption.
    clear Hkfalse.
    destruct Hrange as [Hse _].
    lia.
Qed.

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
    | nil => 
      match activity with
      | (_, _, (_, usage)) =>  
        profile_usage + usage <=? capacity
      end
    | _ => true
    end
  end
.

Lemma can_be_active_at_t_false :
  forall t profile_usage c x lb size p u,
    can_be_active_at_t c (x, (lb, size), (p, u)) (t, profile_usage) = false
      ->
    activity_bounds_is_active t (x, (lb, size), (p, u)) = nil
      /\
    profile_usage + u > c.
Proof.
  intros t p_u c x lb size p u.
  intros Hfalse.
  unfold can_be_active_at_t in Hfalse.
  destruct (activity_bounds_is_active t (x, (lb, size), (p, u))).
  - split.
    + reflexivity.
    + rewrite <- not_true_iff_false in Hfalse.
      rewrite N.leb_le in Hfalse.
      lia.
  - discriminate Hfalse.
Qed.

Open Scope Z_scope.

Definition make_active_list (capacity : N) (profile : list (Z * N)) (activity : string * zn_interval * (N * N)) : list bool :=
  map (can_be_active_at_t capacity activity) profile.

Definition cannot_schedule_activity_w_profile (capacity : N) (profile : list (Z * N)) (activity : string * zn_interval * (N * N)) : bool :=
  match activity with
  | (_, _, (duration, _)) =>
    negb (has_n_true (N.to_nat duration) (make_active_list capacity profile activity))
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
  unfold cumulative_checker in Hchecked.
  destruct (inferred_cumulative_bounds constr fact) as [bounds |] eqn:Hbounds.
  2: discriminate Hchecked.
  specialize (overload_props constr.(capacity) (ZRange.build_range constr.(horizon_start) constr.(horizon_end)) bounds) as Hoverload.
  destruct (find_overloaded_t_with_mandatory (capacity constr)
  (ZRange.build_range (horizon_start constr)
  (horizon_end constr)) bounds) as [[[t usages_t] _] |].
  {
    enough (cumulative_decide constr sol = false).
    {
    rewrite H in Hconstr. apply Hconstr.
    }
    apply exceeds_at_t_dec_false.
    exists t.
    destruct Hoverload as [Hsum Hinhorz].
    split.
    - specialize (ZRange.build_range_correct (horizon_start constr) (horizon_end constr) (horizon_consistent constr)) as Hrange.
      unfold ZRange.is_range in Hrange.
      destruct Hrange as [_ [Hrange _]].
      rewrite Hrange.
      exact Hinhorz.
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
            apply Hneg.
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
    { 
      clear Hoverload.
      apply existsb_exists in Hchecked.
      destruct Hchecked as [a [Hbound Hcannot_sched]].
      
      (* specialize (apply_atomics_correct (N * N) ((constraint_to_intervals constr)) (map atomic_not fact) bounds Hbounds a Hbound) as Happly.
      destruct a as [[x [lb size]] [p u]] eqn:Ha.
      destruct Happly as [lb_init [size_init [Hinis [atoms_applied [Hatomsin Hatomproof]]]]]. *)

      apply inferred_cumulative_bounds_valid with (sol := sol) in Hbounds.
      2: apply Hneg.
      clear Hneg.
      apply Hbounds in Hbound.
      pose proof Hbound as Htask.
      unfold task_in_constraint in Hbound.
      destruct a as [[x [lb size]] [p u]] eqn:Ha.
      destruct Hbound as [Hstart Hinactivity].
      rewrite <- Ha in *.
      remember (make_activity a constr sol) as act.
      
 
(* 
      clear Hatomsin; clear Hatomproof; clear atoms_applied; clear Hbounds; clear Hneg. *)

      unfold cannot_schedule_activity_w_profile in Hcannot_sched.
      rewrite Ha in Hcannot_sched.
      rewrite negb_true_iff in Hcannot_sched.
      specialize has_n_true_all_runs as Hruns.
      remember (ZRange.build_range (horizon_start constr) (horizon_end constr)) as times.
      specialize (resource_profile_correct (capacity constr) bounds times) as Hr_profile_correct.

      remember (capacity constr) as c.
      remember (resource_profile c bounds times) as r_profile.
      rewrite <- Ha in Hcannot_sched.
      specialize (Hruns (N.to_nat p) (make_active_list c r_profile a) Hcannot_sched); clear Hcannot_sched.
      specialize (resource_profile_as_range times (horizon_start constr) (horizon_end constr) c bounds) as Hr_profile_range.
      specialize (ZRange.build_range_correct (horizon_start constr) (horizon_end constr) (horizon_consistent constr)) as Hbuild_range.
      rewrite Heqtimes in Hr_profile_range.
      specialize (Hr_profile_range Hbuild_range); clear Hbuild_range.
      rewrite <- Heqtimes in Hr_profile_range.
      rewrite <- Heqr_profile in Hr_profile_range.     

      clear Heqtimes; clear Heqr_profile.

      unfold make_active_list in Hruns.

      remember (horizon_end constr) as h_end.
      remember (horizon_start constr) as h_start.

      remember (Z.to_nat (h_end - ((start act) + Z.of_N p) + 1)) as i.

      assert ((start act) + Z.of_N p <= h_end).
      { admit. }

      apply (run_at_seq_fk_false r_profile) with (fb := (can_be_active_at_t c a)) (n := (N.to_nat p)) (i := i) in Hr_profile_range.

      - clear Hruns.
        destruct Hr_profile_range as [[t_false p_usage] [Ht [Hprofile Hfalse]]].

        rewrite Ha in Hfalse.
        apply can_be_active_at_t_false in Hfalse.
        destruct Hfalse as [Hnotact Husage].
        assert (~ In (x, u) (activities_bounds_active_at t_false bounds)).
        { 
          unfold activities_bounds_active_at. rewrite nodup_In.
          rewrite in_flat_map.
          unfold not.
          intros [a_man [Ha_man_bounds Hman]].
          
          apply Hbounds in Ha_man_bounds.

          destruct a_man as [[x' [lb' size']] [p' u']].
          unfold activity_bounds_is_active in Hman.
          destruct (interval_to_bounds (lb', size')) as [lb_b ub'] eqn:Hbound_lb.
          destruct (mandatory_active lb_b ub' t_false p') eqn:His_man.
          2: { destruct Hman. }
          simpl in Hman. destruct Hman as [Hxu |]; try contradiction.
          inversion Hxu; subst x'; subst u'; clear Hxu.
          unfold interval_to_bounds in Hbound_lb.
          inversion Hbound_lb; subst lb_b; subst ub'; clear Hbound_lb.

          apply two_tasks_in_constraint_x_eq with (a1 := a) in Ha_man_bounds.
          rewrite Ha in Ha_man_bounds.
          assert (x = x) as Ha1a2 by reflexivity.
          apply Ha_man_bounds in Ha1a2; clear Ha_man_bounds.




          destruct (activity_bounds_is_active t_false a_man) eqn:H_is_active.
          - destruct Hman.
          - 
            assert (p0 = (x, u)).
            {
              destruct 
            }
        }

        apply Hr_profile_correct in Hprofile; clear Hr_profile_correct.
        destruct Hprofile as [_ Hboundssum].

        apply bounds_sum_implies_usage with (constr := constr) (sol := sol) in Hboundssum.
        2: apply Hbounds.

        simpl in Ht.
        assert (start <= t_false < start + Z.of_N p) as Hactive by lia.
        clear Heqi; clear Ht.

        assert (In act (activities_at_t (activity_list constr sol) t_false)) as Hact_active.
        {
          unfold activities_at_t. rewrite filter_In.
          split.
          - exact Hinactivity.
          - unfold is_active_at. rewrite Heqact. simpl.
            rewrite andb_true_iff.
            rewrite Z.leb_le. rewrite Z.ltb_lt. exact Hactive.  
        }



        



    }
  

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


