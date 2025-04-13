
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
Require Import Lia.
Require Import Checker.Atomic.
Require Import Checker.Variable.
Require Checker.Utility.
Require Import Checker.DomainAllVar.
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

Open Scope Z_scope.


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

Definition mandatory_active (lb : Z) (ub : Z) (t : Z) (p_time : N) :=
  (ub <=? t) && (t <? (lb + (Z.of_N p_time))).

Definition constraint_to_param_map (c : CumulativeConstraint) : string -> (N * N) :=
  let params := map (fun elt =>
    match elt with
    | (v, p, u) =>
      (var_name v, (p, u))
    end) c.(vs) in
  param_map params (N0, N0).

Definition constraint_to_vars (c : CumulativeConstraint) : list Var :=
  map (fun elt =>
    match elt with
    | (v, _, _) => v
    end
  ) c.(vs).

Definition domain_to_bound (param_map : string -> (N * N)) (dom : Domain) :=
  match dom.(d_lb) with
  | Some lb =>
    match dom.(d_ub) with
    | Some ub =>
      let size := Z.to_N (ub - lb) in
        Some (dom.(d_name), (lb, size), (param_map dom.(d_name)))
    | _ => None
    end
  | _ => None
  end.

Definition domains_to_bounds (doms : list Domain) (param_map : string -> (N * N)) : list (string * zn_interval * (N * N)) :=
  flat_map_option (domain_to_bound param_map) doms.

Definition inferred_cumulative_bounds (c : CumulativeConstraint) (inference : list Atomic) :=
  let vars := constraint_to_vars c in
  let domains := vars_with_atomics_to_domains (map atomic_not inference) vars in
  domains_to_bounds domains (constraint_to_param_map c).

Definition inference_negated (inference : list Atomic) (sol : Assignment) :=
  forall atomic, In atomic (map atomic_not inference) ->
    Is_true (test_atomic_assignment atomic sol).

Definition interval_to_bounds (i : zn_interval) : (Z * Z)%type :=
  let (lb, size) := i in
    (lb, lb + (Z.of_N size)).

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
  flat_map (activity_bounds_is_active t) activities.

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

Definition value_from_x (x : string) (vs : list Var) (sol : Assignment) :=
  match (find (c_var_with_x x) vs) with
  | None => Z0
  | Some v => sol.(find_value) v
  end.

Definition make_activity (a : string * zn_interval * (N * N)) (vs : list Var) (sol : Assignment) :=
  match a with
  | (x, (lb, size), (p, u)) =>
      mkAct x (value_from_x x vs sol) p u
  end.

Definition in_horizon (a : Activity) (c : CumulativeConstraint) :=
  c.(horizon_start) <= a.(start) /\ a.(start) + Z.of_N a.(p_time) <= c.(horizon_end).

Definition task_in_constraint (a : string * zn_interval * (N * N)) (c : CumulativeConstraint) (sol : Assignment) :=
  let act := (make_activity a (constraint_to_vars c) sol) in
    In act (activity_list c sol)
      /\
    in_horizon act c
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
    (1 <= p <= horizon_length c)%N.
Proof.
  intros x lb size p u c sol.
  intros Htask.
  destruct Htask as [Hin _].
  unfold activity_list in Hin.
  unfold activity_list_inner in Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [[[v p'] u'] H].
  destruct H as [Hact Hinvs].
  specialize c.(valid_p_times) as Hprocess.
  unfold processing_constr in Hprocess.
  apply Hprocess with (v := v) (u := u).
  unfold activity_list_inner_f in Hact.
  unfold make_activity in Hact.
  destruct v as [v].
  inversion Hact; subst p'; subst u'.
  exact Hinvs.
Qed.
  

Open Scope N_scope.

Definition bound_name {U} (bound : string * zn_interval * U) :=
  match bound with
  | (x, _, _) => x
  end.


Definition unique_bounds {U} (bounds : list (string * zn_interval * U)) :=
  NoDup bounds
    /\
  forall a1 a2,
    In a1 bounds -> In a2 bounds
    -> bound_name a1 = bound_name a2
    -> a1 = a2. 

Lemma a_u_dec (U : Type) (u_dec : forall x y : U, {x = y}+{x <> y}) :
  forall x y : string * zn_interval * U, {x = y}+{x <> y}.
Proof.
  repeat decide equality.
Qed.

Lemma unique_bounds_cons (U : Type) :
  forall (a : string * zn_interval * U) bounds,
    unique_bounds (a :: bounds)
      ->
    forall a',
      In a' bounds
        ->
      bound_name a <> bound_name a'.
Proof.
  intros a bounds.
  intros Hunique.
  intros a'. intros Hin.
  unfold not. intros Hname.
  apply Hunique in Hname.
  - subst a'.
    unfold unique_bounds in Hunique.
    destruct Hunique as [Hnodup _].
    rewrite NoDup_cons_iff in Hnodup.
    destruct Hnodup as [Hnotinbounds _].
    contradiction.
  - left. reflexivity.
  - right. exact Hin.
Qed.

Lemma unique_bounds_less (U : Type) :
  forall (a : string * zn_interval * U) bounds,
    unique_bounds (a :: bounds)
      ->
    unique_bounds bounds.
Proof.
  intros a bounds.
  intros Hunique.
  unfold unique_bounds in Hunique.
  unfold unique_bounds.
  destruct Hunique as [Hnodup Hunique].
  split.
  - rewrite NoDup_cons_iff in Hnodup. apply Hnodup.
  - intros a1 a2 Hin1 Hin2 Hname.
    apply Hunique.
    + right. exact Hin1.
    + right. exact Hin2.
    + exact Hname.
Qed.



Definition valid_bounds (bounds : list (string * zn_interval * (N * N))) (c : CumulativeConstraint) (sol : Assignment) :=
  forall a, In a bounds -> task_in_constraint a c sol.

Lemma activity_bounds_nodup :
forall t bounds,
  unique_bounds bounds
    ->
  NoDup (activities_bounds_active_at t bounds).
Proof.
  intros t. induction bounds.
  - intros Hnil. simpl. apply NoDup_nil.
  - intros Hunique.
    apply unique_bounds_less in Hunique as H.
    apply IHbounds in H; clear IHbounds.
    simpl.
    destruct a as [[x [lb size]] [p u]].
    apply NoDup_app.
    + unfold activity_bounds_is_active.
      destruct (interval_to_bounds (lb, size)) as [lb' ub].
      destruct (mandatory_active lb' ub t p).
      * apply NoDup_cons; try easy. apply NoDup_nil.
      * apply NoDup_nil.
    + apply H.
    + intros a Hin.
      intros Hinbounds.
      unfold activities_bounds_active_at in Hinbounds.
      rewrite in_flat_map in Hinbounds.
      destruct Hinbounds as [a' [Hina' Ha]].
      destruct a as [x' u'].
      unfold activity_bounds_is_active in Hin.
      destruct (interval_to_bounds (lb, size)) as [lb_p ub].
      destruct (mandatory_active lb_p ub t p); try easy.
      destruct Hin as [Hxu|]; try easy; inversion Hxu; subst x'; subst u'; clear Hxu.
      destruct a' as [[x' [lb' size']] [p' u']].
      unfold activity_bounds_is_active in Ha.
      destruct (interval_to_bounds (lb', size')) as [lb_p' ub'].
      destruct (mandatory_active lb_p' ub' t p'); try easy.
      destruct Ha as [Hxu|]; try easy; inversion Hxu; subst x'; subst u; clear Hxu.
      apply unique_bounds_cons with (a := (x, (lb, size), (p, u'))) in Hina'.
      * simpl in Hina'. contradiction.
      * exact Hunique.
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
(* Lemma constraint_to_intervals_unique :
  forall c,
    unique_bounds (constraint_to_intervals c).
Proof.
  intros c.
  unfold unique_bounds.
  split.
  - unfold constraint_to_intervals. apply Injective_map_NoDup.
    + unfold Injective. intros [[v1 p1] u1]. intros [[v2 p2] u2].
      destruct v1 as [v1]. destruct v2 as [v2].
      intros H.
      inversion H.
      subst p2; subst u2.
      destruct v1. destruct v2. simpl in *.
      assert (size = size0) by lia.
      subst name0; subst lower_bound0; subst size0.
      reflexivity.
    + apply c.(vs_nodup). 
  - intros a1 a2.
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
    + inversion Hv1v2. reflexivity.
    + exact Hin2.
    + simpl. rewrite H0. rewrite H1. reflexivity.
Qed. *)

Lemma value_from_x_is_v_sol :
  forall v vs x sol,
    In v vs
      ->
    var_name v = x
      ->
    value_from_x x vs sol = sol.(find_value) v.
Proof.
  intros v vs x sol.
  intros Hin Hname.
  unfold value_from_x.
  destruct (find (c_var_with_x x) vs) as [v' |] eqn:Hfind.
  - apply find_some in Hfind.
    destruct Hfind as (_ & Hnamev').
    unfold c_var_with_x in Hnamev'.
    apply sol.(find_value_eq_name).
    rewrite Hname.
    rewrite String.eqb_eq in Hnamev'. rewrite Hnamev'.
    reflexivity.
  - apply find_none with (x := v) in Hfind.
    + exfalso. unfold c_var_with_x in Hfind.
      rewrite String.eqb_neq in Hfind.
      rewrite Hname in Hfind. apply Hfind. reflexivity.
    + exact Hin.
Qed.

Open Scope Z_scope.
Lemma inferred_cumulative_bounds_valid :
  forall (c : CumulativeConstraint) inference sol,
    let bounds := inferred_cumulative_bounds c inference in 
    inference_negated inference sol
    -> valid_bounds bounds c sol /\ unique_bounds bounds.
Proof.
  intros c inference sol bounds.
  intros Hneg.
  unfold inferred_cumulative_bounds in bounds.
  unfold valid_bounds.
  split. 
  { intros a.
    intros Hinbounds. 
    unfold bounds in Hinbounds; clear bounds.
    unfold domains_to_bounds in Hinbounds.
    rewrite in_flat_map_option in Hinbounds.
    destruct Hinbounds as [dom [Hdomin Hdomparam]].
    unfold task_in_constraint.

    assert (exists v : Var, 
      In v (constraint_to_vars c) 
        /\
      var_name v = (dom.(d_name))
        /\
      domain_holds dom sol
    ) by (admit); clear Hdomin; clear Hneg.

    destruct H as (v & Hvinc & Hvname & Hdomholds).
    rename Hvname into Hvdom.
    pose proof Hvdom as Hvname.
    apply Hdomholds in Hvdom as (Hholds & _).
    unfold DomainAll.current_bound_holds in Hholds.
    unfold DomainAll.option_bound in Hholds.

    unfold domain_to_bound in Hdomparam.
    destruct (d_lb dom) as [dom_lb|]; destruct (d_ub dom) as [dom_ub|]; try discriminate Hdomparam.
    inversion Hdomparam as [Hdomparams]; clear Hdomparam.
    remember (constraint_to_param_map c (d_name dom)) as dom_params; destruct dom_params as [dom_p dom_u].
    remember (Z.to_N (dom_ub - dom_lb)) as dom_size.

    apply value_from_x_is_v_sol with (sol := sol) (x := d_name dom) in Hvinc as Hvalue_is_var.

    split; [|split].
    - unfold make_activity.
      unfold activity_list. unfold activity_list_inner.
      rewrite in_map_iff.
      exists (v, dom_p, dom_u).
      split.
      + unfold activity_list_inner_f.
        destruct v.
        rewrite Hvalue_is_var.
        rewrite <- Hvname.
        simpl. reflexivity.
        
      + clear -Heqdom_params.
        unfold constraint_to_param_map in Heqdom_params.
        apply param_map_in in Heqdom_params.
        * rewrite in_map_iff in Heqdom_params.
          destruct Heqdom_params as (((v' & p') & u') & Heqs & Hin).
          inversion Heqs; subst; clear Heqs.
          assert (v = v').
          {
            apply c.()  
          }
        

    - admit.
    - unfold domain_holds in Hdomholds.
      unfold make_activity. simpl. rewrite value_from_x_is_v_sol with (v := v).
      + lia.
      + exact Hvinc.
      + exact Hvname.

    {

    }
    
    
    specialize (apply_atomics_correct (N * N) ((constraint_to_intervals c)) (map atomic_not inference) bounds Hbounds a Hinbounds) as Happly.
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
    split; [| split].
    - unfold make_activity.
      unfold activity_list. unfold activity_list_inner.
      rewrite in_map_iff.
      exists (interval var, p, u).
      split.
      + unfold activity_list_inner_f.
        
        rewrite Hvalue_x.
        reflexivity.
      + exact Hvinc.
    - unfold in_horizon. unfold make_activity. simpl.
      specialize c.(valid_horizon) as Hhor.
      unfold horizon_all in Hhor.
      specialize (Hhor (interval var) p u Hvinc).
      simpl in Hhor.
      rewrite <- Hvalue_x.
      specialize (sol.(consistency_proof) (interval var)) as Hconsistent.
      apply is_in_implies_lower_bound in Hconsistent as Hlow.
      apply is_in_implies_upper_bound in Hconsistent as Hup.
      unfold var_upper_bound in Hup.
      unfold var_lower_bound in Hlow.
      lia.
    - unfold make_activity. simpl.
      rewrite <- Hvalue_x.
      apply atomic_proof_correct with (lb_init := (lower_bound var)) (size_init := (N.of_nat (size var))) (atoms := atoms_applied) (x := name var); try easy.
      intros atom Hinapplied.
      apply Hneg.
      apply Hatomsin.
      exact Hinapplied.
  }
  {
    apply apply_atomics_unique with (atoms := (map atomic_not inference)) (is := (constraint_to_intervals c)).
    - repeat decide equality.
    - apply constraint_to_intervals_unique.
    - exact Hbounds.
  }
Qed.


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
    | nil => 
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
    (activity_bounds_is_active t (x, (lb, size), (p, u)) = nil)
      /\
    ((profile_usage + u > c) \/ (t < lb \/ t >= lb + Z.of_N size + Z.of_N p)%Z).
Proof.
  intros t p_u c x lb size p u.
  intros Hfalse.
  unfold can_be_active_at_t in Hfalse.
  destruct (activity_bounds_is_active t (x, (lb, size), (p, u))).
  - split.
    + reflexivity.
    + repeat rewrite andb_false_iff in Hfalse.
      repeat rewrite <- not_true_iff_false in Hfalse.
      repeat rewrite Z.leb_le in Hfalse.
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

Definition cumulative_checker (inference : list Atomic) (constraint : CumulativeConstraint) : bool :=
  let times := (ZRange.build_range constraint.(horizon_start) constraint.(horizon_end)) in
  match inferred_cumulative_bounds constraint inference with
  | None => false
  | Some bounds => 
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
  2: { discriminate Hchecked. }

  assert (valid_bounds bounds constr sol /\ unique_bounds bounds).
  { 
    apply inferred_cumulative_bounds_valid with (inference := fact).
    - exact Hneg.
    - exact Hbounds.
  }
  destruct H as [Hvalid Hunique]; clear Hbounds; clear Hneg.

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
      remember (make_activity a constr sol) as act.
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
        subst p; subst h_start; subst h_end;
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
          rewrite in_flat_map.
          unfold not.
          intros [a_man [Ha_man_bounds Hman]].
           
          pose proof Ha_man_bounds as Ha_man_inbounds.
          
          apply Hvalid in Ha_man_bounds.

          destruct a_man as [[x' [lb' size']] [p' u']].
          unfold activity_bounds_is_active in Hman.
          destruct (interval_to_bounds (lb', size')) as [lb_b ub'] eqn:Hbound_lb.
          destruct (mandatory_active lb_b ub' t_false p') eqn:His_man.
          2: { destruct Hman. }
          simpl in Hman. destruct Hman as [Hxu |]; try contradiction.
          inversion Hxu; subst x'; subst u'; clear Hxu.

          destruct Hunique as [_ Hunique].
          apply Hunique with (a1 := a) in Ha_man_inbounds.
          - rewrite Ha in Ha_man_inbounds. inversion Ha_man_inbounds.
            subst lb'; subst size'; subst p'; clear Ha_man_inbounds.
            unfold activity_bounds_is_active in Hman_nil.
            rewrite Hbound_lb in Hman_nil.
            rewrite His_man in Hman_nil.
            discriminate Hman_nil. 
          - exact Hinbound.
          - rewrite Heqact. rewrite Ha. unfold make_activity. simpl. reflexivity.
        }
        assert (usage act = u) as Hu.
        {
          rewrite Heqact. rewrite Ha. unfold make_activity. simpl. reflexivity. 
        }
        rewrite Hu. lia.
      + enough (p >= 1)%N by lia.
        rewrite Ha in Htask.
        apply task_valid_processing in Htask.
        lia.
      + enough (p <= horizon_length constr)%N as Hhor_len.
        { unfold horizon_length in Hhor_len.
        lia. }
        rewrite Ha in Htask.
        apply task_valid_processing in Htask.
        lia.
      + rewrite Ha in Htask.
        apply task_valid_processing in Htask.
        subst h_end; subst h_start.
        rewrite Hprofilerange.
        rewrite Heqi.
        lia.
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
Qed.

Lemma is_true_not_false :
  forall b, (b = false -> False) -> Is_true b.
Proof.
  intros. destruct b.
  - reflexivity.
  - simpl. apply H. reflexivity.
Qed.

Definition Inference := list Atomic.

Definition inference_valid (I : Inference) (C : CumulativeConstraint) :=
  forall (theta : Assignment),
    cumulative_decide C theta = true
      ->
    satisfies_nogood I theta = true.

Lemma cumulative_checker_sound :
  forall (I : Inference) (C : CumulativeConstraint),
    cumulative_checker I C = true
      ->
    inference_valid I C.
Proof.
  intros I C.
  intros Hcheck. intros theta Hsol.
  destruct (satisfies_nogood I theta) eqn:Hsat.
  - reflexivity.
  - exfalso. apply checker_not_cumulative with (fact := I) (sol := theta) (constr := C); try apply Is_true_eq_left; try assumption.
  apply neg_atomic. exact Hsat.
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

Definition mkAtm (x : string) (atm_comparator : AtomicComparator) (atm_value : Z) :=
  {|
    var := interval {| name := x; lower_bound := Z0; size := 50 |} ; 
    comparator := atm_comparator ; 
    value := atm_value
  |}.

Definition mkInf (lhs : list Atomic) (rhs : option Atomic) :=
  let lhs_neg := (map atomic_not lhs) in
    lhs_neg ++
    match rhs with
    | None => nil
    | Some rhs => rhs :: nil
    end.

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
    mkInf (
        mkAtm "x" greater_equal 0 ::
        mkAtm "x" less_equal 2 ::
        mkAtm "y" greater_equal 1 ::
        mkAtm "y" less_equal 3 ::
        nil
      ) None in
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
    mkInf (
        mkAtm "x" greater_equal 0 ::
        mkAtm "x" less_equal 2 ::
        mkAtm "y" greater_equal 2 ::
        nil
      ) (Some (mkAtm "y" greater_equal 3)) in
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
    mkInf (
        mkAtm "x" greater_equal 0 ::
        mkAtm "x" less_equal 2 ::
        mkAtm "y" greater_equal 2 ::
        nil
      ) (Some (mkAtm "y" greater_equal 4)) in
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
    mkInf (
        mkAtm "x" greater_equal 0 ::
        mkAtm "x" less_equal 2 ::
        mkAtm "y" greater_equal 1 ::
        nil
      ) (Some (mkAtm "y" greater_equal 4)) in
  cumulative_checker fact constr.

Compute 
  let cap := 1%N in
  let constr := build_cumulative 
    (
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 2%N; def_u := 1%N; |} ::
      nil
    ) 
    cap Z0 10%N in
  let fact := 
    mkInf (
        mkAtm "x" greater_equal 0 ::
        mkAtm "x" less_equal 2 ::
        mkAtm "y" greater_equal 0 ::
        nil
      ) (Some (mkAtm "y" greater_equal 4)) in
  let is := (constraint_to_intervals constr) in
  let error_a := ("ERROR"%string, (0, 16%N), (4%N, 1%N)) in
  let ax := hd error_a is in
  let ay := hd error_a (tl is) in
  let atoms := (map atomic_not fact) in
  let tms := (ZRange.build_range constr.(horizon_start) constr.(horizon_end)) in
  let inferr := inferred_cumulative_bounds constr fact in
    match inferr with
    | None => None
    | Some inferr => 
        let appl_y := hd error_a (tl inferr) in
        match (resource_profile cap inferr tms) with
        | profile_usages u => Some (make_active_list cap u appl_y)
        | profile_conflict c => None
        end
    end
  . 