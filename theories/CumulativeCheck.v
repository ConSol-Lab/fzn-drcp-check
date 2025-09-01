Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import String.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Arith.PeanoNat.
Require Import Bool.
Require Import Lia.

Require Checker.CumulativeUtil.
Require Checker.Spec.
Import Spec.ConstraintDefinitions.
Import Spec.ProofFacts.
Import CumulativeUtil.RunOfN.
Import CumulativeUtil.NSum.
Import CumulativeUtil.BuildCumul.

Require Checker.Utility.
Import Utility.Maps.
Import Utility.ListEx.
Import Utility.Sets.
Import Utility.ZRange.
Import Utility.SubList.
Import Utility ZMaxMinList.
Require Import Checker.Domain.
Require Import Checker.DomainVar.
Require Import Checker.Zext.
Require Import Checker.Deduction.
Import Datatypes.

Open Scope Z_scope.

Record ActivityBound := mkBound {
  b_lb : Z;
  b_ub : Z;
  b_p_time : N;
  b_usage : N;
}.

Record ScheduledActivity := schedAct {
  sched_start : Z;
  sched_duration : N;
  sched_usage : N;
}.

Definition lb_ub_from_dom (dom : Domain) : option (Z * Z) :=
  match dom.(d_lb), dom.(d_ub) with
  | zz lb, zz ub => Some (lb, ub)
  | _, _ => None
  end.

Definition lb_ub_from_act_dom (activity : Activity) (domains : smap.t Domain) : option (Z * Z) :=
  match (activity_start activity) with
  | const value => Some (value, value)    
  | var_name x =>
    match smap.find x domains with
    | None => None
    | Some dom => lb_ub_from_dom dom 
    end
  end.

Definition act_dom_to_bound (dom : Domain) (activity : Activity) : option ActivityBound :=
  match lb_ub_from_dom dom with
  | Some (lb, ub) => Some (mkBound lb ub (activity_duration activity) (activity_usage activity))
  | None => None
  end.

Definition act_doms_to_bound (domains : smap.t Domain) (activity : Activity) : option ActivityBound :=
  match lb_ub_from_act_dom activity domains with
  | Some (lb, ub) => Some (mkBound lb ub (activity_duration activity) (activity_usage activity))
  | None => None
  end.

Definition activity_match (x : string) (activity : Activity) : bool :=
  match (activity_start activity) with
  | const value => false
  | var_name x' => (x =? x')%string
  end.

Definition inferred_cumulative_bounds (constr : CumulativeConstraint) (fact : ProofFact) : (list ActivityBound * option ActivityBound) :=
  match infer_domains fact with
  | None => (nil, None)
  | Some (domains, prop_var) =>
    let bounds := flat_map_option (act_doms_to_bound domains) constr.(activities) in
    match prop_var with
    | None => (bounds, None) 
    (* The below could probably be made more efficient. *)
    | Some prop_var =>
      match find (activity_match prop_var) constr.(activities) with
      | None => (bounds, None)
      | Some prop_act =>
        match smap.find prop_var domains with
        | None => (bounds, None)
        | Some prop_dom => (bounds, act_dom_to_bound prop_dom prop_act)
        end
      end
    end
  end.

Inductive valid_bounds (sol : string -> Z) : list Activity -> list ActivityBound -> Prop :=
  | valid_bounds_nil : valid_bounds sol nil nil
  | valid_bounds_bound (act : Activity) (acts : list Activity) (bound : ActivityBound) (bounds: list ActivityBound) 
    (Hstart : bound.(b_lb) <= evaluate act.(activity_start) sol <= bound.(b_ub)) 
    (Husage : bound.(b_usage) = act.(activity_usage)) (Hduration : bound.(b_p_time) = act.(activity_duration)) 
    (H : valid_bounds sol acts bounds) 
      : valid_bounds sol (act :: acts) (bound :: bounds)
  | valid_bounds_nobound (act : Activity) (acts : list Activity) (bounds : list ActivityBound) (H : valid_bounds sol acts bounds) : valid_bounds sol (act :: acts) bounds
  .

Lemma bound_eq_dec :
  forall x y : ActivityBound, {x = y}+{x <> y}.
Proof.
  intros x y. repeat decide equality.
Qed.

Lemma valid_bounds_act_left sol :
  forall acts bound bounds,
    valid_bounds sol acts (bound :: bounds)
      ->
    exists acts_l acts_r act,
      acts = acts_l ++ act :: acts_r
        /\
      valid_bounds sol acts_r bounds
        /\
      bound.(b_lb) <= evaluate act.(activity_start) sol <= bound.(b_ub) /\
      bound.(b_usage) = act.(activity_usage) /\
      bound.(b_p_time) = act.(activity_duration).
Proof.
  induction acts as [|act acts IH].
  { intros bound bounds H.
    inversion H. }
  intros bound bounds Hvalid.
  inversion Hvalid.
  - subst act0 acts0 bound0 bounds0.
    rename H0 into Hvalid_base.
    exists nil. exists acts. exists act.
    now repeat split.
  - subst act0 acts0. rename bounds0 into bounds'.
    rename H0 into Hbounds'. rename H2 into Hvalid'.
    specialize (IH bound bounds Hvalid').
    destruct IH as (acts_l & acts_r & act' & IHacts & IHvalid & IH).
    exists (act :: acts_l). exists acts_r. exists act'.
    repeat split; try easy.
    rewrite IHacts. reflexivity.
Qed.

Lemma valid_bounds_app_acts sol :
  forall acts' acts bounds,
  valid_bounds sol acts bounds
    ->
  valid_bounds sol (acts' ++ acts) bounds.
Proof.
  induction acts' as [|act acts' IH]; try easy.
  intros acts bounds Hvalid.
  simpl. apply valid_bounds_nobound.
  apply IH. exact Hvalid.
Qed.

  
Lemma valid_bound_matching_activity : 
  forall sol acts bounds bounds_l bounds_r bound,
  valid_bounds sol acts bounds ->
  bounds = bounds_l ++ bound :: bounds_r ->
  exists acts_l act acts_r,
    acts = acts_l ++ act :: acts_r /\
    valid_bounds sol (acts_l ++ acts_r) (bounds_l ++ bounds_r) /\
    bound.(b_lb) <= evaluate act.(activity_start) sol <= bound.(b_ub) /\
    bound.(b_usage) = act.(activity_usage) /\
    bound.(b_p_time) = act.(activity_duration).
Proof.
  intros sol.
  induction acts as [|act acts IH].
  { intros. inversion H. subst bounds.
    symmetry in H2.
    now apply app_eq_nil in H2. }
  intros bounds bounds_l bounds_r bound.
  intros Hvalid.
  destruct bounds_l as [|bound_l bounds_l].
  { simpl. intros Hbounds.
    rewrite Hbounds in Hvalid.
    apply valid_bounds_act_left in Hvalid.
    destruct Hvalid as (acts_l & acts_r & act' & Hacts & Hvalid & Hact').
    exists acts_l. exists act'. exists acts_r.
    repeat split; try easy.
    apply valid_bounds_app_acts.
    exact Hvalid. }
  intros Hbounds.
  inversion Hvalid.
  - subst act0 acts0. rename bound0 into bound'.
    rename bounds0 into bounds'.
    rename H2 into Hvalid'.
    rename H0 into Hbounds'.
    rewrite Hbounds in Hbounds'.
    simpl in Hbounds'; inversion Hbounds'.
    subst bound' bounds'; clear Hbounds'.
    rename Hvalid' into Hvalid_split.
    assert (bounds_l ++ bound :: bounds_r = bounds_l ++ bound :: bounds_r) as Hreq by reflexivity.
    specialize (IH (bounds_l ++ bound :: bounds_r) bounds_l bounds_r bound Hvalid_split Hreq).
    destruct IH as (acts_IH & act_IH & acts_r_IH &IHacts & IHvalid & IH).
    exists (act :: acts_IH). exists act_IH. exists acts_r_IH.
    repeat split; try easy.
    + clear IH.
      rewrite IHacts. reflexivity.
    + simpl. now apply valid_bounds_bound.
  - subst act0 acts0 bounds0.
    rename H2 into Hvalid_acts.
    specialize (IH bounds (bound_l :: bounds_l) bounds_r bound Hvalid_acts Hbounds).
    destruct IH as (acts_IH & act_IH & acts_r_IH &IHacts & IHvalid & IH).
    exists (act :: acts_IH). exists act_IH. exists acts_r_IH.
    repeat split; try easy.
    + rewrite IHacts. reflexivity.
    + simpl. apply valid_bounds_nobound. 
      exact IHvalid.
Qed.

Definition valid_prop_bound (bound : option ActivityBound) (bounds : list ActivityBound) :=
  match bound with
  | Some bound => In bound bounds
  | None => True
  end.

  Definition default_bound := mkBound Z0 Z0 N0 N0.

Lemma inferred_cumulative_bounds_spec constr fact bounds prop_bound_opt :
  forall sol,
    bounds <> nil
      ->
    inferred_cumulative_bounds constr fact = (bounds, prop_bound_opt)
      ->
    (valid_bounds sol constr.(activities) bounds
      ->
    valid_prop_bound prop_bound_opt bounds
      ->
    False)
      ->
    fact_valid sol fact.
Proof.
  intros sol Hnnil Hinfer_bounds Hvalid.
  unfold inferred_cumulative_bounds in Hinfer_bounds.
  destruct infer_domains as [[doms prop_var_opt]|] eqn:Hinfer.
  2: { inversion Hinfer_bounds; subst. contradiction. }
  apply infer_domains_correct with (doms := doms) (xconsq := prop_var_opt); try assumption.
  intros Hdoms_hold.
  remember (flat_map_option
(act_doms_to_bound doms)
(activities constr)) as bounds'.
  assert (infer_domains fact = Some (doms, prop_var_opt) -> sol_in_doms sol doms -> valid_bounds sol constr.(activities) bounds') as H.
  {
    clear -Heqbounds'. intros Hinfer Hdoms_hold.
    subst bounds'.
    remember (activities constr) as activities.
    clear Heqactivities.
    induction activities as [| act activities IH].
    - simpl. apply valid_bounds_nil.
    - simpl. destruct (act_doms_to_bound doms act) as [bound|] eqn:Hto_bound.
      + simpl. 
        unfold act_doms_to_bound in Hto_bound.
        destruct lb_ub_from_act_dom as [(lb & ub) |] eqn:Hlb_ub; try easy.
        apply valid_bounds_bound.
        * inversion Hto_bound; simpl; clear Hto_bound H0. unfold lb_ub_from_act_dom in Hlb_ub.
          destruct activity_start as [x|]; try easy.
          2: { inversion Hlb_ub; subst. simpl.
            split; reflexivity. }
          destruct smap.find as [dom|] eqn:Hfind; try easy.
          specialize (Hdoms_hold x).
          unfold dom_from_domains in Hdoms_hold.
          rewrite Hfind in Hdoms_hold.
          simpl in Hdoms_hold.
          unfold is_in_dom in Hdoms_hold.
          unfold lb_ub_from_dom in Hlb_ub.
          destruct (d_lb dom); try easy.
          destruct (d_ub dom); try easy.
          inversion Hlb_ub; subst.
          zext_as_z.
          simpl.
          lia.
        * inversion Hto_bound; reflexivity.
        * inversion Hto_bound; reflexivity.
        * exact IH.
      + simpl. apply valid_bounds_nobound.
        exact IH.
  }
  assert (bounds = bounds' -> prop_bound_opt <> None) as Hbound_opt_none.
  {
    clear Hinfer_bounds. intros Hbounds. 
    rewrite <- Hbounds in Heqbounds'; subst bounds'. 
    intros Hnone; subst prop_bound_opt.
    apply Hvalid.
    - apply H; assumption.
    - reflexivity.  
  }
  destruct prop_var_opt as [prop_var |] eqn:Hprop_var.
  {
    destruct find as [prop_act |] eqn:Hfind.
    2: { apply Hbound_opt_none; inversion Hinfer_bounds; reflexivity. }
    destruct smap.find as [prop_dom |] eqn:Hfind_dom.
    2: { apply Hbound_opt_none; inversion Hinfer_bounds; reflexivity. }
    inversion Hinfer_bounds. rewrite H1 in Heqbounds'; subst bounds' prop_bound_opt prop_var_opt; clear Hinfer_bounds.
    apply Hvalid.
    { apply H; assumption. }
    clear -Heqbounds' Hinfer Hfind_dom Hfind.
    subst bounds.
    unfold valid_prop_bound.
    destruct act_dom_to_bound as [prop_bound|] eqn:Hprop_bound; try reflexivity.
    apply find_some in Hfind.
    rewrite in_flat_map_option.
    exists prop_act.
    destruct Hfind as [Hin Hmatch].
    split.
    - exact Hin.
    - unfold activity_match in Hmatch.
      destruct activity_start as [x|] eqn:Hstart; try easy.
      rewrite String.eqb_eq in Hmatch; subst x.
      unfold act_doms_to_bound.
      unfold act_dom_to_bound in Hprop_bound.
      destruct lb_ub_from_dom as [(lb & ub)|] eqn:Hlb_ub_dom; try easy. inversion Hprop_bound; clear Hprop_bound H0.
      unfold lb_ub_from_act_dom.
      rewrite Hstart.
      rewrite Hfind_dom.
      rewrite Hlb_ub_dom.
      reflexivity.
  }
  {
    apply Hbound_opt_none; inversion Hinfer_bounds; reflexivity. 
  }
Qed. 

Definition mandatory_active (lb : Z) (ub : Z) (p_time : N) (t : Z) :=
  (ub <=? t) && (t <? (lb + (Z.of_N p_time))).

Definition activity_mandatory (t : Z) (bound : ActivityBound) : option N :=
  if mandatory_active (b_lb bound) (b_ub bound) (b_p_time bound) t
    then Some (b_usage bound)
    else None
  .

Lemma mandatory_active_is_active (sol : Assignment) :
  forall bound t usage,
    activity_mandatory t bound = Some usage
      ->
    forall act,
      bound.(b_lb) <= evaluate act.(activity_start) sol <= bound.(b_ub)
        ->
      (bound.(b_p_time) <= act.(activity_duration))%N
        ->
      is_active_at sol t act = true.
Proof.
  intros bound t usage. 
  unfold activity_mandatory.
  destruct mandatory_active eqn:Hmand; try easy.
  revert Hmand. unfold mandatory_active, is_active_at, evaluate.
  setoid_rewrite andb_true_iff. setoid_rewrite Z.leb_le. setoid_rewrite Z.ltb_lt. intros Ht _ act.
  destruct (activity_start act) eqn:Hstart; lia. 
Qed.

Definition bounds_mandatory_t (bounds : list ActivityBound) (t : Z) := flat_map_option (activity_mandatory t) bounds.

Definition bounds_mandatory_usage_t (bounds : list ActivityBound) (t : Z) :=
  n_sum (bounds_mandatory_t bounds t).

Definition resource_profile_t (capacity : N) (bounds : list ActivityBound) (t : Z) : option N :=
  let mand_usage := bounds_mandatory_usage_t bounds t in
  if (capacity <? mand_usage)%N
    then None
    else Some (capacity - mand_usage)%N.

(* resource_profile expects times in reverse order *)
Definition resource_profile (capacity : N) (bounds : list ActivityBound) (times : list Z) : list N :=
  map_valid (resource_profile_t capacity bounds) times nil.

Definition check_can_be_active (bound : ActivityBound) (usage_left_t : N) (t : Z) : bool :=
  if mandatory_active (b_lb bound) (b_ub bound) (b_p_time bound) t then true else 
    (b_usage bound <=? usage_left_t)%N.

Fixpoint z_map {A B} (f : A -> Z -> B) (l : list A) (z : Z) :=
  match l with
  | nil => nil
  | a :: l' => (f a z) :: z_map f l' (z + 1)
  end.

Lemma z_map_as_map {A B} (f : A -> Z -> B) :
  forall l z,
    z_map f l z = map (fun p => f (fst p) (snd p)) (combine l (range z ((Z.of_nat (length l)) + z - 1))).
Proof.
  induction l.
  - simpl; easy.
  - intros z. simpl z_map. simpl length.
    remember (Z.of_nat (length l)) as llen.
    replace (Z.of_nat (S (length l)) + z - 1) with (llen + z) by lia.
    rewrite range_cons; try lia.
    simpl. rewrite IHl.
    replace (llen + (z + 1) - 1) with (llen + z) by lia.
    reflexivity.
Qed.

Lemma length_z_map {A B} (f : A -> Z -> B) :
  forall l z,
    length (z_map f l z) = length l.
Proof.
  intros l z.
  rewrite z_map_as_map. rewrite length_map.
  rewrite length_combine.
  rewrite length_range.
  lia.
Qed.

Lemma z_map_spec {A B} (f : A -> Z -> B) (d : A) (d_b : B):
  forall l z n a,
    z <= n < (Z.of_nat (length l)) + z
      ->
    nth_z n l z d = a
      ->
    nth_z n (z_map f l z) z d_b = f a n.
Proof.
  intros l z n a.
  unfold nth_z in *.
  destruct (n >=? z) eqn:Hn.
  - intros Hznl Ha.
    rewrite z_map_as_map.
    remember (Z.of_nat (length l) + z - 1) as e.
    assert (z <= e) as Hze by lia.
    remember (fun p : A * Z => f (fst p) (snd p)) as fpair.
    rewrite nth_indep with (d' := fpair (a, Z0)).
    2: { rewrite length_map. rewrite length_combine.
      rewrite length_range. lia. }
    rewrite map_nth.
    rewrite combine_nth.
    + subst fpair. simpl.
      rewrite nth_indep with (d' := d); try lia.
      rewrite Ha.
      rewrite <- nth_z_spec; try lia.
      rewrite range_spec.
      * reflexivity.
      * lia. 
    + rewrite length_range.
      lia.
  - intros Hznl. lia.
Qed.

Lemma nth_z_run (l : list bool) :
  forall k n start,
    let kz := Z.of_nat k in
    let nz := Z.of_nat n in
    (forall iz,
      start + kz <= iz < start + kz + nz
        ->
      nth_z iz l start true = true
    )
      ->
    (forall i,
      k <= i < k + n
        ->
      nth i l true = true)%nat.
Proof.
  intros k n start kz nz.
  intros H.
  intros i Hi.
  remember (Z.of_nat i + start) as iz.
  specialize (H iz).
  rewrite nth_z_spec in H; try lia.
  assert (Z.to_nat (iz - start) = i) as Hizi by lia.
  rewrite Hizi in H. apply H.
  lia.
Qed.

Lemma run_at_z_map {A} (f : A -> Z -> bool) (l : list A) (start : Z) (d : A) :
  forall k n,
    let kz := Z.of_nat k in
    let nz := Z.of_nat n in
    (length l >= k + n)%nat
      ->
    (forall e a, 
      start + kz <= e < start + kz + nz
        ->
      nth_z e l start d = a
        ->
      f a e = true
    )
      ->
    (run_at k (z_map f l start) >= n)%nat.
Proof.
  intros k n kz nz.
  intros Hlen H.
  apply run_at_nth.
  { rewrite length_z_map. exact Hlen. }
  apply nth_z_run with (start := start).
  intros iz Hiz.
  rewrite z_map_spec with (d := d) (a := nth_z iz l start d).
  - apply H; try lia.
    reflexivity.
  - lia.
  - reflexivity.
Qed. 

Definition profile_to_active_list (act_bound : ActivityBound) (profile : list N) :=
  z_map (check_can_be_active act_bound) profile (b_lb act_bound).

Definition can_schedule_activity_with_profile (bound : ActivityBound) (profile : list N) :=
  has_n_true (N.to_nat bound.(b_p_time)) (profile_to_active_list bound profile).

Definition cannot_schedule_activity (capacity : N) (bounds : list ActivityBound) (bound : ActivityBound) :=
  let times := range_rev bound.(b_lb) (bound.(b_ub) + Z.of_N (bound.(b_p_time)) - 1) in
  match resource_profile capacity bounds times with
  | nil => true
  | profile => negb (can_schedule_activity_with_profile bound profile)
  end.

Definition bounds_times (bounds : list ActivityBound) :=
  let t_min := min_l (map b_lb bounds) in
  let t_max := max_l (map b_ub bounds) in
  (* We don't include the processing time because they will have been already conflicting at the latest start time *)
  (t_min, t_max).

Lemma valid_bounds_properties constr sol bounds : 
  valid_bounds sol constr.(activities) bounds
    ->
  Forall (fun bound => 
    (bound.(b_p_time) >= 1)%N
      /\
    bound.(b_lb) <= bound.(b_ub)
  ) bounds.
Proof.
  intros Hvalid.
  rewrite Forall_forall. intros bound Hin.
  apply in_split in Hin.
  destruct Hin as (bounds_l & bounds_r & Hbounds).
  apply valid_bound_matching_activity with (sol := sol) (acts := constr.(activities)) in Hbounds.
  2: { exact Hvalid. }
  destruct Hbounds as (acts_l & act & acts_r & H).
  split.
  - specialize constr.(valid_durations) as Hdur.
    rewrite Forall_forall in Hdur.
    specialize (Hdur act).
    assert (In act (activities constr)) as Hin.
    { destruct H as (H & _). rewrite H.
      rewrite in_app_iff. right. simpl.
      left. reflexivity. }
    apply Hdur in Hin.
    lia.
  - lia.
Qed.
    


Lemma bounds_times_le constr sol bounds :
  valid_bounds sol constr.(activities) bounds
    ->
  forall t_min t_max,
  bounds_times bounds = (t_min, t_max)
    ->
  t_min <= t_max.
Proof.
  intros Hvalid. intros t_min t_max.
  unfold bounds_times.
  induction activities as [| act acts IH].
  - inversion Hvalid. subst bounds. unfold min_l.
    unfold max_l. simpl. intros Ht.
    inversion Ht; subst. reflexivity.
  - inversion Hvalid.
    + subst act0 acts0; rename bounds0 into bounds'.
      rewrite H0.
      assert (In (b_lb bound) (map b_lb bounds)) as Hlb.
      { subst bounds. left. reflexivity. }
      assert (In (b_ub bound) (map b_ub bounds)) as Hub.
      { subst bounds. left. reflexivity. }
      apply min_l_spec in Hlb.
      apply max_l_spec in Hub.
      simpl.
      intros H; inversion H; subst; clear H.
      lia.
    + apply IH; assumption. 
Qed.

Definition resource_profile_full (capacity : N) (bounds : list ActivityBound) :=
  let (t_min, t_max) := bounds_times bounds in
  let times := range t_min t_max in
  match resource_profile capacity bounds times with
  | nil => true
  | _ => false
  end.

(* Main possible improvements:
  - Reuse the full resource profile for the cannot schedule
  - Allow the use of 'hints' to be able to determine at what time there is a profile conflict, or what activity cannot be scheduled (requires changing the proof format) *)
Definition cumulative_checker (fact : ProofFact) (constraint : CumulativeConstraint) : bool :=
  match inferred_cumulative_bounds constraint fact with
  | (nil, _) => false
  | (bounds, rhs_bound) =>
    (* First try if we cannot schedule the activity from the rhs *)
    let cannot_schedule_rhs :=
      match rhs_bound with
      | Some rhs_bound => cannot_schedule_activity (capacity constraint) bounds rhs_bound
      | None => false
      end in
    if cannot_schedule_rhs then true
    (* Then try to find a time conflict on the full profile *)
    else if resource_profile_full (capacity constraint) bounds then true
    (* Otherwise fallback and try all activities *)
    else existsb (cannot_schedule_activity (capacity constraint) bounds) bounds
  end.

Lemma nil_rev {A} :
  forall (l : list A),
    rev l = nil <-> l = nil.
Proof.
  intros l. split; intros H.
  + apply rev_inj. rewrite H. reflexivity.
  + rewrite H. reflexivity.
Qed.

Open Scope N_scope.
Lemma bounds_mandatory_t_le_usage sol :
  forall activities bounds,
  valid_bounds sol activities bounds
    ->
  forall t, 
    bounds_mandatory_usage_t bounds t
      <=
    usage_at_timepoint sol t activities.
Proof.
  intros activities.
  induction activities as [| act acts IH].
  - intros bounds Hvalid t.
    inversion Hvalid. subst bounds.
    reflexivity.
  - intros bounds Hvalid t.
    assert (forall act acts, usage_at_timepoint sol t acts <= usage_at_timepoint sol t (act :: acts)) as Hact_add.
    { clear. intros act acts.
      unfold usage_at_timepoint. 
      setoid_rewrite n_fold_is_n_sum.
      unfold n_sum. simpl.
      destruct is_active_at.
      + simpl. setoid_rewrite n_sum_add. lia.
      + reflexivity. }
    inversion Hvalid.
    + subst act0 acts0; rename bounds0 into bounds'.
      specialize (IH bounds' H2 t).
      specialize (Hact_add act acts).
      unfold bounds_mandatory_usage_t; simpl.
      destruct activity_mandatory eqn:Hmand.
      2: { simpl. unfold bounds_mandatory_usage_t in IH. lia. }
      pose proof Hmand as Hactive.
      unfold activity_mandatory in Hmand.
      destruct mandatory_active in Hmand; try easy.
      inversion Hmand; subst n; clear Hmand. 
      apply mandatory_active_is_active with (sol := sol) (act := act) in Hactive.
      * simpl.
        unfold usage_at_timepoint in *.
        rewrite n_fold_is_n_sum in *.
        simpl; rewrite Hactive; simpl.
        unfold n_sum; simpl; setoid_rewrite n_sum_add.
        unfold bounds_mandatory_usage_t in IH.
        lia.
      * exact Hstart.
      * lia.
    + specialize (IH bounds H2 t).
      specialize (Hact_add act acts).
      lia.
Qed.
  
Lemma resource_profile_contradiction constr sol bounds :
  Cumulative constr sol
    ->
  valid_bounds sol constr.(activities) bounds
    -> 
  forall times,
    times <> nil
      ->
    resource_profile (capacity constr) bounds times <> nil.
Proof.
  intros Hcumul Hvalid.
  intros times Htimesnnil.
  unfold resource_profile.
  intros Hmap_valid.
  apply map_valid_nil_ex_none in Hmap_valid.
  2: { assumption. }
  destruct Hmap_valid as (t & Ht_in & Hprofile).
  unfold resource_profile_t in Hprofile.
  destruct (capacity constr <? bounds_mandatory_usage_t bounds t)%N eqn:Hcap.
  2: { discriminate Hprofile. }
  rewrite N.ltb_lt in Hcap.
  specialize (Hcumul t).
  apply bounds_mandatory_t_le_usage with (t := t) in Hvalid. lia.
Qed.

Open Scope Z_scope.
Definition valid_profile capacity bounds (profile : list N) (t_min t_max : Z) :=
  length profile = Z.to_nat (t_max - t_min + 1)
    /\
  forall t,
    t_min <= t <= t_max
      ->
    Some (nth_z t profile t_min N0) = resource_profile_t capacity bounds t.

(* Search (_ + 0). *)

Lemma can_schedule_activity_with_profile_valid constr sol bounds :
  Cumulative constr sol
    ->
  valid_bounds sol constr.(activities) bounds
    ->
  forall bound profile,
    In bound bounds
      ->
    valid_profile (capacity constr) bounds profile (b_lb bound) (b_ub bound + Z.of_N (b_p_time bound) - 1) 
      ->
    can_schedule_activity_with_profile bound profile = true.
Proof.
  intros Hcumul Hvalid.
  intros bound profile Hinbounds.
  intros Hprofile_valid.
  unfold can_schedule_activity_with_profile.
  apply exists_run_then_n_true.
  apply in_split in Hinbounds.
  destruct Hinbounds as (bounds_l & bounds_r & Hbounds).
  apply valid_bound_matching_activity with (bounds_l := bounds_l) (bounds_r := bounds_r) (bound := bound) in Hvalid.
  2: { assumption. }
  destruct Hvalid as (acts_l & act & acts_r & Hacts & Hvalid_ex & Hstart & Hbound_u & Hbound_p).
  remember (evaluate (activity_start act) sol) as start.
  exists (Z.to_nat (start - b_lb bound)).
  unfold profile_to_active_list.
  destruct Hprofile_valid as [Hprofile_len Hprofile_valid].
  apply run_at_z_map with (d := N0).
  { rewrite Hprofile_len. lia. }
  clear Hprofile_len.
  intros t t_usage.
  intros Ht'.
  assert (start <= t < start + Z.of_N (b_p_time bound)) as Ht by lia; clear Ht'.
  assert (b_lb bound <= t <= b_ub bound + Z.of_N (b_p_time bound) - 1) as Htbounds by lia.
  specialize (Hprofile_valid t Htbounds); clear Htbounds.
  intros Htusage.
  rewrite Htusage in Hprofile_valid; clear Htusage.
  unfold resource_profile_t in Hprofile_valid.
  destruct (capacity constr <? bounds_mandatory_usage_t bounds t)%N eqn:Hcapbounds; try discriminate Hprofile_valid.
  inversion Hprofile_valid; subst t_usage; clear Hprofile_valid.
  unfold check_can_be_active.
  destruct mandatory_active eqn:Hmand.
  { reflexivity. }
  rewrite <- not_true_iff_false in Hcapbounds.
  rewrite N.ltb_lt in Hcapbounds.
  assert (bounds_mandatory_usage_t bounds t <= capacity constr)%N by lia; clear Hcapbounds.
  rewrite N.leb_le.
  enough (bounds_mandatory_usage_t bounds t + (b_usage bound) <= capacity constr)%N by lia.
  specialize (Hcumul t).
  enough (bounds_mandatory_usage_t bounds t + (b_usage bound) <= usage_at_timepoint sol t (activities constr))%N by lia.
  clear Hcumul H.
  rewrite Hbounds.
  clear Hstart.
  rewrite Hacts.
  unfold usage_at_timepoint, bounds_mandatory_usage_t, bounds_mandatory_t.
  rewrite n_fold_is_n_sum.
  rewrite flat_map_option_as_filter_map with (d := N0). setoid_rewrite filter_app. simpl.
  destruct filter_f_option eqn:Hfilter.
  { unfold filter_f_option in Hfilter.
    unfold activity_mandatory in Hfilter.
    now rewrite Hmand in Hfilter. }
  destruct (is_active_at sol t act) eqn:Hactive.
  2: { exfalso. clear -Ht Hactive Heqstart Hbound_p.
    revert Hactive. unfold is_active_at.
    rewrite <- Heqstart.
    rewrite andb_false_iff.
    intros [Hl | Hr]; lia. }
  setoid_rewrite map_app at 2. simpl.
  rewrite n_sum_app.
  unfold n_sum at 3. simpl. rewrite n_sum_add.
  rewrite <- filter_app.
  rewrite <- flat_map_option_as_filter_map.
  rewrite N.add_0_r.
  rewrite N.add_assoc at 1.
  rewrite <- n_sum_app.
  rewrite <- map_app.
  rewrite <- filter_app.
  apply bounds_mandatory_t_le_usage with (t := t) in Hvalid_ex.
  unfold bounds_mandatory_usage_t, usage_at_timepoint, bounds_mandatory_t in Hvalid_ex.
  rewrite n_fold_is_n_sum in Hvalid_ex.
  lia.
Qed.

Lemma resource_profile_valid constr sol bounds :
  Cumulative constr sol
    ->
  valid_bounds sol constr.(activities) bounds
    ->
  forall profile t_min t_max,
    profile = resource_profile (capacity constr) bounds (range_rev t_min t_max)
      ->
    profile <> nil
      ->
    valid_profile (capacity constr) bounds profile t_min t_max.
Proof.
  intros Hcumul Hvalid.
  intros profile t_min t_max Hprofile Hprofilennil.
  destruct (Z_gt_le_dec t_min t_max) as [Hgt | Hle].
  - subst profile; unfold range_rev.
    assert (Z.to_nat (t_max - t_min + 1) = O) by lia.
    rewrite H. simpl.
    split.
    + simpl. lia.
    + intros t Ht. lia.
  - unfold resource_profile in Hprofile.
    apply map_valid_spec with (d := N0) in Hprofile as [Hprofile Hsome]; try assumption; clear Hprofilennil.
    remember (option_map_default
      (resource_profile_t
      (capacity constr) bounds)
      0%N) as fprof.
    assert (length (map fprof (range_rev t_min t_max)) = Z.to_nat (t_max - t_min + 1)) as Hlength.
    { rewrite length_map. rewrite range_rev_is_rev_range. rewrite length_rev.
      rewrite length_range. reflexivity. }
    split.
    { subst profile. rewrite length_rev. exact Hlength. }
    intros t Ht; clear Hle.
    assert (In t (range_rev t_min t_max)) as Hintrange.
    { clear -Ht. rewrite range_rev_is_rev_range.
      rewrite <- in_rev. rewrite <- in_range. exact Ht. }
    specialize (Hsome t Hintrange); clear Hintrange.
    destruct resource_profile_t eqn:Hprofilet; try contradiction; clear Hsome.
    f_equal.
    subst profile.
    rewrite nth_z_spec by lia.
    rewrite rev_nth by lia.
    rewrite Hlength.
    replace (Z.to_nat (t_max - t_min + 1) - S (Z.to_nat (t - t_min)))%nat with (Z.to_nat (t_max - t)) by lia.
    rewrite <- map_nth_len_lt with (d := 0).
    2: { rewrite <- length_map with (f := fprof). 
      rewrite Hlength. lia. }
    clear Hlength.
    subst fprof.
    unfold option_map_default.
    replace (t_max - t) with ((t_max + t_min - t) - t_min) by lia.
    rewrite <- nth_z_spec by lia.
    rewrite range_rev_spec by lia.
    replace (t_max - (t_max + t_min - t - t_min)) with t by lia.
    rewrite Hprofilet.
    reflexivity.
Qed. 

Lemma cannot_schedule_activity_valid constr sol bounds :
  Cumulative constr sol
    ->
  valid_bounds sol constr.(activities) bounds
    ->
  forall bound,
    In bound bounds
      ->
    cannot_schedule_activity (capacity constr) bounds bound = false.
Proof.
  intros Hcumul Hvalid.
  intros bound Hinbounds.
  unfold cannot_schedule_activity.
  pose proof Hvalid as Hvalid'.
  destruct resource_profile eqn:Hprofile.
  { exfalso. apply resource_profile_contradiction with (sol := sol) in Hprofile; try assumption.
    apply valid_bounds_properties in Hvalid.
    rewrite Forall_forall in Hvalid.
    apply Hvalid in Hinbounds.
    rewrite range_rev_is_rev_range.
    rewrite nil_rev.
    rewrite range_cons by lia.
    easy. }
  remember (n :: l) as profile.
  assert (profile <> nil) as Hprofilennil.
  { subst profile. now intros Hnl. }
  clear Heqprofile n l.
  rewrite negb_false_iff.
  apply can_schedule_activity_with_profile_valid with (constr := constr) (sol := sol) (bounds := bounds).
  - exact Hcumul.
  - exact Hvalid.
  - exact Hinbounds.
  - apply resource_profile_valid with (sol := sol);
    try assumption.
    subst profile. reflexivity.
Qed.

Lemma checker_cumulative_eq_true :
  forall fact sol constr,
  Cumulative constr sol
  -> cumulative_checker fact constr = true
  -> fact_valid sol fact.
Proof.
  intros fact sol constr.
  intros Hcumul Hchecked.
  unfold cumulative_checker in Hchecked.
  destruct inferred_cumulative_bounds as [bounds prop_bound_opt] eqn:Hbounds.
  destruct bounds as [|b bounds'] eqn:Hbounds'.
  { discriminate Hchecked. }
  assert (bounds <> nil) as Hboundsnnil.
  { intros Hnil. subst bounds. discriminate Hnil. }
  rewrite <- Hbounds' in *; clear b bounds' Hbounds'.
  apply inferred_cumulative_bounds_spec with (constr := constr) (bounds := bounds) (prop_bound_opt := prop_bound_opt); try assumption.
  clear Hboundsnnil.
  intros Hvalid Hprop_bound.
  assert ((exists bound, In bound bounds /\ cannot_schedule_activity (capacity constr) bounds bound = true) \/ resource_profile_full (capacity constr) bounds = true).
  {
    destruct prop_bound_opt as [prop_bound|].
    - destruct (cannot_schedule_activity (capacity constr) bounds prop_bound) eqn:Hprop_cannot.
      + left. exists prop_bound.
        unfold valid_prop_bound in Hprop_bound.
        now split.
      + destruct resource_profile_full eqn:Hprofile.
        * right. reflexivity.
        * rewrite existsb_exists in Hchecked.
          left. exact Hchecked.
    - destruct resource_profile_full eqn:Hprofile.
      + right. reflexivity.
      + rewrite existsb_exists in Hchecked.
        left. exact Hchecked.
  }
  clear Hchecked Hprop_bound Hbounds.
  destruct H as [(bound & Hinbounds & Hcannot) | Hprofile_full].
  - enough (cannot_schedule_activity (capacity constr) bounds bound = false) 
      by (rewrite H in Hcannot; discriminate).
    apply cannot_schedule_activity_valid with (sol := sol).
    + exact Hcumul.
    + exact Hvalid.
    + exact Hinbounds.
  - unfold resource_profile_full in Hprofile_full.
    destruct (bounds_times bounds) as [t_min t_max] eqn:Htimes.
    destruct resource_profile eqn:Hprofile; try discriminate.
    enough (resource_profile (capacity constr) bounds (range t_min t_max) <> nil)
      by (rewrite Hprofile in H; contradiction).
    apply resource_profile_contradiction with (sol := sol);
      try assumption.
    rewrite range_cons.
    + easy.
    + eapply bounds_times_le.
      * exact Hvalid.
      * exact Htimes.
Qed.

Lemma checker_cumulative :
  forall fact sol constr,
  Cumulative constr sol
  -> cumulative_checker fact constr = true
  -> fact_valid sol fact.
Proof.
  intros fact sol constr.
  intros H1 H2.
  apply checker_cumulative_eq_true with (constr := constr);
  assumption.
Qed.

Open Scope string.

(* Mandatory conflict *)    
Compute 
  let constr := build_cumulative 
    (
      mkAct (var_name "x") 4%N 1%N ::
      mkAct (var_name "y") 3%N 1%N ::
      nil
    ) 
    1%N in
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
      mkAct (var_name "x") 4%N 1%N ::
      mkAct (var_name "y") 1%N 1%N ::
      nil
    ) 
    1%N in
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

Compute 
  let constr := build_cumulative 
    (
      mkAct (var_name "x") 4%N 1%N ::
      mkAct (var_name "y") 1%N 1%N ::
      nil
    ) 
    1%N in
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
      mkAct (var_name "x") 4%N 1%N ::
      mkAct (var_name "y") 1%N 1%N ::
      nil
    ) 
    1%N in
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
      mkAct (var_name "x") 4%N 1%N ::
      mkAct (var_name "y") 1%N 1%N ::
      nil
    ) 
    1%N in
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
      mkAct (var_name "x") 4%N 1%N ::
      mkAct (var_name "y") 2%N 1%N ::
      nil
    ) 
    1%N in
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
      mkAct (var_name "x") 4%N 1%N ::
      mkAct (var_name "y") 2%N 1%N ::
      nil
    ) 
    1%N in
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
