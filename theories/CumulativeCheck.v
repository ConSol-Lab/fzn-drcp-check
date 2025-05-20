
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import String.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Arith.PeanoNat.
Require Import Bool.
Require Import Lia.

Require Import Checker.Cumulative.
Require Checker.CumulativeUtil.
Import CumulativeUtil.RunOfN.
Import CumulativeUtil.XNSum.

Require Checker.Utility.
Import Utility.Maps.
Import Utility.ListEx.
Import Utility.Sets.
Import Utility.ZRange.
Import Utility.SubList.
Require Import Checker.Domain.
Require Import Checker.DomainVar.
Require Import Checker.Deduction.
Import Datatypes.

Record ActivityBound := mkBound {
  b_x : string;
  b_lb : Z;
  b_ub : Z;
  b_p_time : N;
  b_usage : N;
}.

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

Definition domain_to_bound (param_map : string -> (N * N)) (x : string) (dom : Domain) :=
  match dom.(d_lb) with
  | Some lb =>
    match dom.(d_ub) with
    | Some ub =>
      match param_map x with
      | (p, u) => Some (mkBound x lb ub p u)
      end
    | _ => None
    end
  | _ => None
  end.

Definition domains_to_bounds (doms : DomainMap) (param_map : string -> (N * N)) :=
  smap.mapi (domain_to_bound param_map) doms.

Definition unwrap_bindings {A B} (l : list (A * option B)) :=
  flat_map_option snd l.

Definition inferred_cumulative_bounds (constr : CumulativeConstraint) (fact : Deduction.Inference) :=
  let activity_vars := constraint_to_vs constr in
  match infer_domains (Some activity_vars) fact with
  | None => (nil, None)
  | Some (domains, prop_var) =>
    let param_map := constraint_to_param_map constr in
    let bounds_map := domains_to_bounds domains param_map in
    let bounds := unwrap_bindings (smap.bindings bounds_map) in
    match prop_var with
    | None => (bounds, None) 
    | Some prop_var =>
      match smap.find prop_var bounds_map with
      | Some (Some prop_bound) => (bounds, Some prop_bound)
      | _ => (nil, None)
      end
    end
  end.

Definition bound_to_act (sol : string -> Z) (bound : ActivityBound) :=
  mkAct (b_x bound) (sol (b_x bound)) (b_p_time bound) (b_usage bound).

Lemma act_bound_p_ge_1 constr sol :
  forall bound,
  In (bound_to_act sol bound) (activity_list constr sol)
    ->
  (bound.(b_p_time) >= 1)%N.
Proof.
  intros bound Hin.
  specialize constr.(valid_p_times) as Hp.
  enough (p_time (bound_to_act sol bound) >= 1)%N.
  { unfold bound_to_act in H.
    destruct bound. simpl in *. assumption. }
  remember (bound_to_act sol bound) as act;
  clear Heqact bound.
  apply a_def_in_if in Hin.
  enough (def_p (a_def_from_activity act) >= 1)%N.
  { unfold a_def_from_activity in H. 
    destruct act. simpl in *. assumption. }
  apply Hp.
  exact Hin.
Qed.

Definition valid_bounds (bounds : list ActivityBound) (c : CumulativeConstraint) (sol : string -> Z) :=
  forall bound, In bound bounds
    ->
  In (bound_to_act sol bound) (activity_list c sol)
    /\
  b_lb bound <= (bound_to_act sol bound).(start) <= b_ub bound.

Definition valid_prop_bound (bound : option ActivityBound) (bounds : list ActivityBound) :=
  match bound with
  | Some bound => In bound bounds
  | None => True
  end.

Definition unique_bounds (bounds : list ActivityBound) :=
  NoDup (map b_x bounds).

Definition default_bound := mkBound "x"%string Z0 Z0 N0 N0.

Lemma inferred_cumulative_bounds_unique constr fact :
  forall bounds prop_bound_opt,
    inferred_cumulative_bounds constr fact = (bounds, prop_bound_opt)
      ->
    unique_bounds bounds.
Proof.
  intros bounds prop_bound_opt.
  unfold inferred_cumulative_bounds.
  intros H.
  assert (bounds = nil \/ exists doms, bounds = unwrap_bindings (smap.bindings (domains_to_bounds doms (constraint_to_param_map constr)))) as Hbounds.
  {
    destruct infer_domains as [[doms prop_var]|] eqn:Hinfer.
    - destruct prop_var.
      + destruct smap.find as [found|].
        * destruct found.
          -- right.
            exists doms. 
            inversion H; reflexivity.
          -- left. inversion H; reflexivity.
        * left. inversion H; reflexivity.
      + right. 
        exists doms.
        inversion H; reflexivity.
    - left. inversion H; reflexivity.
  }
  clear -Hbounds.
  destruct Hbounds as [Hbounds | (m & Hbounds)].
  - subst. apply NoDup_nil.
  - assert (forall x a, In (x, Some a) (smap.bindings (domains_to_bounds m (constraint_to_param_map constr))) -> (x = b_x a)) as Hinx.
    {
      clear. intros x a.
      unfold domains_to_bounds.
      rewrite smap.mapi_spec.
      rewrite in_map_iff.
      intros ([x' dom] & Hpair & Hin).
      inversion Hpair; subst; clear Hpair.
      rename H1 into Hto_bound.
      unfold domain_to_bound in Hto_bound.
      destruct dom as [lb ub holes].
      destruct lb as [lb|]; try easy; destruct ub as [ub|]; try easy; simpl in Hto_bound.
      destruct constraint_to_param_map as [p u].
      destruct a; inversion Hto_bound.
      reflexivity.
    }
    subst bounds.
    unfold unwrap_bindings.
    unfold unique_bounds.
    rewrite flat_map_option_as_filter_map with (d := default_bound).
    apply nodup_key with (a_k := fst).
    + clear.
      remember (smap.bindings
        (domains_to_bounds m
        (constraint_to_param_map constr))) as l.
      assert (NoDup (map fst l)).
      { subst l. apply nodup_bindings_keys. }
      apply nodup_map_filter.
      exact H.
    + intros [x a_opt].
      intros H.
      rewrite filter_In in H.
      destruct H as (Hin & Hfiltertrue).
      unfold filter_f_option in Hfiltertrue.
      unfold option_map_default.
      destruct snd eqn:Hopt; try discriminate Hfiltertrue.
      simpl in Hopt; subst a_opt.
      simpl. apply Hinx in Hin. assumption. 
Qed.

Lemma inferred_cumulative_bounds_spec constr fact bounds prop_bound_opt :
  forall sol,
    bounds <> nil
      ->
    inferred_cumulative_bounds constr fact = (bounds, prop_bound_opt)
      ->
    (valid_bounds bounds constr sol
      ->
    valid_prop_bound prop_bound_opt bounds
      ->
    False)
      ->
    inference_valid sol fact.
Proof.
  intros sol Hnnil Hinfer_bounds Hvalid.
  unfold inferred_cumulative_bounds in Hinfer_bounds.
  destruct infer_domains as [[doms prop_var_opt]|] eqn:Hinfer.
  2: { inversion Hinfer_bounds; subst. contradiction. }
  apply infer_domains_correct with (vs := (Some (constraint_to_vs constr))) (doms := doms) (xconsq := prop_var_opt); try assumption.
  intros Hdoms_hold.
  remember (unwrap_bindings
    (smap.bindings
    (domains_to_bounds doms
    (constraint_to_param_map constr)))) as bounds'.
  assert (infer_domains (Some (constraint_to_vs constr)) fact = Some (doms, prop_var_opt) -> doms_hold_for_sol sol doms -> valid_bounds bounds' constr sol) as H.
  {
    clear -Heqbounds'. intros Hinfer Hdoms_hold.
    subst bounds'.
    unfold valid_bounds. intros bound Hin.
    unfold unwrap_bindings in Hin. rewrite in_flat_map_option in Hin.
    destruct Hin as ([x bound_opt] & Hin_bindings & Hin_as_l).
    simpl in Hin_as_l; subst bound_opt.
    unfold activity_list, activity_list_inner.
    unfold domains_to_bounds in Hin_bindings.
    rewrite smap.mapi_spec in Hin_bindings.
    rewrite in_map_iff in *.
    destruct Hin_bindings as ([x' dom] & Hto_bound & Hindoms).
    inversion Hto_bound; subst x'; clear Hto_bound.
    rename H1 into Hto_bound.
    apply infer_domains_vs with (x := x) (dom := dom) in Hinfer; try assumption.
    rewrite smap_in_spec in Hindoms.
    apply (Hdoms_hold x dom) in Hindoms; clear Hdoms_hold.
    unfold domain_to_bound in Hto_bound.
    destruct dom as [lb ub holes] eqn:Hdom;
    destruct lb as [lb|]; destruct ub as [ub|]; try easy; simpl in Hto_bound.
    destruct (constraint_to_param_map constr x) as [p u] eqn:Hpu.
    destruct bound as [bx blb bub bp bu]; inversion Hto_bound; subst bx blb bub bp bu; clear Hto_bound.
    simpl in *.
    split.
    - clear -Hinfer Hpu.
      exists (mkActDef x p u).
      unfold activity_from_a_def. split; try reflexivity.
      unfold constraint_to_param_map in Hpu.
      symmetry in Hpu.
      apply param_map_in in Hpu.
      + rewrite in_map_iff in Hpu.
        destruct Hpu as (a_def & Ha_def & Hin).
        destruct a_def as [x' p' u']; inversion Ha_def; subst.
        exact Hin.
      + clear Hpu.
        unfold constraint_to_vs, constraint_to_vars in Hinfer.
        rewrite sstr.build_spec in Hinfer.
        rewrite map_map.
        rewrite in_map_iff in *.
        destruct Hinfer as (a_def & Hx & Hin).
        exists a_def.
        split; try assumption.
        destruct a_def. simpl.
        apply Hx.
    - unfold is_in_dom in Hindoms. lia.
  }

  destruct prop_var_opt as [prop_var |] eqn:Hprop_var.
  {
    destruct smap.find as [prop_bound_opt' |] eqn:Hfind.
    2: { inversion Hinfer_bounds. subst bounds. contradiction. }
    destruct prop_bound_opt' as [prop_bound |].
    2: { inversion Hinfer_bounds. subst bounds. contradiction. }
    inversion Hinfer_bounds. rewrite H1 in Heqbounds'; subst bounds' prop_bound_opt prop_var_opt; clear Hinfer_bounds.
    apply Hvalid.
    { apply H; try assumption. }
    clear -Heqbounds' Hinfer Hfind.
    subst bounds.
    unfold valid_prop_bound.
    rewrite smap.find_spec in Hfind.
    rewrite <- smap_in_spec in Hfind.
    unfold unwrap_bindings.
    rewrite in_flat_map_option.
    exists (prop_var, Some prop_bound).
    split.
    - assumption.
    - simpl. reflexivity.
  }
  {
    inversion Hinfer_bounds; rewrite H1 in Heqbounds'; subst bounds' prop_bound_opt.
    apply Hvalid.
    - apply H; try assumption.
    - reflexivity.
  }
Qed. 

Definition mandatory_active (lb : Z) (ub : Z) (p_time : N) (t : Z) :=
  (ub <=? t) && (t <? (lb + (Z.of_N p_time))).

Lemma mandatory_active_is_active :
  forall start lb ub p_time t,
    lb <= start <= ub
      ->
    mandatory_active lb ub p_time t = true
      ->
    is_active_at start p_time t = true.
Proof.
  intros start lb ub p t.
  intros Hstart.
  unfold mandatory_active, is_active_at.
  lia.
Qed.

Definition activity_mandatory (t : Z) (bound : ActivityBound) : option (string * N) :=
  if mandatory_active (b_lb bound) (b_ub bound) (b_p_time bound) t
    then Some (b_x bound, b_usage bound)
    else None
  .

Definition bounds_mandatory_t (bounds : list ActivityBound) (t : Z) := flat_map_option (activity_mandatory t) bounds.

Definition bounds_mandatory_usage_t (bounds : list ActivityBound) (t : Z) :=
  xn_sum (bounds_mandatory_t bounds t).

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

Lemma bounds_times_le constr sol bounds :
  valid_bounds bounds constr sol
    ->
  forall t_min t_max,
  bounds_times bounds = (t_min, t_max)
    ->
  t_min <= t_max.
Proof.
  intros Hvalid. intros t_min t_max.
  unfold bounds_times.
  destruct bounds as [|bound bounds'].
  - unfold min_l, max_l. simpl.
    intros H. inversion H.
    reflexivity.
  - remember (bound :: bounds') as bounds.
    assert (In bound bounds) as Hinbounds.
    { subst bounds. left. reflexivity. }
    specialize (Hvalid bound Hinbounds).
    assert (In (b_lb bound) (map b_lb bounds)) as Hlb.
    { subst bounds. left. reflexivity. }
    assert (In (b_ub bound) (map b_ub bounds)) as Hub.
    { subst bounds. left. reflexivity. }
    apply min_l_spec in Hlb.
    apply max_l_spec in Hub.
    destruct Hvalid as [_ Hbounds].
    clear -Hbounds Hlb Hub.
    intros H; inversion H; subst; clear H.
    lia.
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
Definition cumulative_checker (fact : Deduction.Inference) (constraint : CumulativeConstraint) : bool :=
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

Lemma bounds_mandatory_t_sublist constr sol bounds :
  unique_bounds bounds
    ->
  valid_bounds bounds constr sol
    ->
  forall t, 
  sublist (bounds_mandatory_t bounds t)
    (map act_to_xn
      (activities_at_t (activity_list constr sol)
        t)).
Proof.
  intros Hunique Hvalid. intros t.
  apply sublist_if_in_nodup.
  - intros [x u] Hin.
    rewrite in_map_iff.
    unfold bounds_mandatory_t in Hin.
    rewrite in_flat_map_option in Hin.
    destruct Hin as (bound & Hinbounds & Hmand).
    unfold activity_mandatory in Hmand.
    specialize (Hvalid bound Hinbounds).
    destruct Hvalid as [Hin Hlbub].
    exists (bound_to_act sol bound).
    unfold activities_at_t. rewrite filter_In.
    rewrite <- and_assoc.
    setoid_rewrite and_comm at 2.
    rewrite and_assoc.
    split; try exact Hin.
    destruct bound as [x' lb ub p u']; simpl in *.
    destruct mandatory_active eqn:Hactive; try easy.
    inversion Hmand; subst; clear Hmand.
    split.
    + unfold act_to_xn. reflexivity.
    + eapply mandatory_active_is_active.
      * exact Hlbub.
      * exact Hactive.
  - unfold bounds_mandatory_t.
    rewrite flat_map_option_as_filter_map with (d := (""%string, N0)).
    apply NoDup_map_inv with (f := fst).
    apply nodup_key with (a_k := b_x).
    + apply nodup_map_filter.
      exact Hunique. 
    + intros act. unfold option_map_default, filter_f_option.
      rewrite filter_In.
      destruct activity_mandatory as [[x n]|] eqn:Hmand; try easy.
      intros [Hin _].
      unfold activity_mandatory in Hmand.
      destruct act; destruct mandatory_active; try easy; simpl in *.
      inversion Hmand; subst; reflexivity.
Qed.
  
Lemma resource_profile_contradiction constr sol bounds :
  Cumulative constr sol
    ->
  unique_bounds bounds
    ->
  valid_bounds bounds constr sol
    -> 
  forall times,
    times <> nil
      ->
    resource_profile (capacity constr) bounds times <> nil.
Proof.
  intros Hcumul Hunique Hvalid.
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
  enough (bounds_mandatory_usage_t bounds t <= usage_sum (activities_at_t (activity_list constr sol) t))%N by lia.
  clear -Hunique Hvalid.
  unfold bounds_mandatory_usage_t, usage_sum.
  apply xn_sum_sub_list.
  apply bounds_mandatory_t_sublist; assumption.
Qed.

Definition valid_profile capacity bounds (profile : list N) (t_min t_max : Z) :=
  length profile = Z.to_nat (t_max - t_min + 1)
    /\
  forall t,
    t_min <= t <= t_max
      ->
    Some (nth_z t profile t_min N0) = resource_profile_t capacity bounds t.

Lemma can_schedule_activity_with_profile_valid constr sol bounds :
  Cumulative constr sol
    ->
  unique_bounds bounds
    ->
  valid_bounds bounds constr sol
    ->
  forall bound profile,
    In bound bounds
      ->
    valid_profile (capacity constr) bounds profile (b_lb bound) (b_ub bound + Z.of_N (b_p_time bound) - 1) 
      ->
    can_schedule_activity_with_profile bound profile = true.
Proof.
  intros Hcumul Hunique Hvalid.
  intros bound profile Hinbounds.
  intros Hprofile_valid.
  unfold can_schedule_activity_with_profile.
  apply exists_run_then_n_true.
  remember (sol (b_x bound)) as start.
  assert (b_lb bound <= start <= b_ub bound).
  { specialize (Hvalid bound Hinbounds).
    subst start. unfold bound_to_act in Hvalid.
    destruct bound. simpl in *.
    lia. } 
  exists (Z.to_nat (start - b_lb bound)).
  unfold profile_to_active_list.
  destruct Hprofile_valid as [Hprofile_len Hprofile_valid].
  apply run_at_z_map with (d := N0).
  - rewrite Hprofile_len. lia.
  - clear Hprofile_len.
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
    subst start.
    destruct mandatory_active eqn:Hmand.
    { reflexivity. }
    rewrite <- not_true_iff_false in Hcapbounds.
    rewrite N.ltb_lt in Hcapbounds.
    assert (bounds_mandatory_usage_t bounds t <= capacity constr)%N by lia; clear Hcapbounds.
    rewrite N.leb_le.
    enough (bounds_mandatory_usage_t bounds t + (b_usage bound) <= capacity constr)%N by lia.
    specialize (Hcumul t).
    enough (bounds_mandatory_usage_t bounds t + (b_usage bound) <= usage_sum (activities_at_t (activity_list constr sol) t))%N by lia.
    clear H0 Hcumul H.
    unfold bounds_mandatory_usage_t, usage_sum.
    apply xn_sum_add_le with (x := (b_x bound)).
    + apply bounds_mandatory_t_sublist; assumption.
    + clear -Hunique Hinbounds Hmand.
      unfold bounds_mandatory_t.
      rewrite in_flat_map_option.
      unfold activity_mandatory.
      intros (bound' & Hin' & Hdef').
      destruct mandatory_active eqn:Hmand' in Hdef'; try discriminate.
      inversion Hdef'; clear H1; rename H0 into Hx;
      clear Hdef'.
      apply nodup_map with (l := bounds) in Hx;
      try assumption.
      subst bound'. rewrite Hmand' in Hmand.
      discriminate Hmand.
    + rewrite in_map_iff.
      specialize (Hvalid bound Hinbounds) as Hbound.
      exists (bound_to_act sol bound).
      split.
      * reflexivity.
      * unfold activities_at_t.
        rewrite filter_In.
        split; try apply Hbound.
        unfold is_active_at, bound_to_act; simpl.
        lia.
Qed.

Lemma resource_profile_valid constr sol bounds :
  Cumulative constr sol
    ->
  unique_bounds bounds
    ->
  valid_bounds bounds constr sol
    ->
  forall profile t_min t_max,
    profile = resource_profile (capacity constr) bounds (range_rev t_min t_max)
      ->
    profile <> nil
      ->
    valid_profile (capacity constr) bounds profile t_min t_max.
Proof.
  intros Hcumul Hunique Hvalid.
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
  unique_bounds bounds
    ->
  valid_bounds bounds constr sol
    ->
  forall bound,
    In bound bounds
      ->
    cannot_schedule_activity (capacity constr) bounds bound = false.
Proof.
  intros Hcumul Hunique Hvalid.
  intros bound Hinbounds.
  unfold cannot_schedule_activity.
  pose proof Hvalid as Hvalid'.
  specialize (Hvalid' bound Hinbounds) as [Hinacts Hactbounds].
  destruct resource_profile eqn:Hprofile.
  { exfalso. apply resource_profile_contradiction with (sol := sol) in Hprofile; try assumption.
    apply act_bound_p_ge_1 in Hinacts.
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
  - exact Hunique.
  - exact Hvalid.
  - exact Hinbounds.
  - apply resource_profile_valid with (sol := sol);
    try assumption.
    subst profile. reflexivity.
Qed.

Lemma checker_cumulative_eq_true :
  forall fact sol constr,
  cumulative_decide constr sol = true
  -> cumulative_checker fact constr = true
  -> inference_valid sol fact.
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
  apply inferred_cumulative_bounds_unique in Hbounds as Hunique.
  clear Hboundsnnil.
  intros Hvalid Hprop_bound.
  reflect_rewrite (cumulative_decides constr sol) in Hcumul.
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
    + exact Hunique.
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
  Is_true (cumulative_decide constr sol)
  -> Is_true (cumulative_checker fact constr)
  -> inference_valid sol fact.
Proof.
  intros fact sol constr.
  intros H1 H2.
  apply Is_true_eq_true in H1, H2.
  apply checker_cumulative_eq_true with (constr := constr);
  assumption.
Qed.

Open Scope string.

(* Mandatory conflict *)    
Compute 
  let constr := build_cumulative 
    (
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 3%N; def_u := 1%N; |} ::
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
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 1%N; def_u := 1%N; |} ::
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
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 1%N; def_u := 1%N; |} ::
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
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 1%N; def_u := 1%N; |} ::
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
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 1%N; def_u := 1%N; |} ::
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
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 2%N; def_u := 1%N; |} ::
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
      {| def_x := "x"; def_p := 4%N; def_u := 1%N; |} ::
      {| def_x := "y"; def_p := 2%N; def_u := 1%N; |} ::
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
