
Require Import Coq.Logic.FinFun.
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
Import Utility.ZRange2.
Require Import Checker.Domain.
Require Import Checker.DomainVar.
Require Import Checker.Deduction.

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
  match bound with
  | mkBound x _ _ p u =>
    mkAct x (sol x) p u
  end.

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
      * repeat decide equality.
      * exact String.string_dec.
      * exact H.
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
  match bound with
  | mkBound x lb ub p u =>
    if mandatory_active lb ub p t
      then Some (x, u)
      else None
  end.

Definition bounds_mandatory_t (bounds : list ActivityBound) (t : Z) := flat_map_option (activity_mandatory t) bounds.

Definition bounds_mandatory_usage_t (bounds : list ActivityBound) (t : Z) :=
  xn_sum (bounds_mandatory_t bounds t).

Definition resource_profile_t (capacity : N) (bounds : list ActivityBound) (t : Z) : option N :=
  let mand_usage := bounds_mandatory_usage_t bounds t in
  if (capacity <? mand_usage)%N
    then None
    else Some (capacity - mand_usage)%N.

Definition resource_profile (capacity : N) (bounds : list ActivityBound) (times : list Z) : list N :=
  (* TODO: see if we can get rid of this rev... *)
  rev (map_valid (resource_profile_t capacity bounds) times nil).

Definition check_can_be_active (act_bound : ActivityBound) (usage_left_t : N) (t : Z) : bool :=
  match act_bound with
  | mkBound _ lb ub p u =>
    if mandatory_active lb ub p t then true else 
      (u <=? usage_left_t)%N
  end.

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
  let times := range bound.(b_lb) (bound.(b_ub) + Z.of_N (bound.(b_p_time)) - 1) in
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
  | (bounds, Some prop_bound) =>
    cannot_schedule_activity (capacity constraint) bounds prop_bound
  | (bounds, None) =>
    (* Try to find a mandatory conflict on the full time range *)
    if resource_profile_full (capacity constraint) bounds
      then true
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
  sub_list xn_eq_dec (bounds_mandatory_t bounds t)
    (map act_to_xn
      (activities_at_t (activity_list constr sol)
        t)).
Proof.
  intros Hunique Hvalid. intros t.
  apply sub_list_if_in_nodup.
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
    destruct bound as [x' lb ub p u'].
    destruct mandatory_active eqn:Hactive; try easy.
    inversion Hmand; subst; clear Hmand.
    split.
    + unfold act_to_xn. reflexivity.
    + simpl in *.
      eapply mandatory_active_is_active.
      * exact Hlbub.
      * exact Hactive.
  - unfold bounds_mandatory_t.
    rewrite flat_map_option_as_filter_map with (d := (""%string, N0)).
    apply NoDup_map_inv with (f := fst).
    apply nodup_key with (a_k := b_x).
    + apply nodup_map_filter.
      * repeat decide equality.
      * exact String.string_dec.
      * exact Hunique. 
    + intros act. unfold option_map_default, filter_f_option.
      rewrite filter_In.
      destruct activity_mandatory as [[x n]|] eqn:Hmand; try easy.
      intros [Hin _].
      unfold activity_mandatory in Hmand.
      destruct act; destruct mandatory_active; try easy.
      inversion Hmand; subst; reflexivity.
Qed.
  
Lemma resource_profile_contradiction constr sol bounds :
  Cumulative constr sol
    ->
  unique_bounds bounds
    ->
  valid_bounds bounds constr sol
    -> 
  forall p_start p_end,
    p_start <= p_end
      ->
    resource_profile (capacity constr) bounds (range p_start p_end) <> nil.
Proof.
  intros Hcumul Hunique Hvalid.
  intros p_start p_end Hstartend.
  unfold resource_profile.
  intros Hmap_valid.
  rewrite nil_rev in Hmap_valid.
  apply map_valid_nil_ex_none in Hmap_valid.
  2: { now rewrite range_cons. }
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

Open Scope nat_scope.
Lemma unique_determines (bounds : list ActivityBound) :
  unique_bounds bounds
    ->
  forall bound bound',
    In bound bounds
      ->
    In bound' bounds
      ->
    b_x bound = b_x bound'
      ->
    bound = bound'.
Proof.
  intros Hunique bound bound' Hin Hin' Hx_eq.
  assert (forall (x y : ActivityBound), {x = y} + {x <> y}) by repeat decide equality.
  destruct (H bound bound') as [Heq | Hneq].
  { exact Heq. }
  exfalso.
  unfold unique_bounds in Hunique.
  apply in_split in Hin.
  destruct Hin as (l1 & l2 & Hbounds).
  rewrite Hbounds in Hin'.
  rewrite Hbounds in Hunique.
  rewrite map_app in Hunique; simpl in Hunique.
  apply NoDup_remove in Hunique.
  assert (In bound' l1 \/ In bound' l2) as Hboundl1l2.
  { rewrite in_app_iff in Hin'.
    destruct Hin' as [Hin' | Hin'].
    - left; assumption.
    - right. now destruct Hin'. }
  destruct Hunique as [_ Hnin].
  apply Hnin.
  rewrite in_app_iff.
  destruct Hboundl1l2 as [Hin1 | Hin2].
  - left. rewrite in_map_iff.
    now exists bound'.
  - right. rewrite in_map_iff.
    now exists bound'.
Qed.


Open Scope Z_scope.
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
    length profile = Z.to_nat (b_ub bound + Z.of_N (b_p_time bound) - b_lb bound)
      ->
    (forall t,
      b_lb bound <= t < b_ub bound + Z.of_N (b_p_time bound)
        ->
      Some (nth_z t profile (b_lb bound) N0) = resource_profile_t (capacity constr) bounds t
    )
      ->
    can_schedule_activity_with_profile bound profile = true.
Proof.
  intros Hcumul Hunique Hvalid.
  intros bound profile Hinbounds.
  intros Hprofile_len Hprofile_valid.
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
  apply run_at_z_map with (d := N0).
  - lia.
  - clear Hprofile_len.
    intros t t_usage.
    intros Ht'.
    assert (start <= t < start + Z.of_N (b_p_time bound)) as Ht by lia; clear Ht'.
    assert (b_lb bound <= t < b_ub bound + Z.of_N (b_p_time bound)) as Htbounds by lia.
    specialize (Hprofile_valid t Htbounds); clear Htbounds.
    intros Htusage.
    rewrite Htusage in Hprofile_valid; clear Htusage.
    unfold resource_profile_t in Hprofile_valid.
    destruct (capacity constr <? bounds_mandatory_usage_t bounds t)%N eqn:Hcapbounds; try discriminate Hprofile_valid.
    inversion Hprofile_valid; subst t_usage; clear Hprofile_valid.
    pose proof Hvalid as Hvalid'.
    unfold check_can_be_active.
    destruct bound as [x lb ub p u]; simpl in *.
    subst start.
    destruct (mandatory_active lb ub p t) eqn:Hmand.
    { reflexivity. }
    rewrite <- not_true_iff_false in Hcapbounds.
    rewrite N.ltb_lt in Hcapbounds.
    assert (bounds_mandatory_usage_t bounds t <= capacity constr)%N by lia; clear Hcapbounds.
    rewrite N.leb_le.
    enough (bounds_mandatory_usage_t bounds t + u <= capacity constr)%N by lia.
    specialize (Hcumul t).
    enough (bounds_mandatory_usage_t bounds t + u <= usage_sum (activities_at_t (activity_list constr sol) t))%N by lia.
    unfold bounds_mandatory_usage_t, usage_sum.
    apply xn_sum_add_le with (x := x).
    + apply bounds_mandatory_t_sublist; assumption.
    + unfold bounds_mandatory_t.
      rewrite in_flat_map_option.
      intros (bound' & Hin & Hmandatory).
      remember (mkBound x lb ub p u) as bound.
      assert (b_x bound = b_x bound') as Hbxbx'.
      { unfold activity_mandatory in Hmandatory.
        destruct bound'. destruct mandatory_active in Hmandatory; try discriminate Hmandatory.
        inversion Hmandatory. subst. reflexivity. }
      specialize (unique_determines bounds Hunique bound bound' Hinbounds Hin Hbxbx') as Hbb'.
      subst bound'.
      enough (mandatory_active lb ub p t = true) as Htrue.
      { rewrite Htrue in Hmand. discriminate Hmand. }
      clear Hmand.
      unfold activity_mandatory in Hmandatory.
      rewrite Heqbound in Hmandatory.
      destruct mandatory_active eqn:Hmand in Hmandatory.
      * exact Hmand.
      * discriminate Hmandatory. 
    + rewrite in_map_iff.
      remember (mkBound x lb ub p u) as bound.
      specialize (Hvalid' bound Hinbounds) as Hbound.
      exists (mkAct x (sol x) p u).
      split.
      * reflexivity.
      * unfold activities_at_t.
        rewrite filter_In.
        subst bound. unfold bound_to_act in Hbound; simpl in *.
        split; try easy.
        unfold is_active_at.
        lia.
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
    lia. }
  (* I don't like the below manipulation, must be way to make things cleaner here... *)
  unfold resource_profile in Hprofile.
  remember (range (b_lb bound) (b_ub bound + Z.of_N (b_p_time bound) - 1)) as bound_range.
  remember (n :: l) as profile.
  assert (profile <> nil) as Hprofilennil.
  { subst profile. now intros Hnl. }
  clear Heqprofile n l.
  rewrite negb_false_iff.
  apply can_schedule_activity_with_profile_valid with (constr := constr) (sol := sol) (bounds := bounds).
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - clear -Hactbounds Heqbound_range Hprofilennil Hprofile.
    subst profile.
    rewrite length_rev.
    rewrite nil_rev in Hprofilennil.
    rewrite map_valid_as_map with (d := N0).
    + rewrite app_nil_r.
      rewrite length_rev.
      rewrite length_map.
      subst bound_range.
      rewrite length_range. lia.
    + exact Hprofilennil.
  - intros t Ht.
    symmetry in Hprofile.
    remember (rev profile) as profile_rev.
    pose proof Heqprofile_rev as Hprofile_rev.
    rewrite Hprofile in Heqprofile_rev; clear Hprofile.
    rewrite rev_involutive in Heqprofile_rev.
    assert (profile_rev <> nil) as Hprofile_rev_nnil.
    { rewrite Hprofile_rev. rewrite nil_rev.
      exact Hprofilennil. }
    apply map_valid_spec with (d := N0) in Heqprofile_rev; try assumption. destruct Heqprofile_rev as [Hprofile Hsome].
    rewrite Hprofile_rev in Hprofile.
    assert (forall l', rev profile = rev l' -> profile = l').
    { intros l'. intros Hrev.
      rewrite <- rev_involutive.
      rewrite <- rev_involutive at 1.
      f_equal. exact Hrev. }
    apply H in Hprofile; clear H Hprofile_rev Hprofile_rev_nnil profile_rev.
    assert (In t bound_range) as Htrange.
    { clear -Heqbound_range Ht.
      subst bound_range.
      rewrite <- in_range. lia. }
    specialize (Hsome t Htrange).
    destruct resource_profile_t as [t_usage'|] eqn:Hprofilet; try easy; clear Hsome.
    subst profile; clear Hprofilennil.
    f_equal.
    rewrite nth_z_spec; try lia.
    rewrite <- map_nth_len_lt with (d := 0).
    2: { subst bound_range. rewrite length_range. lia. }
    unfold option_map_default.
    rewrite Heqbound_range.
    rewrite <- nth_z_spec; try lia.
    rewrite range_spec; try lia.
    rewrite Hprofilet.
    reflexivity.
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
  destruct prop_bound_opt as [prop_bound|].
  {
    unfold valid_prop_bound in Hprop_bound.
    enough (cannot_schedule_activity (capacity constr) bounds prop_bound = false).
    { rewrite H in Hchecked. discriminate Hchecked. }
    apply cannot_schedule_activity_valid with (sol := sol).
    - exact Hcumul.
    - exact Hunique.
    - exact Hvalid.
    - exact Hprop_bound.
  }
  {
    unfold resource_profile_full in Hchecked.
    destruct (bounds_times bounds) as [t_min t_max] eqn:Htimes.
    destruct resource_profile eqn:Hprofile.
    + enough (resource_profile (capacity constr) bounds (range t_min t_max) <> nil).
      { rewrite Hprofile in H. contradiction. }
      apply resource_profile_contradiction with (sol := sol);
      try assumption.
      eapply bounds_times_le.
      * exact Hvalid.
      * exact Htimes.
    + rewrite existsb_exists in Hchecked.
      destruct Hchecked as (bound & Hinbounds & Hcannot).
      enough (cannot_schedule_activity (capacity constr) bounds bound = false).
      { rewrite H in Hcannot. discriminate Hcannot. }
      apply cannot_schedule_activity_valid with (sol := sol);
      assumption.
  }
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
