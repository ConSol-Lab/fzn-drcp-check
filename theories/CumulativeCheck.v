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

(** The main object of interest: represents an activity with (inclusive) lower and upper bounds for its starting time, as well as its other parameters, processing time and resource usage. Note that it includes no mention of a name, because Var can be a constant without a name. *)
Record BoundedActivity := mkBoundAct {
  b_lb : Z;
  b_ub : Z;
  b_p_time : N;
  b_usage : N;
}.

(** The below functions allow constructing a list of BoundedActivity's from a fact and a constraint. *)

Definition lb_ub_from_act_dom (activity : Activity) (domains : smap.t Domain) : option (Z * Z) :=
  match (activity_start activity) with
  | const value => Some (value, value)    
  | var_name x =>
    match smap.find x domains with
    | None => None
    | Some dom => lb_ub_from_dom dom 
    end
  end.

Definition act_dom_to_bounded_act (dom : Domain) (activity : Activity) : option BoundedActivity :=
  match lb_ub_from_dom dom with
  | Some (lb, ub) => Some (mkBoundAct lb ub (activity_duration activity) (activity_usage activity))
  | None => None
  end.

Definition act_doms_to_bounded_acts (domains : smap.t Domain) (activity : Activity) : option BoundedActivity :=
  match lb_ub_from_act_dom activity domains with
  | Some (lb, ub) => Some (mkBoundAct lb ub (activity_duration activity) (activity_usage activity))
  | None => None
  end.

Definition activity_match (x : string) (activity : Activity) : bool :=
  match (activity_start activity) with
  | const value => false
  | var_name x' => (x =? x')%string
  end.

Definition inferred_cumulative_activity_bounds (constr : CumulativeConstraint) (fact : ProofFact) : (list BoundedActivity * option BoundedActivity) :=
  match infer_domains fact with
  | None => (nil, None)
  | Some (domains, prop_var) =>
    let bounded_activities := flat_map_option (act_doms_to_bounded_acts domains) constr.(activities) in
    match prop_var with
    | None => (bounded_activities, None) 
    (* The below could probably be made more efficient. *)
    | Some prop_var =>
      match find (activity_match prop_var) constr.(activities) with
      | None => (bounded_activities, None)
      | Some prop_act =>
        match smap.find prop_var domains with
        | None => (bounded_activities, None)
        | Some prop_dom => (bounded_activities, act_dom_to_bounded_act prop_dom prop_act)
        end
      end
    end
  end.

(** Because we do not have a name in a bounded activity because activities can also have a constant value for their starting time instead of a variable, we define bounds to be valid by requiring any addition of a bound to be accompanied by a matching activity. We also allow adding activities without bounds, because maybe an activity is not mentioned in the fact but we still want to work with the full list of activities (as that makes proving things easier). *)
Inductive valid_bounds (sol : string -> Z) : list Activity -> list BoundedActivity -> Prop :=
  | valid_bounds_nil : valid_bounds sol nil nil
  | valid_bounds_bound (act : Activity) (acts : list Activity) (bound : BoundedActivity) (bounds: list BoundedActivity) 
    (Hstart : bound.(b_lb) <= evaluate act.(activity_start) sol <= bound.(b_ub)) 
    (Husage : bound.(b_usage) = act.(activity_usage)) (Hduration : bound.(b_p_time) = act.(activity_duration)) 
    (H : valid_bounds sol acts bounds) 
      : valid_bounds sol (act :: acts) (bound :: bounds)
  | valid_bounds_nobound (act : Activity) (acts : list Activity) (bounds : list BoundedActivity) (H : valid_bounds sol acts bounds) : valid_bounds sol (act :: acts) bounds
  .

Lemma valid_bounds_act_left sol :
  forall acts bound bounds,
    valid_bounds sol acts (bound :: bounds)
      ->
    exists acts_l acts_r act,
      acts = acts_l ++ act :: acts_r
        /\
      valid_bounds sol acts_r bounds
        /\
      bound.(b_lb) <= evaluate act.(activity_start) sol <= bound.(b_ub) 
        /\
      bound.(b_usage) = act.(activity_usage) 
        /\
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

(** This is the important lemma that allows us to extract a matching activity for a bound and isolate the remaining bounds and activities, which are then still valid.  *)
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

Definition valid_prop_bound (bound : option BoundedActivity) (bounds : list BoundedActivity) :=
  match bound with
  | Some bound => In bound bounds
  | None => True
  end.

Definition default_bound := mkBoundAct Z0 Z0 N0 N0.

Lemma inferred_cumulative_activity_bounds_prop_bound_valid constr fact bounds prop_bound_opt :
  inferred_cumulative_activity_bounds constr fact = (bounds, prop_bound_opt)
    ->
  valid_prop_bound prop_bound_opt bounds.
Proof.
  unfold inferred_cumulative_activity_bounds.
  destruct infer_domains as [(doms & maybe_prop_var)| ] eqn:Hinfer.
  2: { intros Hbounds; now inversion Hbounds. }
  destruct maybe_prop_var as [prop_var|] eqn:Hprop_var.
  2: { intros Hbounds; now inversion Hbounds. }
  subst maybe_prop_var; destruct find as [prop_act|] eqn:Hfind.
  2: { intros Hbounds; now inversion Hbounds. }
  destruct smap.find as [prop_dom|] eqn:Hfind_dom.
  2: { intros Hbounds; now inversion Hbounds. }
  intros H; inversion H; clear H.
  destruct act_dom_to_bounded_act as [prop_bound|] eqn:Hprop_bound; try reflexivity; subst prop_bound_opt; subst bounds.
  apply find_some in Hfind.
  unfold valid_prop_bound.
  rewrite in_flat_map_option.
  exists prop_act.
  destruct Hfind as [Hin Hmatch].
  split.
  - exact Hin.
  - unfold activity_match in Hmatch.
    destruct activity_start as [x|] eqn:Hstart; try easy.
    rewrite String.eqb_eq in Hmatch; subst x.
    unfold act_doms_to_bounded_acts.
    unfold act_dom_to_bounded_act in Hprop_bound.
    destruct lb_ub_from_dom as [(lb & ub)|] eqn:Hlb_ub_dom; try easy. inversion Hprop_bound; clear Hprop_bound H0.
    unfold lb_ub_from_act_dom.
    rewrite Hstart.
    rewrite Hfind_dom.
    rewrite Hlb_ub_dom.
    reflexivity.
Qed.

Lemma inferred_cumulative_activity_bounds_spec constr fact bounds prop_bound_opt :
  forall sol,
    inferred_cumulative_activity_bounds constr fact = (bounds, prop_bound_opt)
      ->
    ~ valid_bounds sol constr.(activities) bounds
      ->
    fact_valid sol fact.
Proof.
  intros sol Hinfer_bounds Hnvalid.
  unfold inferred_cumulative_activity_bounds in Hinfer_bounds.
  destruct infer_domains as [[doms prop_var_opt]|] eqn:Hinfer.
  2: { 
    inversion Hinfer_bounds; subst. exfalso. apply Hnvalid.
    remember (activities constr) as activities; clear.
    induction activities as [|act acts IH].
    - apply valid_bounds_nil.
    - apply valid_bounds_nobound. exact IH.
  }
  apply infer_domains_correct with (doms := doms) (xconsq := prop_var_opt); try assumption.
  intros Hdoms_hold.
  remember (flat_map_option
    (act_doms_to_bounded_acts doms)
    (activities constr)) as bounds'.
  assert (infer_domains fact = Some (doms, prop_var_opt) -> sol_in_doms sol doms -> valid_bounds sol constr.(activities) bounds') as H.
  {
    clear -Heqbounds'. intros Hinfer Hdoms_hold.
    subst bounds'.
    remember (activities constr) as activities.
    clear Heqactivities.
    induction activities as [| act activities IH].
    - simpl. apply valid_bounds_nil.
    - simpl. destruct (act_doms_to_bounded_acts doms act) as [bound|] eqn:Hto_bound.
      + simpl. 
        unfold act_doms_to_bounded_acts in Hto_bound.
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
    apply Hnvalid.
    apply H.
    - apply Hinfer.
    - apply Hdoms_hold.
  }
  destruct prop_var_opt as [prop_var |] eqn:Hprop_var.
  {
    destruct find as [prop_act |] eqn:Hfind.
    2: { apply Hbound_opt_none; inversion Hinfer_bounds; reflexivity. }
    destruct smap.find as [prop_dom |] eqn:Hfind_dom.
    2: { apply Hbound_opt_none; inversion Hinfer_bounds; reflexivity. }
    inversion Hinfer_bounds. rewrite H1 in Heqbounds'; subst bounds' prop_bound_opt prop_var_opt; clear Hinfer_bounds.
    apply Hnvalid.
    apply H.
    - exact Hinfer.
    - exact Hdoms_hold.
  }
  {
    apply Hnvalid.
    inversion Hinfer_bounds; rewrite H1 in Heqbounds';
    subst bounds'.
    apply H.
    - exact Hinfer.
    - exact Hdoms_hold.
  }
Qed. 


(* Lemma inferred_cumulative_activity_valid constr fact bounds prop_bound_opt :
  forall sol,
    fact_valid sol fact
      ->
    bounds <> nil
      ->
    inferred_cumulative_activity_bounds constr fact = (bounds, prop_bound_opt)
      ->
    valid_bounds sol constr.(activities) bounds.
Proof.
  intros sol.
  intros Hvalid Hnnil.
  unfold inferred_cumulative_activity_bounds.
  destruct infer_domains as [(doms & maybe_prop_var) | ] eqn:Hinfer.
  2: { intros H; inversion H; now subst. }
  intros H.
  assert (bounds = flat_map_option
    (act_doms_to_bounded_acts doms)
    (activities constr)) as Hbounds.
  {
    destruct maybe_prop_var.
    - destruct find.
      + destruct smap.find; now inversion H.
      + now inversion H.
    - now inversion H.
  }
  clear H.
 *)


Definition mandatory_active (lb : Z) (ub : Z) (p_time : N) (t : Z) :=
  (ub <=? t) && (t <? (lb + (Z.of_N p_time))).

Definition activity_mandatory (t : Z) (bound : BoundedActivity) : option N :=
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

(* Definition bounds_mandatory_t (bounds : list BoundedActivity) (t : Z) := flat_map_option (activity_mandatory t) bounds.
 *)
Definition bounds_mandatory_usage_t (bounds : list BoundedActivity) (t : Z) :=
  n_sum (flat_map_option (activity_mandatory t) bounds).

Definition resource_profile_t (capacity : N) (bounds : list BoundedActivity) (t : Z) : option N :=
  let mand_usage := bounds_mandatory_usage_t bounds t in
  if (capacity <? mand_usage)%N
    then None
    else Some (capacity - mand_usage)%N.

(** `resource_profile` expects times in reverse order, so e.g. computed using `range_rev`, as map_valid reverses the order in order to allow it to be tail-call recursive. *)
Definition resource_profile (capacity : N) (bounds : list BoundedActivity) (times : list Z) : list N :=
  map_valid (resource_profile_t capacity bounds) times nil.

Definition check_can_be_active (bound : BoundedActivity) (usage_left_t : N) (t : Z) : bool :=
  if mandatory_active (b_lb bound) (b_ub bound) (b_p_time bound) t then true else 
    (b_usage bound <=? usage_left_t)%N.

(** Given a function that takes a Z as its second argument, map a list of A's and provide an increasing value as the second argument, incremented by 1 for each value starting at starting point `z`. Example: Given a list [a, b, c] and start value -1, it will return [f a -1, f b 0, f b 1]. Used in practice when you have a list of timepoints that you map, but then do not want to again store the timepoint with the result (because it is needed in a later step or proof). *)
Fixpoint z_map {A B} (f : A -> Z -> B) (l : list A) (z : Z) :=
  match l with
  | nil => nil
  | a :: l' => (f a z) :: z_map f l' (z + 1)
  end.

(** We can write z_map in terms of map, range and combine by first combining the original list l with the range and then calling map on it with f. This allows us to use well-known facts about map, combine and range instead of having to prove all of these for z_map. *)
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

(** We now give a specification that is easier to work with. Given that we provide an n that corresponds to some integer that the list is combined with by z_map and that the corresponding element in l is equal to some value a, then the nth value (in the nth_z sense) is equal to applying f to a with n as the second argument. *)
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
    rewrite nth_indep with (d' := f a Z0).
    2: { rewrite length_z_map. lia. }
    remember (Z.of_nat (length l) + z - 1) as e. 
    assert (z <= e) as Hze by lia.
    rewrite z_map_as_map.
    rewrite <- map_nth_len_lt with (d := (a, 0)).
    2: { rewrite length_combine. rewrite length_range. lia. }
    rewrite combine_nth.
    2: { rewrite length_range. lia. }
    rewrite nth_indep with (d' := d); try lia.
    rewrite Ha.
    rewrite range_nth_spec by lia.
    simpl. 
    f_equal.
    lia.
  - lia.
Qed.

(** We now give a condition for a run of a certain length (defined with nth) in terms of nth_z. The main benefit of using nth_z is that we can work more directly with the actual time instead of the time's index in the list of times we work with. *)
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

(** Using z_map gives us a condition for which a run starting at some particular value k has size at least n, namely if all values corresponding to some interval evaluate to true. *)
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

Definition profile_to_active_list (act_bound : BoundedActivity) (profile : list N) :=
  z_map (check_can_be_active act_bound) profile (b_lb act_bound).

(** Given a profile, see if it is possible to schedule an activity somewhere by checking if there is a space at least the size of the activity's duration where the activity can be active given the profile. *)
Definition can_schedule_activity_with_profile (bound : BoundedActivity) (profile : list N) :=
  has_n_true (N.to_nat bound.(b_p_time)) (profile_to_active_list bound profile).

(** Given a capacity, a list of bounds and a particular bound, first checks whether there is a time conflict somewhere between the bound's earliest starting time and latest completion time. If no such time conflict exists, it checks for an activity conflict for that particular bound by checking if it cannot be scheduled anywhere in its bounds. *)
Definition check_conflict_for_bound (capacity : N) (bounds : list BoundedActivity) (bound : BoundedActivity) :=
  let times := range_rev bound.(b_lb) (bound.(b_ub) + Z.of_N (bound.(b_p_time)) - 1) in
  match resource_profile capacity bounds times with
  | nil => true
  | profile => negb (can_schedule_activity_with_profile bound profile)
  end.

(** Compute the minimum lower bound and maximum upper bound of a list of bounds. *)
Definition bounds_times (bounds : list BoundedActivity) :=
  let t_min := min_l (map b_lb bounds) in
  let t_max := max_l (map b_ub bounds) in
  (* We don't include the processing time because they will have been already conflicting at the latest start time *)
  (t_min, t_max).

(** Whether every activity of the constraint lasts at least one time unit. *)
Definition nonzero_duration a :=
  (a.(activity_duration) >= 1)%N.

(** All bounds in a list of bounds have some basic facts known about them. *)
Lemma valid_bounds_properties constr sol bounds : 
  Forall nonzero_duration constr.(activities)
    ->
  valid_bounds sol constr.(activities) bounds
    ->
  Forall (fun bound => 
    (bound.(b_p_time) >= 1)%N
      /\
    bound.(b_lb) <= bound.(b_ub)
  ) bounds.
Proof.
  intros Hdur Hvalid.
  rewrite Forall_forall. intros bound Hin.
  apply in_split in Hin.
  destruct Hin as (bounds_l & bounds_r & Hbounds).
  apply valid_bound_matching_activity with (sol := sol) (acts := constr.(activities)) in Hbounds.
  2: { exact Hvalid. }
  destruct Hbounds as (acts_l & act & acts_r & H).
  split.
  - rewrite Forall_forall in Hdur.
    specialize (Hdur act).
    assert (In act (activities constr)) as Hin.
    { destruct H as (H & _). rewrite H.
      rewrite in_app_iff. right. simpl.
      left. reflexivity. }
    apply Hdur in Hin; unfold nonzero_duration in Hin.
    lia.
  - lia.
Qed.

(** Using the fact that every individual lower bound is less than or equal to upper bound, means that the minimum time will also be less than or equal to the max time of all bounds. *)
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

(* Given a capacity and a list of activity bounds, checks for a time conflict using the resource profile over the entire horizon of the activity bounds: i.e., whether the profile overflows the capacity somewhere. *)
Definition check_time_conflict_horizon (capacity : N) (bounds : list BoundedActivity) :=
  let (t_min, t_max) := bounds_times bounds in
  let times := range t_min t_max in
  match resource_profile capacity bounds times with
  | nil => true
  | _ => false
  end.

(** Zero-duration activities are never active, so dropping them preserves the semantics (`ensure_nonzero_equiv`).  `check_conflict_for_bound` assumes there are no such activities left. *)
Definition ensure_nonzero_duration constr : CumulativeConstraint :=
  {| capacity := constr.(capacity);
     activities := activities_pos_duration constr.(activities) |}.

(** A zero-duration activity is never active. *)
Lemma zero_duration_never_active (sol : Assignment) :
  forall t act,
    act.(activity_duration) = 0%N
      ->
    is_active_at sol t act = false.
Proof.
  unfold is_active_at; intros t act ->.
  rewrite andb_false_iff, Z.ltb_ge, Z.leb_gt.
  lia.
Qed.

Lemma usage_at_timepoint_cons (sol : Assignment) :
  forall t act acts,
    usage_at_timepoint sol t (act :: acts)
      = ((if is_active_at sol t act then act.(activity_usage) else 0) + usage_at_timepoint sol t acts)%N.
Proof.
  unfold usage_at_timepoint; intros; simpl.
  destruct is_active_at; simpl.
  all: rewrite ?n_fold_is_n_sum; lia.
Qed.

(** Dropping zero-duration activities does not change the usage at any timepoint. *)
Lemma usage_at_timepoint_pos_duration (sol : Assignment) :
  forall t acts,
    usage_at_timepoint sol t (activities_pos_duration acts)
      = usage_at_timepoint sol t acts.
Proof.
  intros t acts.
  unfold activities_pos_duration.
  induction acts as [| act acts IH].
  - reflexivity.
  - cbn [filter].
    destruct (1 <=? _)%N eqn:Hdur; rewrite !usage_at_timepoint_cons.
    + congruence.
    + rewrite (zero_duration_never_active sol t act).
      * rewrite IH; reflexivity.
      * apply N.leb_gt in Hdur; lia.
Qed.

(** Removing zero-length constraints preserves the semantics. *)
Lemma ensure_nonzero_equiv :
  forall constr sol,
    Cumulative constr sol <-> Cumulative (ensure_nonzero_duration constr) sol.
Proof.
  intros constr sol.
  unfold Cumulative, ensure_nonzero_duration; simpl.
  split; intros H t; specialize (H t).
  all: revert H; rewrite usage_at_timepoint_pos_duration.
  all: auto.
Qed.

(* Main possible improvements:
  - Reuse the full resource profile for the cannot schedule
  - Do not retry the right-hand side in the final check_conflict_bound
  - Allow the use of 'hints' to be able to determine at what time there is a profile conflict, or what activity cannot be scheduled (requires changing the proof format)
  - Do not check every timepoint, but instead only profile height changes
*)
Definition cumulative_checker_nonzero (fact : ProofFact) (constraint : CumulativeConstraint) : bool :=
  let (bounds, maybe_bound_rhs) := inferred_cumulative_activity_bounds constraint fact in
  (* First try conflict for the activity from the rhs *)
  let rhs_found_conflict :=
    match maybe_bound_rhs with
    | Some bound_rhs => check_conflict_for_bound (capacity constraint) bounds bound_rhs
    | None => false
    end in
  if rhs_found_conflict then true
  (* Then try to find a time conflict on the resource profile over the entire constraint horizon *)
  else if check_time_conflict_horizon (capacity constraint) bounds then true
  (* Otherwise fallback and try to find a conflict for all activities. Note that it will retry the r.h.s. *)
  else existsb (check_conflict_for_bound (capacity constraint) bounds) bounds.

Definition cumulative_checker (fact : ProofFact) (constraint : CumulativeConstraint) : bool :=
  cumulative_checker_nonzero fact (ensure_nonzero_duration constraint).



Open Scope N_scope.
(** If the bounds were computed in a valid way, the mandatory usage of bounds at some time t should always be less than the usage of all activities active at t. *)
Lemma bounds_mandatory_t_le_usage assignment :
  forall activities bounds,
  valid_bounds assignment activities bounds
    ->
  forall t, 
    bounds_mandatory_usage_t bounds t
      <=
    usage_at_timepoint assignment t activities.
Proof.
  intros activities.
  (** Due to the nature of `valid_bounds` and the fact we cannot easily get the activity associated with a bound because bounds have no name, we use an inductive proof. *)
  induction activities as [| act acts IH].
  { intros bounds Hvalid t.
    inversion Hvalid. subst bounds.
    reflexivity. }
  intros bounds Hvalid t.
  assert (forall act acts, usage_at_timepoint assignment t acts <= usage_at_timepoint assignment t (act :: acts)) as Hact_add.
  { clear. intros act acts.
    unfold usage_at_timepoint. 
    setoid_rewrite n_fold_is_n_sum.
    unfold n_sum. simpl.
    destruct is_active_at.
    - simpl. setoid_rewrite n_sum_add. lia.
    - reflexivity. }
  inversion Hvalid.
  - subst act0 acts0; rename bounds0 into bounds'.
    (* This is the case where there is an added bound corresponding to the added activity. *)
    specialize (IH bounds' H2 t).
    specialize (Hact_add act acts).
    unfold bounds_mandatory_usage_t; simpl.
    destruct activity_mandatory eqn:Hmand.
    2: { simpl. unfold bounds_mandatory_usage_t in IH. lia. }
    pose proof Hmand as Hactive.
    unfold activity_mandatory in Hmand.
    destruct mandatory_active in Hmand; try easy.
    inversion Hmand; subst n; clear Hmand. 
    apply mandatory_active_is_active with (sol := assignment) (act := act) in Hactive.
    * simpl.
      unfold usage_at_timepoint in *.
      rewrite n_fold_is_n_sum in *.
      simpl; rewrite Hactive; simpl.
      unfold n_sum; simpl; setoid_rewrite n_sum_add.
      unfold bounds_mandatory_usage_t in IH.
      lia.
    * exact Hstart.
    * lia.
  - (* This is the case where there is an activity added without a bound. *)
    specialize (IH bounds H2 t).
    specialize (Hact_add act acts).
    lia.
Qed.

(** Given a cumulative constraint, a solution for that constraint and a list of bounds corresponding to that constraint and satisfied by that solution, a resource profile should not overflow and should therefore return a profile. *)
Lemma no_profile_overflow_for_solution constraint assignment bounds :
  Cumulative constraint assignment
    ->
  valid_bounds assignment constraint.(activities) bounds
    -> 
  forall times,
    times <> nil
      ->
    resource_profile (capacity constraint) bounds times <> nil.
Proof.
  intros Hcumul Hvalid.
  intros times Htimesnnil.
  unfold resource_profile.
  (* map_valid is not nil if all inputs return Some. Therefore, if it is nil, there must be some value that returns None, for which we show this cannot be if the constraint is satisfied. *)
  intros Hmap_valid.
  apply map_valid_nil_ex_none in Hmap_valid.
  2: { assumption. }
  destruct Hmap_valid as (t & Ht_in & Hprofile).
  unfold resource_profile_t in Hprofile.
  destruct (capacity constraint <? bounds_mandatory_usage_t bounds t)%N eqn:Hcap.
  2: { discriminate Hprofile. }
  rewrite N.ltb_lt in Hcap.
  specialize (Hcumul t).
  apply bounds_mandatory_t_le_usage with (t := t) in Hvalid. lia.
Qed.

Open Scope Z_scope.
(** For a particular capacity.set of bounds and a minimum and maximum time, a profile is valid if it has the correct length and if for every element corresponding to a particular time, that element is the result of a profile calculation.  *)
Definition valid_profile capacity bounds (profile : list N) (t_min t_max : Z) :=
  length profile = Z.to_nat (t_max - t_min + 1)
    /\
  forall t,
    t_min <= t <= t_max
      ->
    Some (nth_z t profile t_min N0) = resource_profile_t capacity bounds t.

Require Import Permutation.

Open Scope N_scope.
(** We are not actually using this, but it shows the principle we use to prove `can_schedule_activity_with_profile_valid`. *)
Lemma n_sum_map :
  forall (A : Type) (f : A -> N) l1 l2 a,
    sublist l1 l2
      ->
    ~ In a l1
      ->
    In a l2
      ->
    n_sum (map f l1) + (f a) <= n_sum (map f l2).
Proof.
  intros A f l1 l2 a.
  intros Hsub Hnin1 Hin2.
  destruct Hsub as (diff & Hperm).
  apply Permutation_map with (f := f) in Hperm as Hperm_map.
  apply n_sum_perm in Hperm_map.
  rewrite <- Hperm_map.
  apply sublist_one_of with (a := a) in Hperm; try assumption.
  apply in_split in Hperm as Hdiff_split.
  destruct Hdiff_split as (diff_1 & diff_2 & Hdiff).
  rewrite Hdiff. repeat rewrite map_app. repeat rewrite n_sum_app.
  unfold n_sum; simpl; setoid_rewrite n_sum_add.
  lia.
Qed.
  

Open Scope Z_scope.
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
  remember (N.to_nat (b_p_time bound)) as b_duration.
  (* We must show that there are b_duration `true` values in a row in the active list. We can do this by providing an index and showing that the five values starting at that index are all `true`. *)
  (* We know that since sol satisfies cumulative, if we find the activity corresponding to our bound, then the start time of that activity according to sol must be able to be active for its entire duration. *)
  apply exists_run_then_n_true.
  (* Since `sol` satisfies the constraint, for every activity `sol` has a start time and the activity is active for its duration starting from there. So if we get the activity corresponding to the bound, its start time according to `sol` should satisfy our requirement. So first we must get this activity. *)
  apply in_split in Hinbounds.
  destruct Hinbounds as (bounds_l & bounds_r & Hbounds).
  apply valid_bound_matching_activity with (bounds_l := bounds_l) (bounds_r := bounds_r) (bound := bound) in Hvalid.
  2: { exact Hbounds. }
  destruct Hvalid as (acts_l & act & acts_r & Hacts & Hvalid_ex & Hstart & Hbound_u & Hbound_p).
  remember (evaluate (activity_start act) sol) as start.
  (* We need the index, not the exact time, so we remove the profile's minimum time, which is the bound's lower bound as that is how the profile was constructed. *)
  exists (Z.to_nat (start - b_lb bound)).
  unfold profile_to_active_list.
  destruct Hprofile_valid as [Hprofile_len Hprofile_valid].
  (* We can now use that our profile is constructed using z_map. *)
  apply run_at_z_map with (d := N0).
  { rewrite Hprofile_len. lia. }
  clear Hprofile_len.
  (* Now we must show it can indeed be active starting at start up to the end. *)
  intros t profile_value_at_t.
  (* We rewrite the times into something more readable. *)
  intros Ht'.
  assert (start <= t < start + Z.of_N (b_p_time bound)) as Ht by lia; clear Ht'; subst b_duration.
  (* Now we want to use the validity of the profile to get that profile_value_at_t is indeed capacity - mandatory usage at t. *)
  assert (b_lb bound <= t <= b_ub bound + Z.of_N (b_p_time bound) - 1) as Htbounds by lia.
  specialize (Hprofile_valid t Htbounds); clear Htbounds.
  intros Htusage.
  rewrite Htusage in Hprofile_valid; clear Htusage.
  (* resource_profile_t will return None if there is overflow, we want to get the actual computation. *)
  unfold resource_profile_t in Hprofile_valid.
  destruct (capacity constr <? bounds_mandatory_usage_t bounds t)%N eqn:Hcapbounds'; try discriminate Hprofile_valid.
  inversion Hprofile_valid; subst profile_value_at_t; clear Hprofile_valid.
  (* Rewrite Hcapbounds to something more readable. *)
  rewrite <- not_true_iff_false in Hcapbounds'; rewrite N.ltb_lt in Hcapbounds'; assert (bounds_mandatory_usage_t bounds t <= capacity constr)%N as Hcapbounds by lia; clear Hcapbounds'.
  unfold check_can_be_active.
  (* In case the activity is mandatory, clearly it can be active. *)
  destruct mandatory_active eqn:Hmand.
  { reflexivity. }
  (* We now deal with the case where the activity is not mandatory, so it is not part of bounds_mandatory_usage_t, but remember we know it is active at t and sol satisfies the constraint so we must have that the capacity does not overflow if we add the activity's usage. *)
  rewrite N.leb_le.
  enough (bounds_mandatory_usage_t bounds t + (b_usage bound) <= capacity constr)%N by lia.
  specialize (Hcumul t).
  enough (bounds_mandatory_usage_t bounds t + (b_usage bound) <= usage_at_timepoint sol t (activities constr))%N by lia.
  clear Hcumul Hcapbounds.
  (* Ideally we would use n_sum_map, but it is hard to relate the bounds and activities as sublist because we cannot convert bounds -> activities or activities -> bounds. *)
  (* We rewrite bounds_mandatory_usage_t to show it relies only on bounds_l and bounds_r, not bound. *)
  unfold bounds_mandatory_usage_t.
  rewrite Hbounds.
  rewrite flat_map_option_as_filter_map with (d := N0).
  rewrite filter_app. simpl.
  destruct filter_f_option eqn:Hfilter.
  { unfold filter_f_option in Hfilter.
    unfold activity_mandatory in Hfilter.
    now rewrite Hmand in Hfilter. }
  rewrite <- filter_app.
  rewrite <- flat_map_option_as_filter_map.
  (* Now we write usage at timepoint to split the activity corresponding to the bounded activity off from the other activities. *)
  unfold usage_at_timepoint.
  rewrite n_fold_is_n_sum.
  rewrite Hacts. rewrite filter_app. simpl.
  destruct (is_active_at sol t act) eqn:Hactive.
  2: { exfalso. clear -Ht Hactive Heqstart Hbound_p.
    revert Hactive. unfold is_active_at.
    rewrite <- Heqstart.
    rewrite andb_false_iff.
    intros [Hl | Hr]; lia. }
  rewrite map_app. simpl. 
  (* This rewrite is made possible by the Proper instance for permutation in n_sum. *)
  rewrite <- Permutation_middle.
  rewrite <- map_app; rewrite <- filter_app.
  rewrite n_sum_cons.
  apply bounds_mandatory_t_le_usage with (t := t) in Hvalid_ex.
  unfold usage_at_timepoint, bounds_mandatory_usage_t in Hvalid_ex.
  rewrite n_fold_is_n_sum in Hvalid_ex.
  lia.
Qed.


Lemma resource_profile_valid :
  forall capacity bounds profile t_min t_max,
    profile = resource_profile capacity bounds (range_rev t_min t_max)
      ->
    profile <> nil
      ->
    valid_profile capacity bounds profile t_min t_max.
Proof.
  intros capacity bounds profile t_min t_max.
  intros Hprofile Hprofilennil.
  (* In case t_min < t_max, we have an empty profile, so we deal with that case first. *)
  destruct (Z_gt_le_dec t_min t_max) as [Hgt | _].
  { 
    subst profile; unfold range_rev, valid_profile.
    assert (Z.to_nat (t_max - t_min + 1) = O) by lia.
    setoid_rewrite H. split; try reflexivity.
    intros t Ht. 
    (* Now we get contradiction as such t cannot exist if t_min > t_max *)
    lia.
  }
  unfold resource_profile in Hprofile.
  (* Here we use the fact that profile is not nil to get the fact that all values returned Some and that map_valid is then just a reversed map. *)
  apply map_valid_spec with (d := N0) in Hprofile as [Hprofile Hsome]; try assumption; clear Hprofilennil.
  (* We want to cancel the revs. *)
  rewrite range_rev_is_rev_range in Hprofile, Hsome.
  rewrite <- map_rev in Hprofile.
  rewrite rev_involutive in Hprofile.
  setoid_rewrite <- in_rev in Hsome.
  split.
  { subst profile. rewrite length_map. now rewrite length_range. }
  intros t Ht.
  (* We want to use Hsome. *)
  assert (In t (range t_min t_max)) as Hintrange.
  { clear -Ht. now rewrite <- in_range. }
  specialize (Hsome t Hintrange); clear Hintrange.
  destruct resource_profile_t eqn:Hprofilet; try contradiction; clear Hsome.
  f_equal.
  subst profile.
  (* We write in terms of nth so we can use facts about nth. *)
  rewrite nth_z_spec by lia.
  rewrite <- map_nth_len_lt with (d := 0).
  2: { rewrite length_range. lia. }
  unfold option_map_default.
  rewrite range_nth_spec by lia.
  replace (t_min + (Z.of_nat (Z.to_nat (t - t_min)))) with t by lia.
  rewrite Hprofilet.
  reflexivity.
Qed.

(** Helper lemma for below. *)
Lemma nil_rev {A} :
  forall (l : list A),
    rev l = nil <-> l = nil.
Proof.
  intros l. split; intros H.
  + apply rev_inj. rewrite H. reflexivity.
  + rewrite H. reflexivity.
Qed.

(** Given a cumulative constraint, a solution for that constraint and a set of bounds corresponding to that constraint and satisfied by the solution, we should not be able to find a conflict. *)
Lemma no_bound_conflict_for_solution constraint assignment bounds :
  Forall nonzero_duration constraint.(activities)
    ->
  Cumulative constraint assignment
    ->
  valid_bounds assignment constraint.(activities) bounds
    ->
  forall bound,
    In bound bounds
      ->
    check_conflict_for_bound (capacity constraint) bounds bound = false.
Proof.
  intros Hdur Hcumul Hvalid.
  intros bound Hinbounds.
  unfold check_conflict_for_bound.
  pose proof Hvalid as Hvalid'.
  destruct resource_profile eqn:Hprofile.
  { exfalso. apply no_profile_overflow_for_solution with (assignment := assignment) in Hprofile; try assumption.
    apply (valid_bounds_properties _ _ _ Hdur) in Hvalid.
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
  apply can_schedule_activity_with_profile_valid with (constr := constraint) (sol := assignment) (bounds := bounds).
  - exact Hcumul.
  - exact Hvalid.
  - exact Hinbounds.
  - apply resource_profile_valid.
    + subst profile. reflexivity.
    + exact Hprofilennil.
Qed.

Lemma checker_cumulative :
  forall constraint fact,
  cumulative_checker fact constraint = true
    ->
  forall assignment, 
    Cumulative constraint assignment
      -> 
    fact_valid assignment fact.
Proof.
  intros constr0 fact Hchecked.
  unfold cumulative_checker in Hchecked.
  intros sol Hcumul.
  (* Switch to the constraint that the checker actually runs on. *)
  apply ensure_nonzero_equiv in Hcumul.
  pose proof (activities_pos_duration_correct constr0.(activities)) as Hdur.
  set (constr := ensure_nonzero_duration constr0) in *.
  unfold cumulative_checker_nonzero in Hchecked.
  (* We want to get rid of the case where the checker returns false when there is an inconsistency immediately in the fact/it cannot produce bounds. *)
  destruct inferred_cumulative_activity_bounds as [bounds prop_bound_opt] eqn:Hbounds.
  (* We now want to use our spec for inferred_cumulative_bounds. *)
  apply inferred_cumulative_activity_bounds_spec with (constr := constr) (bounds := bounds) (prop_bound_opt := prop_bound_opt).
  { exact Hbounds. }
  intros Hvalid.
  apply inferred_cumulative_activity_bounds_prop_bound_valid in Hbounds as Hprop_bound.
  (* There are some duplicated cases based on where the conflict is found, e.g., cannot_schedule_activity is occurs twice. We assert here that there must be one of two types of conflict: activity conflict or time conflict. *)
  assert ((exists bound, In bound bounds /\ check_conflict_for_bound (capacity constr) bounds bound = true) \/ check_time_conflict_horizon (capacity constr) bounds = true).
  {
    destruct prop_bound_opt as [prop_bound|].
    - destruct (check_conflict_for_bound (capacity constr) bounds prop_bound) eqn:Hprop_cannot.
      + left. exists prop_bound.
        unfold valid_prop_bound in Hprop_bound.
        now split.
      + destruct check_time_conflict_horizon eqn:Hprofile.
        * right. reflexivity.
        * rewrite existsb_exists in Hchecked.
          left. exact Hchecked.
    - destruct check_time_conflict_horizon eqn:Hprofile.
      + right. reflexivity.
      + rewrite existsb_exists in Hchecked.
        left. exact Hchecked.
  }
  (* We have used the structure of the checker, so we can discard it. *)
  clear Hchecked Hprop_bound Hbounds.
  (* Now we look at the two conflict cases and show that our checker indicates there is a conflict even though we assume the assignment to satisfy the constraint, giving us a contradiction in each case. *)
  destruct H as [(bound & Hinbounds & Hconflict) | Hconflict].
  - enough (check_conflict_for_bound (capacity constr) bounds bound = false) 
      by (rewrite H in Hconflict; discriminate).
    apply no_bound_conflict_for_solution with (assignment := sol).
    + exact Hdur.
    + exact Hcumul.
    + exact Hvalid.
    + exact Hinbounds.
  - unfold check_time_conflict_horizon in Hconflict.
    destruct (bounds_times bounds) as [t_min t_max] eqn:Htimes.
    destruct resource_profile eqn:Hprofile; try discriminate.
    enough (resource_profile (capacity constr) bounds (range t_min t_max) <> nil)
      by (rewrite Hprofile in H; contradiction).
    apply no_profile_overflow_for_solution with (assignment := sol);
      try assumption.
    rewrite range_cons.
    + easy.
    + eapply bounds_times_le.
      * exact Hvalid.
      * exact Htimes.
Qed.

Open Scope string.

(** Uncomment the below for some tests to ensure the cumulative checker successfully checks some facts it should be able to check. *)

(* Mandatory conflict *)    
(* Compute 
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
  cumulative_checker fact constr. *)
