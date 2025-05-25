Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.
Require Import Checker.Domain.
Require Import Checker.Utility.
Import Utility.ListEx.
Import Utility.Sets.
Import Utility.ListInd.
Import Utility.ZRange.

Record ActivityDefine := mkActDef
  {
    def_x : string;
    def_p : N;
    def_u : N;
  }.

Fixpoint def_xs (l : list ActivityDefine) : sstr.t :=
  match l with
  | nil => sstr.empty
  | a :: l' => sstr.add (a.(def_x)) (def_xs l')
  end.

Definition def_a_to_v (xs : sstr.t) (a : ActivityDefine) : option ActivityDefine :=
  if (sstr.mem a.(def_x) xs) || (a.(def_p) <? 1)%N 
    then None
    else Some a.

Fixpoint def_to_vs (l : list ActivityDefine) (xs : sstr.t)  :=
  match l with
  | nil => nil
  | a :: l' => 
    match def_a_to_v xs a with
    | Some a_out => a_out :: nil 
    | None => nil
    end ++ (def_to_vs l' (sstr.add a.(def_x) xs))
  end.

Lemma def_to_vs_in :
  forall l a xs,
    In a (def_to_vs l xs)
      ->
    ~ sstr.In a.(def_x) xs.
Proof.
  induction l as [| a l IH].
  - intros a xs.
    intros Hin.
    simpl in Hin. contradiction.
  - intros a' xs.
    intros Hin.
    simpl in Hin.
    destruct (def_a_to_v) as [a_out |] eqn:Htov.
    + simpl in Hin. destruct Hin.
      * unfold def_a_to_v in Htov.
        destruct (sstr.mem (def_x a) xs
        || (def_p a <? 1)%N) eqn:Hmem.
        -- discriminate Htov.
        -- subst a_out.
          inversion Htov; subst a'; clear Htov.
          repeat rewrite orb_false_iff in Hmem.
          destruct Hmem as [Hmem _].
          rewrite <- sstr.mem_spec.
          intros H; rewrite H in Hmem.
          discriminate Hmem.
     * apply IH in H.
        rewrite sstr.add_spec in H.
        intros Hin.
        apply H. 
        right. exact Hin.
    + simpl in Hin.
      apply IH in Hin.
      rewrite sstr.add_spec in Hin.
      intros Hinxs.
      apply Hin. 
      right. exact Hinxs.
Qed.

Lemma def_to_vs_checks_correct :
  forall activities xs,
    let activities' := def_to_vs activities xs in
    NoDup (map def_x activities') /\ forall a, In a activities' -> (def_p a >= 1)%N.
Proof.
  induction activities as [| a activities IH].
  - intros xs. simpl. split.
    + apply NoDup_nil.
    + easy.
  - intros xs. 
    simpl.
    destruct (def_a_to_v xs a) as [a_out |] eqn:Htov.
    + intros; subst.
      specialize (IH (sstr.add (def_x a) xs)).
      remember (def_to_vs activities (sstr.add (def_x a) xs)) as activities'.
      destruct IH as [IHnodup IHp].
      unfold def_a_to_v in Htov.
      destruct orb eqn:Hchecked in Htov; try discriminate Htov.
      inversion Htov; subst a_out; clear Htov.
      split.
      { 
        rewrite map_app.
        apply NoDup_app.
        - simpl.
          apply NoDup_cons.
          + intros H. destruct H.
          + apply NoDup_nil.
        - apply IHnodup.
        - clear -Hchecked Heqactivities'.
          subst activities'.
          intros x'.
          intros Hin. simpl in Hin.
          destruct Hin as [Hout | Hfalse]; try contradiction.
          rewrite in_map_iff.
          intros (a' & Hnamea' & Hina').
          apply def_to_vs_in in Hina'.
          apply Hina'; clear Hina'.
          rewrite sstr.add_spec.
          left. rewrite Hout. rewrite Hnamea'.
          reflexivity.
      }
      {
        intros a'. 
        rewrite in_app_iff.
        intros [Haa' | Hin].
        - clear -Hchecked Haa'.
          destruct Haa'; try contradiction.
          subst a'.
          rewrite orb_false_iff in Hchecked.
          destruct Hchecked as [_ Hp].
          rewrite <- not_true_iff_false in Hp.
          rewrite N.ltb_lt in Hp.
          lia.
        - apply IHp.
          exact Hin.
      }
    + simpl. apply IH.
Qed.

Record CumulativeConstraint :=
  {
    capacity: N;
    activities: list ActivityDefine;
    valid_p_times : forall a, In a activities -> (a.(def_p) >= 1)%N;
    acts_nodup : NoDup (map def_x activities)
  }.

Definition build_cumulative (activities_in : list ActivityDefine) (cap : N) : CumulativeConstraint :=
  {|
    capacity := cap ;
    activities := def_to_vs activities_in sstr.empty;
    valid_p_times := (proj2 (def_to_vs_checks_correct activities_in sstr.empty));
    acts_nodup := (proj1 (def_to_vs_checks_correct activities_in sstr.empty))
  |}.

Record Activity := mkAct {
  a_name : string;
  start : Z;
  p_time : N;
  usage : N;
}.

Lemma activity_eq_dec :
  forall x y : Activity, {x = y}+{x <> y}.
Proof.
  intros x y. decide equality.
  - apply N.eq_dec.
  - apply N.eq_dec.
  - apply Z.eq_dec.
  - apply String.string_dec.
Qed.

Fixpoint n_sum_rec (l : list N) (current : N) : N :=
  match l with
  | nil => current
  | n :: l' => n_sum_rec l' (current + n)
  end.


Open Scope N_scope.
Definition n_sum (l : list N) : N :=
  n_sum_rec l N0.

Definition xn_sum (l : list (string * N)) : N :=
  n_sum (map snd l).

Lemma xn_eq_dec :
  forall x y : (string * N), {x = y}+{x <> y}.
Proof.
  intros x y. decide equality.
  - apply N.eq_dec.
  - apply String.string_dec.
Qed.

Definition act_to_xn (a : Activity) : (string * N) :=
  (a.(a_name), a.(usage)).

Definition usage_sum (l : list Activity) : N :=
  xn_sum (map act_to_xn l).

Open Scope Z_scope.
Definition is_active_at (start_time : Z) (p_time : N) (t : Z) : bool :=
  let end_time := (start_time + (Z.of_N p_time)) in
    (start_time <=? t) && (t <? end_time).

Definition activities_at_t (l : list Activity) (t : Z) : list Activity :=
  filter (fun a => is_active_at a.(start) a.(p_time) t) l
.

Definition activity_from_a_def (a : string -> Z) (act : ActivityDefine) : Activity :=
  match act with
  | mkActDef x p u => 
    mkAct x (a x) p u
  end.

Definition a_def_from_activity (act : Activity) : ActivityDefine :=
  match act with
  | mkAct x start p u =>
    mkActDef x p u
  end.

Definition activity_list_inner (l : list ActivityDefine) (a : string -> Z) : list Activity :=
  map (activity_from_a_def a) l
.

Definition activity_list (c : CumulativeConstraint) (a : string -> Z) : list Activity :=
  activity_list_inner c.(activities) a
.

Lemma a_def_in_iff :
  forall c a act,
    start act = a (a_name act) /\ In (a_def_from_activity act) (activities c) <-> In act (activity_list c a).
Proof.
  intros c a act.
  destruct act as [x start p u]; unfold a_def_from_activity; simpl.
  unfold activity_list, activity_list_inner.
  rewrite in_map_iff; unfold activity_from_a_def.
  split; intros H.
  - exists (mkActDef x p u).
    now destruct H as [Hstart Hin]; subst.
  - destruct H as [a_def [Hdef Hin]].
    now destruct a_def; inversion Hdef; subst.
Qed.

Lemma a_def_in_if :
  forall c a act,
    In act (activity_list c a) ->
    In (a_def_from_activity act) (activities c).
Proof.
  intros c a act Hin.
  rewrite <- a_def_in_iff in Hin.
  apply Hin.
Qed.

Lemma act_in_iff :
  forall c a a_def,
    In a_def (activities c) <-> In (activity_from_a_def a a_def) (activity_list c a).
Proof.
  intros c a a_def.
  destruct a_def as [x p u].
  unfold activity_list, activity_list_inner, activity_from_a_def.
  rewrite in_map_iff.
  split; intros H.
  - now exists (mkActDef x p u).
  - destruct H as [a_def [Hdef Hin]].
    now destruct a_def; inversion Hdef; subst.
Qed.

Definition starts (l : list Activity) :=
  map start l.

Definition ends (l : list Activity) :=
  map (fun a => start a + (Z.of_N (p_time a)) - 1) l.


Definition max_l (l : list Z) :=
  fold_right Z.max (hd 0 l) l.

Definition min_l (l : list Z) :=
  fold_right Z.min (hd 0 l) l.

Lemma min_l_spec l : forall n, In n l -> min_l l <= n.
Proof.
  set (P := fun (s : list Z) (acc : Z) =>
    forall n, In n s -> acc <= n).
  enough (P l (min_l l)).
  { apply H. } 
  unfold min_l.
  apply fold_ind; unfold P in *; clear P.
  - intros n Hin. destruct Hin.
  - intros n acc s. intros IH.
    intros n'. intros [Hnn' | Hin].
    + subst. lia.
    + specialize (IH n' Hin).
      lia.
Qed.

Lemma max_l_spec l : forall n, In n l -> n <= max_l l.
Proof.
  set (P := fun (s : list Z) (acc : Z) =>
    forall n, In n s -> n <= acc).
  enough (P l (max_l l)).
  { apply H. } 
  unfold max_l.
  apply fold_ind; unfold P in *; clear P.
  - intros n Hin. destruct Hin.
  - intros n acc s. intros IH.
    intros n'. intros [Hnn' | Hin].
    + subst. lia.
    + specialize (IH n' Hin).
      lia.
Qed.

Open Scope N_scope.
Definition Cumulative (constraint : CumulativeConstraint) (a : string -> Z) : Prop :=
  let activities := activity_list constraint a in
  forall t,
    usage_sum (activities_at_t activities t) <= constraint.(capacity).


Open Scope N_scope.
Definition cumulative_decide (constraint : CumulativeConstraint) (a : string -> Z) : bool :=
  let activities := activity_list constraint a in
  let t_min := min_l (starts activities) in
  let t_max := max_l (ends activities) in
  forallb 
    (fun t => 
      usage_sum (activities_at_t activities t) <=? constraint.(capacity)
    )
    (range t_min t_max)
.

(* From Coq 9.0 *)
Lemma filter_false {A} l : filter (fun _ : A => false) l = nil.
Proof. induction l; cbn [filter]; congruence. Qed.

Open Scope Z_scope.
Lemma cumulative_decides :
  forall c a,
    reflect (Cumulative c a) (cumulative_decide c a).
Proof.
  intros c a.
  destruct (cumulative_decide c a) eqn:Hdec.
  - apply ReflectT. 
    unfold Cumulative.
    remember (activity_list c a) as acts.
    assert (forall t, t < min_l (starts acts) -> activities_at_t (activity_list c a) t = nil) as Ht_min.
    {
      intros t Htmin.
      unfold activities_at_t; rewrite <- Heqacts.
      rewrite <- filter_false with (l := acts).
      apply filter_ext_in.
      intros act Hin.
      unfold is_active_at.
      enough (t < start act) by lia.
      enough (min_l (starts acts) <= start act) by lia.
      apply min_l_spec.
      unfold starts. rewrite in_map_iff.
      now exists act.
    }
    assert (forall t, t > max_l (ends acts) -> activities_at_t (activity_list c a) t = nil) as Ht_max.
    {
      intros t Htmin.
      unfold activities_at_t; rewrite <- Heqacts.
      rewrite <- filter_false with (l := acts).
      apply filter_ext_in.
      intros act Hin.
      unfold is_active_at.
      enough (t >= start act + Z.of_N (p_time act)) by lia.
      enough (start act + Z.of_N (p_time act) - 1 <= max_l (ends acts)) by lia.
      apply max_l_spec.
      unfold ends. rewrite in_map_iff.
      now exists act.
    }
    intros t.
    destruct (t <? min_l (starts acts)) eqn:Ht_small.
    { 
      rewrite <- Heqacts in *; clear Heqacts Hdec.
      rewrite Ht_min.
      - unfold usage_sum, xn_sum, n_sum. simpl. lia.
      - lia.
    }
    destruct (t >? max_l (ends acts)) eqn:Ht_large.
    { 
      rewrite <- Heqacts in *; clear Heqacts Hdec.
      rewrite Ht_max.
      - unfold usage_sum, xn_sum, n_sum. simpl. lia.
      - lia.
    }
    clear Ht_min Ht_max.
    unfold cumulative_decide in Hdec.
    rewrite <- Heqacts in *.
    rewrite forallb_forall in Hdec.
    rewrite <- N.leb_le.
    apply Hdec.
    rewrite <- in_range.
    lia.
  - apply ReflectF. 
    intros Hcumul.
    unfold cumulative_decide in Hdec.
    rewrite <- not_true_iff_false in Hdec.
    rewrite forallb_forall in Hdec.
    apply Hdec; clear Hdec.
    intros t. intros Htin; clear Htin.
    rewrite N.leb_le.
    apply Hcumul.
Qed.

(* This is not the right place for this, probably also there are some better ways to do this. *)

Lemma reflect_neg_iff (P : Prop) (b : bool) :
  reflect P b -> (~ P <-> b = false).
Proof.
  intros R; destruct R; split; cbv; congruence.
Qed.

Ltac reflect_rewrite_base R loc is_goal :=
  match type of R with
  | reflect ?P ?P_dec =>
    let Rtrue := fresh in
    let Rfalse := fresh in
    specialize (reflect_iff P P_dec R) as Rtrue;
    specialize (reflect_neg_iff P P_dec R) as Rfalse;
    match is_goal with
    | false =>
      first [ rewrite Rtrue in loc
        | rewrite <- Rtrue in loc
        | rewrite Rfalse in loc
        | rewrite <- Rfalse in loc ]
    | true =>
      first [ rewrite Rtrue
        | rewrite <- Rtrue
        | rewrite Rfalse
        | rewrite <- Rfalse ]
    end;
    clear Rtrue Rfalse
  | _ => fail "Argument should be reflect lemma!"
  end.

Ltac reflect_rewrite R := reflect_rewrite_base R True true.
 
Tactic Notation "reflect_rewrite" constr(R) :=
  reflect_rewrite R.

Tactic Notation "reflect_rewrite" constr(R) "in" hyp(H) :=
  reflect_rewrite_base R H false.
