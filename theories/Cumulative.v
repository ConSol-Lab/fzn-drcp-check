Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.
Require Import Checker.Domain.
Require Import Checker.Utility.
Require Import Checker.Spec.
Import Spec.ConstraintDefinitions.
Import Utility.ListEx.
Import Utility.Sets.
Import Utility.ListInd.
Import Utility.ZRange.

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
  intros activities.
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

Definition build_cumulative (activities_in : list ActivityDefine) (cap : N) : CumulativeConstraint :=
  {|
    capacity := cap ;
    activities := def_to_vs activities_in sstr.empty;
    valid_p_times := (proj2 (def_to_vs_checks_correct activities_in sstr.empty));
    acts_nodup := (proj1 (def_to_vs_checks_correct activities_in sstr.empty))
  |}.

Lemma activity_eq_dec :
  forall x y : Activity, {x = y}+{x <> y}.
Proof.
  intros x y. decide equality.
  - apply N.eq_dec.
  - apply N.eq_dec.
  - apply Z.eq_dec.
  - apply String.string_dec.
Qed.


Open Scope N_scope.
Lemma xn_eq_dec :
  forall x y : (string * N), {x = y}+{x <> y}.
Proof.
  intros x y. decide equality.
  - apply N.eq_dec.
  - apply String.string_dec.
Qed.

Open Scope Z_scope.

Definition a_def_from_activity (act : Activity) : ActivityDefine :=
  match act with
  | mkAct x start p u =>
    mkActDef x p u
  end.

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



(* From Coq 9.0 *)
Lemma filter_false {A} l : filter (fun _ : A => false) l = nil.
Proof. induction l; cbn [filter]; congruence. Qed.

(* This is not the right place for this, probably also there are some better ways to do this. *)
Open Scope Z_scope.
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
