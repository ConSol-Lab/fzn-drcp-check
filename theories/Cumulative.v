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
(* 
Lemma nodup_def_to_vs :
  forall l xs h_start h_size,
    NoDup (def_to_vs l xs h_start h_size).
Proof.
  intros l xs h_start h_size.
  apply NoDup_map_inv with (f := x_from_v).
  apply nodup_xs_def_to_vs.
Qed.
 *)

(* Lemma horizon_all_def_to_vs :
  forall l xs h_start h_size,
    horizon_all (def_to_vs l xs h_start h_size) h_start h_size
    .
Proof.
  induction l.
  - intros xs h_start h_size.
    unfold horizon_all.
    intros v p u Hin.
    simpl in Hin. contradiction.
  - intros xs h_start h_size.
    unfold horizon_all.
    intros v p u Hin.
    destruct v as [v].
    simpl in Hin.
    destruct (def_a_to_v xs h_start h_size a) as [a_out |] eqn:Htov.
    + apply in_app_or in Hin.
      destruct Hin as [Ha | Hin].
      * destruct Ha as [Ha | Hfalse]; try destruct Hfalse.
        subst a_out.
        unfold def_a_to_v in Htov.
        destruct (sstr.mem (def_x a) xs
        || (def_p a <? 1)%N
        || (h_size - h_start <? Z.of_N (def_p a))) eqn:Hmem.
        { discriminate Htov. }
        (* repeat rewrite orb_false_iff in Hsize. *)
        (* repeat rewrite <- not_true_iff_false in Hsize. *)
        (* repeat rewrite N.ltb_lt in Hsize. *)
        (* destruct Hsize as [[_ Hp] Hsize]. *)
        inversion Htov.
        lia.
      * apply IHl in Hin.
        exact Hin.
    + simpl in Hin.
      apply IHl in Hin.
      exact Hin.
Qed.
 *)
(* Lemma processing_constr_def_to_vs :
  forall l xs h_start h_size,
    processing_constr (def_to_vs l xs h_start h_size) h_start h_size
    .
Proof.
Admitted. *)
  (* induction l. *)
(*   - intros xs h_start h_size. *)
(*     unfold processing_constr. *)
(*     intros v p u Hin. *)
(*     simpl in Hin. contradiction. *)
(*   - intros xs h_start h_size. *)
(*     unfold processing_constr. *)
(*     intros v p u Hin. *)
(*     destruct v as [v]. *)
(*     simpl in Hin. *)
(*     destruct (def_a_to_v xs h_start h_size a) as [a_out |] eqn:Htov. *)
(*     + apply in_app_or in Hin. *)
(*       destruct Hin as [Ha | Hin]. *)
(*       * destruct Ha as [Ha | Hfalse]; try destruct Hfalse. *)
(*         subst a_out. *)
(*         unfold def_a_to_v in Htov. *)
(*         destruct (sstr.mem (def_x a) xs *)
(*         || (def_p a <? 1)%N *)
(*         || (h_size - h_start <? Z.of_N (def_p a))) eqn:Hmem. *)
(*         { discriminate Htov. } *)
(*         repeat rewrite orb_false_iff in Hsize. *)
(*         repeat rewrite <- not_true_iff_false in Hsize. *)
(*         repeat rewrite N.ltb_lt in Hsize. *)
(*         (* destruct Hsize as [[_ Hp] Hsize]. *) *)
(*         inversion Htov. *)
(*         simpl in H2. *)
(*         simpl. *)
(*         (* unfold upper_bound. simpl. *) *)
(*         lia. *)
(*       * apply IHl in Hin. *)
(*         exact Hin. *)
(*     + simpl in Hin. *)
(*       apply IHl in Hin. *)
(*       exact Hin. *)
(* Qed. *)

(* Lemma def_horizon_consistent :
  forall (h_start : Z) (h_size : N),
    h_start <= h_start + Z.of_N h_size.
Proof.
  lia.
Qed.
 *)
     
(* Lemma x_determines_var_def_to_vs:
  forall vs,
    NoDup (map x_from_v vs)
      ->
    x_determines_params vs.
Proof.
  intros vs Hnodup.
  unfold x_determines_params.
  intros a1 s1 e1 a2 s2 e2.
  intros Hin1 Hin2 Hname.
  assert (x_from_v (a1, s1, e1) = x_from_v (a2, s2, e2)).
  {
    simpl. exact Hname. 
  }
  apply nodup_map with (f := x_from_v) (l := vs).
  - repeat decide equality.
  - repeat decide equality.
  - exact Hnodup.
  - exact Hin1.
  - exact Hin2.
  - exact H.
Qed.
 *)

Record CumulativeConstraint :=
  {
    capacity: N;
    activities: list ActivityDefine;
    horizon_start : Z;
    horizon_end : Z;
    valid_p_times : forall a, In a activities -> (a.(def_p) >= 1)%N;
    horizon_consistent : horizon_start <= horizon_end;
    acts_nodup : NoDup (map def_x activities)
  }.

Lemma is_horizon_consistent :
  forall h_start h_size,
    h_start <= h_start + Z.of_N h_size.
Proof. lia. Qed.

Definition build_cumulative (activities_in : list ActivityDefine) (c : N) (h_start : Z) (h_size : N) : CumulativeConstraint :=
  let h_end := h_start + Z.of_N h_size in
    {|
      capacity := c ;
      activities := def_to_vs activities_in sstr.empty;
      horizon_start := h_start ;
      horizon_end := h_end ;
      horizon_consistent := is_horizon_consistent h_start h_size ;
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

Definition activity_list_inner_f (a : string -> Z) (act : ActivityDefine) : Activity :=
  match act with
  | mkActDef x p u => 
    mkAct x (a x) p u
  end.

Definition activity_list_inner (l : list ActivityDefine) (a : string -> Z) : list Activity :=
  map (activity_list_inner_f a) l
.

Definition activity_list (c : CumulativeConstraint) (a : string -> Z) : list Activity :=
  activity_list_inner c.(activities) a
.

Open Scope N_scope.
Definition cumulative_decide (constraint : CumulativeConstraint) (a : string -> Z) : bool :=
  let c_activities := activity_list constraint a in
  forallb 
    (fun t => 
      usage_sum (activities_at_t c_activities t) <=? constraint.(capacity)
    )
    (ZRange.build_range constraint.(horizon_start) constraint.(horizon_end))
.

