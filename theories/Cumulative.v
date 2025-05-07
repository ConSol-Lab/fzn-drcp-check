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

Record ActivityDefine :=
  {
    def_x : string;
    def_p : N;
    def_u : N;
  }.

Definition x_determines_params (l : list (ActivityDefine * Z * Z)) :=
  forall a1 s1 e1 a2 s2 e2,
    In (a1, s1, e1) l ->
    In (a2, s2, e2) l ->
    a1.(def_x) = a2.(def_x) ->
    (a1, s1, e1) = (a2, s2, e2).

Definition processing_constr (l : list (ActivityDefine * Z * Z)) (h_start : Z) (h_end : Z) :=
  forall a s e,
    In (a, s, e) l ->
      (* TODO: the smaller than diff actually results from horizon_all *)
      (1 <= a.(def_p) <= Z.to_N (h_end - h_start))%N.

Definition horizon_all (l : list (ActivityDefine * Z * Z)) (h_start : Z) (h_end : Z) :=
  forall a s e,
    In (a, s, e) l
      ->
    h_start <= s /\ e + Z.of_N a.(def_p) <= h_end.


Fixpoint def_xs (l : list ActivityDefine) : sstr.t :=
  match l with
  | nil => sstr.empty
  | a :: l' => sstr.add (a.(def_x)) (def_xs l')
  end.

Definition def_a_to_v (xs : sstr.t) (est : Z) (lct : Z) (a : ActivityDefine) : option (ActivityDefine * Z * Z) :=
  if (sstr.mem a.(def_x) xs) || (a.(def_p) <? 1)%N || (lct - est <? Z.of_N a.(def_p))
    then None
    else Some (a, est, lct - Z.of_N a.(def_p)).

Fixpoint def_to_vs (l : list ActivityDefine) (xs : sstr.t) (est : Z) (lct : Z)  :=
  match l with
  | nil => nil
  | a :: l' => 
    match def_a_to_v xs est lct a with
    | Some a_out => a_out :: nil 
    | None => nil
    end ++ (def_to_vs l' (sstr.add a.(def_x) xs) est lct)
  end.

Lemma def_to_vs_in :
  forall l v p u xs h_start h_size,
    In (v, p, u) (def_to_vs l xs h_start h_size)
      ->
    ~ sstr.In v.(def_x) xs.
Proof.
  induction l.
  - intros v p u xs h_start h_size.
    intros Hin.
    simpl in Hin. contradiction.
  - intros v p u xs h_start h_size.
    intros Hin.
    simpl in Hin.
    destruct (def_a_to_v xs h_start h_size a) as [a_out |] eqn:Htov.
    + simpl in Hin. destruct Hin.
      * unfold def_a_to_v in Htov.
        destruct (sstr.mem (def_x a) xs
        || (def_p a <? 1)%N
        || (h_size - h_start <? Z.of_N (def_p a))) eqn:Hmem.
        -- discriminate Htov.
        -- repeat rewrite orb_false_iff in Hmem.
            destruct Hmem as [[Hmem _] _].
            rewrite <- not_true_iff_false in Hmem.
            rewrite sstr.mem_spec in Hmem.
            assert (def_x a = v.(def_x)) as Hname.
            {
              inversion Htov as [Haout]; clear Htov.
              rewrite H in Haout.
              inversion Haout as [Hv].
              simpl. reflexivity.
            }
            rewrite <- Hname.
            exact Hmem.
      * apply IHl in H.
        rewrite sstr.add_spec in H.
        intros Hin.
        apply H. 
        right. exact Hin.
    + simpl in Hin.
      apply IHl in Hin.
      rewrite sstr.add_spec in Hin.
      intros Hinxs.
      apply Hin. 
      right. exact Hinxs.
Qed.

Definition x_from_v (v : ActivityDefine * Z * Z) : string :=
  match v with
  | (v, _, _) => v.(def_x)
  end.

Lemma nodup_xs_def_to_vs :
  forall l xs h_start h_size,
    NoDup (map x_from_v (def_to_vs l xs h_start h_size)).
Proof.
  induction l.
  - intros xs h_start h_size. simpl. apply NoDup_nil.
  - intros xs h_start h_size.
    simpl.
    destruct (def_a_to_v xs h_start h_size a) as [a_out |] eqn:Htov.
    + rewrite map_app.
      apply NoDup_app.
      * simpl.
        apply NoDup_cons.
        -- intros H. destruct H.
        -- apply NoDup_nil.
      * apply IHl.
      * {
          intros x'.
          intros Hin. simpl in Hin.
          destruct Hin as [Hout | Hfalse]; try contradiction.
          destruct a_out as [[v p'] u'].
          simpl in Hout.
          subst x'.
          unfold def_a_to_v in Htov.
          destruct (sstr.mem (def_x a) xs
          || (def_p a <? 1)%N
          || (h_size - h_start <? Z.of_N (def_p a))) eqn:Hmem.
          - discriminate Htov.
          - repeat rewrite orb_false_iff in Hmem.
            destruct Hmem as [[Hmem _] _].
            rewrite <- not_true_iff_false in Hmem.
            rewrite sstr.mem_spec in Hmem.
            inversion Htov as [Hv]; clear Htov;
            subst p'; subst u'.
            rewrite <- Hv.
            intros H.
            rewrite in_map_iff in H.
            destruct H as [[[v' p'] u'] [Hname H]].
            simpl in Hname.
            apply def_to_vs_in in H.
            rewrite Hname in H.
            apply H.
            apply sstr.add_spec.
            left.
            rewrite Hv.
            simpl.
            reflexivity.
      }
    + simpl. apply IHl.
Qed.

Lemma nodup_def_to_vs :
  forall l xs h_start h_size,
    NoDup (def_to_vs l xs h_start h_size).
Proof.
  intros l xs h_start h_size.
  apply NoDup_map_inv with (f := x_from_v).
  apply nodup_xs_def_to_vs.
Qed.


Lemma horizon_all_def_to_vs :
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

Lemma processing_constr_def_to_vs :
  forall l xs h_start h_size,
    processing_constr (def_to_vs l xs h_start h_size) h_start h_size
    .
Proof.
Admitted.
(*   induction l. *)
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

Lemma def_horizon_consistent :
  forall (h_start : Z) (h_size : N),
    h_start <= h_start + Z.of_N h_size.
Proof.
  lia.
Qed.

     
Lemma x_determines_var_def_to_vs:
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


Record CumulativeConstraint :=
  {
    capacity: N;
    vs: list (ActivityDefine * Z * Z);
    horizon_start : Z;
    horizon_end : Z;
    valid_horizon : horizon_all vs horizon_start horizon_end;
    valid_p_times : processing_constr vs horizon_start horizon_end;
    horizon_consistent : horizon_start <= horizon_end;
    x_determine_params : x_determines_params vs;
    vs_nodup : NoDup vs
  }.

Definition build_cumulative (l : list ActivityDefine) (c : N) (h_start : Z) (h_size : N) : CumulativeConstraint :=
  let h_end := h_start + Z.of_N h_size in
    {|
      capacity := c ;
      vs := def_to_vs l sstr.empty h_start h_end ;
      horizon_start := h_start ;
      horizon_end := h_end ;
      valid_horizon := (horizon_all_def_to_vs l sstr.empty h_start h_end) ;
      valid_p_times := (processing_constr_def_to_vs l sstr.empty h_start h_end) ;
      horizon_consistent := def_horizon_consistent h_start h_size;
      x_determine_params := (x_determines_var_def_to_vs (def_to_vs l sstr.empty h_start h_end) (nodup_xs_def_to_vs l sstr.empty h_start h_end));
      vs_nodup := (nodup_def_to_vs l sstr.empty h_start h_end)
    |}.


(* Compute build_cumulative ({|def_x := "x";
def_p := 5%N;
def_u := 1%N;|} :: nil) 1%N Z0 20%N. *)

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

Definition activity_list_inner_f (a : string -> Z) (x : (ActivityDefine * Z * Z)) : Activity :=
  match x with
  | (v, _, _) => 
    let var_id := v.(def_x) in
    mkAct var_id (a var_id) v.(def_p) v.(def_u)
  end.

Definition activity_list_inner (l : list (ActivityDefine * Z * Z)) (a : string -> Z) : list Activity :=
  map (activity_list_inner_f a) l
.

Definition activity_list (c : CumulativeConstraint) (a : string -> Z) : list (Activity) :=
  activity_list_inner c.(vs) a
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

