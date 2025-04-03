Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Lia.
Require Import Checker.Domain.
Require Import Checker.Utility.
Require Import Checker.Variable.

Definition x_determines_var (l : list (Var * N * N)) :=
  forall v1 v2 p u,
    In (v1, p, u) l ->
    var_name v1 = var_name v2 ->
    v1 = v2.

Definition x_determines_params (l : list (Var * N * N)) :=
  forall v1 v2 p1 p2 u1 u2,
    In (v1, p1, u1) l ->
    In (v2, p2, u2) l ->
    var_name v1 = var_name v2 ->
    (v1, p1, u1) = (v2, p2, u2).

Definition processing_constr (l : list (Var * N * N)) (h_start : Z) (h_end : Z) :=
  forall v p u,
    In (v, p, u) l ->
      (* TODO: the smaller than diff actually results from horizon_all *)
      (1 <= p <= Z.to_N (h_end - h_start))%N.

Definition horizon_all (l : list (Var * N * N)) (h_start : Z) (h_end : Z) :=
  forall v p u,
    In (v, p, u) l
      ->
    match v with
    | interval var => 
      h_start <= var.(lower_bound) /\ var.(upper_bound) + Z.of_N p <= h_end
    end.

(* Record CumulativeConstraint :=
  {
    capacity: N;
    vs: list (Var * N * N);
    horizon_start : Z;
    horizon_end : Z;
    valid_horizon : horizon_all vs horizon_start horizon_end;
    valid_p_times: processing_constr vs horizon_start horizon_end;
    horizon_consistent : horizon_start <= horizon_end;
    x_determine_var : x_determines_var vs;
    x_determine_params : x_determines_params vs;
    vs_nodup : NoDup vs
  }. *)

Record ActivityDefine :=
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

Definition def_a_to_v (xs : sstr.t) (h_start : Z) (h_size : N) (a : ActivityDefine) : option (Var * N * N) :=
  if (sstr.mem a.(def_x) xs) || (a.(def_p) <? 1)%N || (h_size <? a.(def_p))%N
    then None
    else Some (interval {|
      name := a.(def_x) ;
      lower_bound := h_start ;
      size := N.to_nat h_size ;
     |}, a.(def_p), a.(def_u)).

Fixpoint def_to_vs (l : list ActivityDefine) (xs : sstr.t) (h_start : Z) (h_size : N)  :=
  match l with
  | nil => nil
  | a :: l' => 
    match def_a_to_v xs h_start h_size a with
    | Some a_out => a_out :: nil 
    | None => nil
    end ++ (def_to_vs l' (sstr.add a.(def_x) xs) h_start h_size)
  end.

Lemma def_to_vs_in :
  forall l v p u xs h_start h_size,
    In (v, p, u) (def_to_vs l xs h_start h_size)
      ->
    ~ sstr.In (var_name v) xs.
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
        || (h_size <? def_p a)%N) eqn:Hmem.
        -- discriminate Htov.
        -- repeat rewrite orb_false_iff in Hmem.
            destruct Hmem as [[Hmem _] _].
            rewrite <- not_true_iff_false in Hmem.
            rewrite sstr.mem_spec in Hmem.
            assert (def_x a = var_name v) as Hname.
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

Lemma nodup_comp_vs :
  forall l xs h_start h_size,
    NoDup (def_to_vs l xs h_start h_size).
Proof.
  induction l.
  - intros xs h_start h_size. simpl. apply NoDup_nil.
  - intros xs h_start h_size.
    simpl.
    destruct (def_a_to_v xs h_start h_size a) eqn:Htov.
    + apply NoDup_app.
      * apply NoDup_cons.
        -- intros H. destruct H.
        -- apply NoDup_nil.
      * apply IHl.
      * {
          intros a'.
          intros Hin.
          destruct Hin as [Hpa' | Hfalse]; try destruct Hfalse.
          subst p.
          unfold def_a_to_v in Htov.
          destruct (sstr.mem (def_x a) xs
          || (def_p a <? 1)%N
          || (h_size <? def_p a)%N) eqn:Hmem.
          - discriminate Htov.
          - repeat rewrite orb_false_iff in Hmem.
            destruct Hmem as [[Hmem _] _].
            rewrite <- not_true_iff_false in Hmem.
            rewrite sstr.mem_spec in Hmem.
            inversion Htov as [Ha']; clear Htov;
            destruct a' as [[v p'] u'];
            inversion Ha' as [Hv]; subst p'; subst u'; clear Ha'.
            rewrite Hv.
            intros H.
            apply def_to_vs_in in H.
            apply H.
            apply sstr.add_spec.
            left.
            rewrite <- Hv.
            simpl.
            reflexivity.
      }
    + simpl. apply IHl.
Qed.


Record CumulativeConstraint :=
  {
    capacity: N;
    vs: list (Var * N * N);
    horizon_start : Z;
    horizon_end : Z;
    vs_nodup : NoDup vs
  }.

(* Lemma nodup_comp_vs :
  forall l x xs h_start h_size,
    NoDup (def_to_vs l xs h_start h_size)
      ->
    NoDup (def_to_vs l (sstr.add x xs) h_start h_size)
    .
Proof.
  induction l.
  - intros x xs h_start h_size.
    intros Hnodup. simpl. apply NoDup_nil.
  - intros x xs h_start h_size.
    simpl.
    intros Hnodup.
    apply NoDup_app.
    + unfold def_a_to_v.
      destruct (sstr.mem (def_x a) (sstr.add x xs)
      || (def_p a <? 1)%N
      || (h_size <? def_p a)%N).
      * apply NoDup_nil.
      * apply NoDup_cons.
        -- intros H. destruct H.
        -- apply NoDup_nil.
    + apply NoDup_app_remove_l in Hnodup.
      apply IHl.
      apply Hnodup.
    + intros a'.
      pose proof Hnodup as Hnodupl.
      apply NoDup_app_remove_l in Hnodupl. 
      apply IHl with (x := x) in Hnodupl.
      intros Hin.
      unfold def_a_to_v in Hin.
      destruct (sstr.mem (def_x a) (sstr.add x xs)
      || (def_p a <? 1)%N
      || (h_size <? def_p a)%N) eqn:Hmem.
      { destruct Hin. }
      repeat rewrite orb_false_iff in Hmem.
      destruct Hmem as [[Hmem _] _].
      rewrite <- not_true_iff_false in Hmem.
      rewrite sstr.mem_spec in Hmem.
      destruct Hin as [Ha' | Hfalse].
      2: { destruct Hfalse. }
      destruct a' as [[v p] u].
      inversion Ha' as [Hv].
      subst p; subst u; clear Ha'.
      intros H.
      rewrite Hv in H.
      unfold def_to_vs in H.
      rewrite in_flat_map in H.
      destruct H as [a' [Hainl Hxxs]].
      un *)



Lemma nodup_comp_vs :
  forall l h_start h_size,
    NoDup (def_to_vs l (def_xs l) h_start h_size).
Proof.
  induction l.
  - intros h_start h_size.
    simpl. apply NoDup_nil.
  - intros h_start h_size.
    unfold def_to_vs.
    simpl.
    apply NoDup_app.
    + unfold def_a_to_v.
      destruct (sstr.mem (def_x a)
      (sstr.add (def_x a) (def_xs l))
      || (def_p a <? 1)%N
      || (h_size <? def_p a)%N).
      * apply NoDup_nil.
      * apply NoDup_cons.
        -- intros H. destruct H.
        -- apply NoDup_nil.
    + apply IHl.
      intros a' Hin'.
      apply Hmem.
      right. exact Hin'. 
    + intros a'.
      intros Hin.


      intros Hinnot.
      rewrite in_flat_map in Hinnot.
      destruct Hinnot as [a' [Hinl Hinout]].
      unfold def_a_to_v in Hin, Hinout.
      destruct (sstr.mem (def_x a) xs
      || (def_p a <? 1)%N
      || (h_size <? def_p a)%N) eqn:Hmema; 
      destruct (sstr.mem (def_x a') xs
      || (def_p a' <? 1)%N
      || (h_size <? def_p a')%N) eqn:Hmema'.
      * destruct Hin.
      * destruct Hin.
      * destruct Hinout.
      * repeat rewrite orb_false_iff in Hmema, Hmema'.
        rewrite <- not_true_iff_false in Hmema, Hmema'.
        rewrite sstr.mem_spec in Hmema, Hmema'.
        destruct Hmema as [[Hnotinxs _] _].
        destruct Hmema' as [[Hnotinxs' _] _].
        destruct Hinout as [Haout | Hfalse]; try contradiction.

Admitted.


Definition build_cumulative (l : list ActivityDefine) (c : N) (h_start : Z) (h_size : N) : CumulativeConstraint :=
    {|
      capacity := c ;
      vs := def_to_vs l (def_xs l) h_start h_size ;
      horizon_start := h_start ;
      horizon_end := h_start + Z.of_N h_size ;
      vs_nodup := (nodup_comp_vs l h_start h_size)
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

Definition activity_list_inner_f (a : Assignment) (x : (Var * N * N)) : Activity :=
  match x with
  | (v, x_p_time, x_usage) => 
    match v with
    | interval int_var =>
      mkAct int_var.(name) (a.(find_value) v) x_p_time x_usage
    end
  end.

Definition activity_list_inner (l : list (Var * N * N)) (a : Assignment) : list Activity :=
  map (activity_list_inner_f a) l
.

Definition activity_list (c : CumulativeConstraint) (a : Assignment) : list (Activity) :=
  activity_list_inner c.(vs) a
.

Open Scope N_scope.
Definition cumulative_decide (constraint : CumulativeConstraint) (a : Assignment) : bool :=
  let c_activities := activity_list constraint a in
  forallb 
    (fun t => 
      usage_sum (activities_at_t c_activities t) <=? constraint.(capacity)
    )
    (ZRange.build_range constraint.(horizon_start) constraint.(horizon_end))
.

