Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.
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
      size := N.to_nat (h_size - a.(def_p)) ;
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

Definition x_from_v (v : Var * N * N) : string :=
  match v with
  | (v, _, _) => var_name v
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
          || (h_size <? def_p a)%N) eqn:Hmem.
          - discriminate Htov.
          - repeat rewrite orb_false_iff in Hmem.
            destruct Hmem as [[Hmem _] _].
            rewrite <- not_true_iff_false in Hmem.
            rewrite sstr.mem_spec in Hmem.
            inversion Htov as [Hv]; clear Htov;
            subst p'; subst u'.
            rewrite Hv.
            intros H.
            rewrite in_map_iff in H.
            destruct H as [[[v' p'] u'] [Hname H]].
            simpl in Hname.
            apply def_to_vs_in in H.
            rewrite Hname in H.
            apply H.
            apply sstr.add_spec.
            left.
            rewrite <- Hv.
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
    horizon_all (def_to_vs l xs h_start h_size) h_start (h_start + Z.of_N h_size)
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
        || (h_size <? def_p a)%N) eqn:Hsize.
        { discriminate Htov. }
        repeat rewrite orb_false_iff in Hsize.
        repeat rewrite <- not_true_iff_false in Hsize.
        repeat rewrite N.ltb_lt in Hsize.
        destruct Hsize as [[_ Hp] Hsize].
        inversion Htov.
        unfold upper_bound. simpl.
        lia.
      * apply IHl in Hin.
        exact Hin.
    + simpl in Hin.
      apply IHl in Hin.
      exact Hin.
Qed.

Lemma processing_constr_def_to_vs :
  forall l xs h_start h_size,
    processing_constr (def_to_vs l xs h_start h_size) h_start (h_start + Z.of_N h_size)
    .
Proof.
  induction l.
  - intros xs h_start h_size.
    unfold processing_constr.
    intros v p u Hin.
    simpl in Hin. contradiction.
  - intros xs h_start h_size.
    unfold processing_constr.
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
        || (h_size <? def_p a)%N) eqn:Hsize.
        { discriminate Htov. }
        repeat rewrite orb_false_iff in Hsize.
        repeat rewrite <- not_true_iff_false in Hsize.
        repeat rewrite N.ltb_lt in Hsize.
        destruct Hsize as [[_ Hp] Hsize].
        inversion Htov.
        unfold upper_bound. simpl.
        lia.
      * apply IHl in Hin.
        exact Hin.
    + simpl in Hin.
      apply IHl in Hin.
      exact Hin.
Qed.

Lemma def_horizon_consistent :
  forall (h_start : Z) (h_size : N),
    h_start <= h_start + Z.of_N h_size.
Proof.
  lia.
Qed.

Lemma nodup_map (A B : Type) (eq_dec : forall x y : A, {x = y}+{x <> y}) (eq_dec_b : forall x y : B, {x = y}+{x <> y}) :
  forall (f : A -> B) (l : list A),
    NoDup (map f l)
      ->
    forall a1 a2,
      In a1 l
        ->
      In a2 l
        ->
      f a1 = f a2
        ->
      a1 = a2.
Proof.
  intros f l Hnodup.
  intros a1 a2 Hin1 Hin2 Hf.
  destruct (eq_dec a1 a2) as [Heq | Hneq].
  - exact Heq.
  - exfalso.
    apply in_split in Hin1.
    destruct Hin1 as [l1 [l2 Hl]].
    subst l.
    apply in_app_or in Hin2.
    destruct Hin2 as [Hin2 | Hin2].
    + apply in_split in Hin2.
      destruct Hin2 as [l3 [l4 Hl]].
      subst l1.
      repeat rewrite map_app in Hnodup.
      simpl in Hnodup.
      rewrite (NoDup_count_occ eq_dec_b) in Hnodup.
      specialize (Hnodup (f a1)).
      repeat rewrite count_occ_app in Hnodup.
      rewrite count_occ_cons_eq in Hnodup; try easy.
      rewrite count_occ_cons_eq in Hnodup; try easy. 
      lia.
    + destruct Hin2 as [Hfalse | Hin2]; try contradiction.
      apply in_split in Hin2.
      destruct Hin2 as [l3 [l4 Hl]].
      subst l2.
      repeat rewrite map_app in Hnodup.
      simpl in Hnodup.
      repeat rewrite map_app in Hnodup.
      simpl in Hnodup.
      rewrite (NoDup_count_occ eq_dec_b) in Hnodup.
      specialize (Hnodup (f a1)).
      repeat rewrite count_occ_app in Hnodup.
      rewrite count_occ_cons_eq in Hnodup; try easy.
      repeat rewrite count_occ_app in Hnodup.
      rewrite count_occ_cons_eq in Hnodup; try easy. 
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
  intros v1 v2 p1 p2 u1 u2.
  intros Hin1 Hin2 Hname.
  assert (x_from_v (v1, p1, u1) = x_from_v (v2, p2, u2)).
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
    vs: list (Var * N * N);
    horizon_start : Z;
    horizon_end : Z;
    valid_horizon : horizon_all vs horizon_start horizon_end;
    valid_p_times : processing_constr vs horizon_start horizon_end;
    horizon_consistent : horizon_start <= horizon_end;
    x_determine_params : x_determines_params vs;
    vs_nodup : NoDup vs
  }.

Definition build_cumulative (l : list ActivityDefine) (c : N) (h_start : Z) (h_size : N) : CumulativeConstraint :=
    {|
      capacity := c ;
      vs := def_to_vs l sstr.empty h_start h_size ;
      horizon_start := h_start ;
      horizon_end := h_start + Z.of_N h_size ;
      valid_horizon := (horizon_all_def_to_vs l sstr.empty h_start h_size) ;
      valid_p_times := (processing_constr_def_to_vs l sstr.empty h_start h_size) ;
      horizon_consistent := def_horizon_consistent h_start h_size;
      x_determine_params := (x_determines_var_def_to_vs (def_to_vs l sstr.empty h_start h_size) (nodup_xs_def_to_vs l sstr.empty h_start h_size));
      vs_nodup := (nodup_def_to_vs l sstr.empty h_start h_size)
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

