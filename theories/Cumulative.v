Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Lia.
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

Record CumulativeConstraint :=
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
  }.

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

