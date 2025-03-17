Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Lia.
Require Import Checker.Utility.
Require Import Checker.Variable.

Record CumulativeConstraint :=
  {
    capacity: N;
    vs: list (Var * N * N);
    horizon_start : Z;
    horizon_end : Z;
    horizon_consistent : horizon_start <= horizon_end
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

Definition usage_sum (l : list Activity) : N :=
  xn_sum (map (fun a => 
    (a.(a_name), a.(usage))
  ) l).

Open Scope Z_scope.
Definition is_active_at (start_time : Z) (p_time : N) (t : Z) : bool :=
  let end_time := (start_time + (Z.of_N p_time)) in
    (start_time <=? t) && (t <=? end_time).

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