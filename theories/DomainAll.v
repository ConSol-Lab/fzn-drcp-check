Require Import Coq.Logic.FinFun.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import String.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Arith.PeanoNat.
Require Import Bool.

Require Import Checker.Nogood.
Require Import Checker.Cumulative.
Require Checker.CumulativeUtil.
Import CumulativeUtil.ResourceSum.
Require Import Checker.Utility.
Import ListEx.
Require Import Lia.
Require Import Checker.Variable.
Require Checker.Utility.
Require Coq.MSets.MSetAVL.
Require Coq.MSets.MSetProperties.
Require Coq.Structures.OrdersEx.

(* ################################### *)
(* ####### MSet instantiations ####### *)

Module sstr := MSetAVL.Make OrdersEx.String_as_OT.
Module sint := MSetAVL.Make OrdersEx.Z_as_OT.
Module Z_String_as_OT := OrdersEx.PairOrderedType OrdersEx.Z_as_OT OrdersEx.String_as_OT.
Module sintstr := MSetAVL.Make Z_String_as_OT.
Module sstr_prps := MSetProperties.Properties sstr.
Module sint_prps := MSetProperties.Properties sint.
Module sintstr_prps := MSetProperties.Properties sintstr.

Inductive AtomicComparator :=
  | less_equal
  | greater_equal
  | not_equal
  | equal.

Record Atomic := {
    cmp : AtomicComparator;
    val : Z
}.

(* This is much more efficient than using filter twice. *)
Definition in_interval (s : sint.t) (from : Z) (to : Z) : sint.t :=
  let t := sint.this s in
  let split_1 := sint.Raw.t_right (sint.Raw.split (from - 1) t) in
  let ok_1 := sint.Raw.split_ok2 (from - 1) (sint.is_ok s) in
  let split_2 := sint.Raw.t_left (sint.Raw.split (to + 1) split_1) in
  let ok_2 := sint.Raw.split_ok1 (to + 1) ok_1 in
  {| sint.this := split_2; sint.is_ok := ok_2 |}.

Lemma in_interval_spec :
  forall s lb ub,
    forall n, 
      sint.In n (in_interval s lb ub) 
        <->
      sint.In n s /\ lb <= n <= ub.
Proof.
  specialize sint.Raw.split_spec2 as Hsplit_r.
  specialize sint.Raw.split_spec1 as Hsplit_l.
  intros s lb ub n.
  unfold in_interval.
  unfold sint.In; unfold sint.Raw.In; simpl.
  specialize (Hsplit_r (sint.this s) (lb-1) n (sint.is_ok s)).
  specialize (sint.Raw.split_ok2 (lb - 1) (sint.is_ok s)) as Hok_1.
  remember (sint.Raw.t_right (sint.Raw.split (lb-1) (sint.this s))) as split_1.
  specialize (Hsplit_l split_1 (ub+1) n Hok_1).
  rewrite Hsplit_l. rewrite Hsplit_r.
  repeat rewrite Z.compare_lt_iff.
  split.
  - clear. intros H.
    destruct H as [[Hin Hl] Hr].
    split.
    + exact Hin.
    + lia.
  - clear. intros H.
    destruct H as [Hin [Hl Hr]].
    repeat split.
    + exact Hin.
    + lia.
    + lia.
Qed.  

Definition check_bound (lb : Z) (ub : Z) (holes : sint.t) := 
  if lb <=? ub
    then Some (lb, ub, holes)
    else None.


Definition apply_atomic (atomic : Atomic) (lb : Z) (ub : Z) (holes : sint.t) :=
  match atomic.(cmp) with
  | less_equal => check_bound lb (Z.min ub atomic.(val)) holes
  | greater_equal => check_bound (Z.max lb atomic.(val)) ub holes
  | equal =>
    if ((ub <? atomic.(val)) || (atomic.(val) <? lb))
      then None
      else Some (atomic.(val), atomic.(val), holes)
  | not_equal => 
    if ((lb <=? atomic.(val)) && (atomic.(val) <=? ub))
      then Some (lb, ub, sint.add atomic.(val) holes)
      else None
  end.

Definition hole_fold_f (hole : Z) (acc : (Z * list Z)) :=
  match acc with
  | (lb, interior) =>
    if (hole =? lb)
      then (lb + 1, interior)
      else (lb, hole :: interior)
  end.

Definition apply_holes_l (lb : Z) (holes : sint.t) :=
  sint.fold hole_fold_f holes (lb, nil).

Definition hole_fold_r_f (acc : (Z * sint.t)) (hole : Z) :=
  match acc with
  | (ub, interior) =>
    if (hole =? ub)
      then (ub - 1, interior)
      else (ub, sint.add hole interior)
  end.

Definition apply_holes_r (ub : Z) (holes : list Z) :=
  fold_left hole_fold_r_f holes (ub, sint.empty).

Definition apply_holes (lb : Z) (ub : Z) (holes : sint.t) :=
  let holes_between := in_interval holes lb ub in
  match apply_holes_l lb holes_between with
  | (lb, interior_l) =>
    match apply_holes_r ub interior_l with
    | (ub, interior) =>
      check_bound lb ub interior
    end
  end.


Fixpoint apply_atomics_rec (atomics : list Atomic) (lb : Z) (ub : Z) (holes : sint.t):=
    match atomics with
    | nil => Some (lb, ub, holes)
    | a :: atomics' => 
      match apply_atomic a lb ub holes with
      | None => None
      | Some (lb, ub, holes) => apply_atomics_rec atomics' lb ub holes
      end
    end.

Definition apply_atomics (atomics : list Atomic) (lb : Z) (ub : Z) :=
  match apply_atomics_rec atomics lb ub sint.empty with
  | None => None
  | Some (lb, ub, holes) =>
    apply_holes lb ub holes
  end.