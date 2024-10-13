Require Import Bool.
Require Import ZArith.
Require Import Int.
Require Import Checker.Variable.
Require Import Checker.Inference.
Require Import Checker.Atomic.
Require Import Checker.Nogood.
Require Import List.
Require Import Logic.FunctionalExtensionality.
Open Scope Z_scope.
Import ListNotations.

Record LinearConstraint :=
  {
    terms : list (Z * Var);
    bound : Z;
  }.

Fixpoint evaluate_linear (x : list (Z * Var)) (sol : Assignment) : Z :=
  match x with
  | [] => 0
  | (coef, v) :: xs =>
      let val := (find_value sol) v in
      let rest := evaluate_linear xs sol in
      coef * val + rest
  end.

Definition satisfies_linear (cons : LinearConstraint) (sol : Assignment) : bool :=
  evaluate_linear (terms cons) sol <=? bound cons.

Definition is_valid_linear_inference 
  (inference : list Atomic) (constraint : LinearConstraint) : Prop := 
  forall (sol : Assignment),
  Is_true (satisfies_linear constraint sol) ->
  Is_true (satisfies_nogood inference sol).

Definition scaled_lower_bound (w : Z) (x : Var) :=
  w * if w >? 0 then var_lower_bound x else var_upper_bound x.

Theorem valid_scaled_lower_bound : forall (w : Z) (x : Var) (v : Z),
  Is_true (is_in x v) -> w * v >= scaled_lower_bound w x.
Proof.
  intros.
  specialize (Z.gtb_spec w 0) as wbound.
  destruct wbound as [wpos|wneg].
  - assert (Hrhs: scaled_lower_bound w x = w * var_lower_bound x). {
      unfold scaled_lower_bound.
      apply Z.lt_gt, Z.gtb_gt in wpos.
      rewrite wpos.
      reflexivity.
    }
    rewrite Hrhs.
    apply Z.le_ge, Z.mul_le_mono_nonneg_l.
    + apply Z.lt_le_incl, wpos.
    + apply Z.ge_le, is_in_implies_lower_bound, H.
  - assert (Hrhs: scaled_lower_bound w x = w * var_upper_bound x). {
      unfold scaled_lower_bound.
      rewrite Z.gtb_ltb.
      rewrite negb_involutive_reverse with (0 <? w).
      rewrite <- Z.leb_antisym.
      apply Z.leb_le in wneg.
      rewrite wneg.
      reflexivity.
    }
    rewrite Hrhs.
    apply Z.le_ge, Z.mul_le_mono_nonpos_l.
    + apply wneg.
    + apply is_in_implies_upper_bound, H.
Qed.

Definition evaluate_optimistic_scaled (w : Z) (x : Var) (atomic : Atomic) :=
  match (comparator atomic) with
  | less_equal => if w >=? 0 then w * var_lower_bound x else w * value atomic
  | greater_equal => if w <? 0 then w * var_upper_bound x else w * value atomic
  | equal => w * value atomic
  | _ => scaled_lower_bound w x
  end.

Lemma valid_scaled_atomic_nonneg : forall (w : Z) (x : Var) (atomic : Atomic) (v : Z),
  Is_true (is_in x v) ->
  Is_true (test_atomic atomic v) ->
  w >= 0 -> 
  w * v >= evaluate_optimistic_scaled w x atomic.
Proof.
  intros w x atomic v Hin Hatomic Hnonneg.
  unfold evaluate_optimistic_scaled.
  destruct (comparator atomic) eqn:cmp ;
  unfold test_atomic in Hatomic ;
  rewrite cmp in Hatomic ;
  apply Is_true_eq_true in Hatomic.
  - apply Z.geb_ge in Hnonneg as Hnonnegb. 
    rewrite Hnonnegb.
    apply Z.le_ge, Z.mul_le_mono_nonneg_l ; apply Z.ge_le.
    * apply Hnonneg.
    * apply is_in_implies_lower_bound, Hin.
  - rewrite Z.ltb_antisym.
    apply Z.ge_le, Zle_imp_le_bool in Hnonneg as Hnonnegb. 
    rewrite Hnonnegb.
    simpl.
    apply Z.le_ge, Z.mul_le_mono_nonneg_l.
    * apply Hnonneg.
    * apply Z.geb_ge in Hatomic.
      apply Z.ge_le, Hatomic.
  - apply valid_scaled_lower_bound, Hin.
  - apply Z.eqb_eq in Hatomic.
    rewrite Hatomic.
    apply Z.le_ge, Z.le_refl.
Qed.

Lemma valid_scaled_atomic_neg : forall (w : Z) (x : Var) (atomic : Atomic) (v : Z),
  Is_true (is_in x v) ->
  Is_true (test_atomic atomic v) ->
  w < 0 -> 
  w * v >= evaluate_optimistic_scaled w x atomic.
Proof.
  intros w x atomic v Hin Hatomic Hneg.
  unfold evaluate_optimistic_scaled.
  destruct (comparator atomic) eqn:cmp ;
  unfold test_atomic in Hatomic ;
  rewrite cmp in Hatomic ;
  apply Is_true_eq_true in Hatomic.
  - rewrite Z.geb_leb, Z.leb_antisym.
    apply Z.ltb_lt in Hneg as Hnegb.  
    rewrite Hnegb.
    simpl.
    apply Z.le_ge, Z.mul_le_mono_nonpos_l.
    * apply Z.lt_le_incl, Hneg.
    * apply Z.leb_le in Hatomic.
      apply Hatomic.
  - apply Z.ltb_lt in Hneg as Hnegb.  
    rewrite Hnegb.
    apply Z.le_ge, Z.mul_le_mono_nonpos_l.
    * apply Z.lt_le_incl, Hneg.
    * apply is_in_implies_upper_bound, Hin.
  - apply valid_scaled_lower_bound, Hin.
  - apply Z.eqb_eq in Hatomic.
    rewrite Hatomic.
    apply Z.le_ge, Z.le_refl.
Qed.

Theorem valid_scaled_atomic : forall (w : Z) (x : Var) (atomic : Atomic) (v : Z),
  Is_true (is_in x v) ->
  Is_true (test_atomic atomic v) ->
  w * v >= evaluate_optimistic_scaled w x atomic.
Proof.
  intros w x atomic v Hin Hatomic.
  specialize (Z.geb_spec w 0) as wbound.
  destruct wbound as [Hnonneg|Hneg].
  - apply valid_scaled_atomic_nonneg.
    + apply Hin.
    + apply Hatomic.
    + apply Z.le_ge, Hnonneg.
  - apply valid_scaled_atomic_neg.
    + apply Hin.
    + apply Hatomic.
    + apply Hneg.
Qed.

Definition evaluate_optimistic_scaled_list (w : Z) (x : Var) (atomics: list Atomic) :=
  fold_right
    Z.max (scaled_lower_bound w x)
    (map (evaluate_optimistic_scaled w x) atomics).

Theorem valid_scaled_atomic_list : forall
  (w : Z) (x : Var) (atomics : list Atomic) (v : Z),
  Is_true (is_in x v) ->
  (forall (atomic : Atomic), In atomic atomics -> Is_true(test_atomic atomic v)) ->
  w * v >= evaluate_optimistic_scaled_list w x atomics.
Proof.
  intros w x atomics v Hin Hlist.
  unfold evaluate_optimistic_scaled_list.
  induction atomics.
  - simpl.
    apply valid_scaled_lower_bound, Hin.
  - assert (Htail: forall atomic : Atomic, In atomic atomics -> Is_true (test_atomic atomic v)). {
      intros.
      apply Hlist.
      simpl.
      right.
      apply H.
    }
    apply IHatomics in Htail.
    simpl.
    apply Z.le_ge, Z.max_lub ; apply Z.ge_le.
    + apply valid_scaled_atomic.
      * apply Hin.
      * apply Hlist.
        simpl.
        left.
        reflexivity.
    + apply Htail.
Qed.

Fixpoint evaluate_optimistic_linear (x : list (Z * Var)) (inference : list Atomic) :=
  match x with
  | [] => 0
  | (coef, v) :: xs =>
      evaluate_optimistic_scaled_list coef v (
        filter (fun atomic => eqb v (var atomic)) inference
      ) + evaluate_optimistic_linear xs inference
  end.


Theorem evaluate_optimistic_linear_falsifies : forall
  (x : list (Z * Var)) (inference : list Atomic) (sol : Assignment),
  (forall (atomic : Atomic), In atomic inference -> Is_true (test_atomic_assignment atomic sol)) ->
  evaluate_linear x sol >= evaluate_optimistic_linear x inference.
Proof.
  intros x inference sol Hsat.
  induction x ; simpl.
  - apply Z.le_ge, Z.le_refl.
  - destruct a as [coef v].
    apply Z.le_ge, Z.add_le_mono ; apply Z.ge_le.
    + apply valid_scaled_atomic_list.
      * apply (consistency_proof sol).
      * intros atomic Hatomic_filter.
        assert (Hatomic: In atomic inference). {
          apply filter_In in Hatomic_filter.
          destruct Hatomic_filter as [Hin _].
          apply Hin.
        }
        apply Hsat in Hatomic.
        unfold test_atomic_assignment in Hatomic.
        apply filter_In in Hatomic_filter.
        destruct Hatomic_filter as [_ Heq_var].
        apply Is_true_eq_left, eqb_eq in Heq_var.
        rewrite Heq_var.
        apply Hatomic.
    + apply IHx.
Qed.


Definition linear_checker
  (inference : list Atomic) (constraint : LinearConstraint) : bool := 
  let expr_lower_bound := evaluate_optimistic_linear
    (terms constraint)
    (map atomic_not inference) in
    expr_lower_bound >? bound constraint.



Theorem linear_inference_checker_correct : 
  forall (inference : list Atomic) (constraint : LinearConstraint),
    linear_checker inference constraint = true ->
    is_valid_linear_inference inference constraint.
Proof.
  unfold is_valid_linear_inference, satisfies_linear, linear_checker.
  intros inference constraint Hchk sol Hnogood.
  destruct (satisfies_nogood inference sol) as [|] eqn:Hsat.
  reflexivity.
  exfalso.
  assert (Hfalse: forall (atomic : Atomic), In atomic (map atomic_not inference) -> Is_true (test_atomic_assignment atomic sol)). {
    intros.
    apply unsat_nogood with (i := inference) (s := sol).
    apply Hsat.
    apply H.
  }
  specialize (evaluate_optimistic_linear_falsifies
  (terms constraint)
  (map atomic_not inference)
  sol
  Hfalse
  ) as Hev_bound.
  remember (evaluate_optimistic_linear (terms constraint) (map atomic_not inference)) as opt_ev.
  remember (evaluate_linear (terms constraint) sol) as ev.
  apply Is_true_eq_true, Z.leb_le in Hnogood.
  apply Z.lt_irrefl with opt_ev.
  apply Z.le_lt_trans with (bound constraint).
  * apply Z.le_trans with (m := ev).
    + apply Z.ge_le, Hev_bound.
    + apply Hnogood.
  * apply Z.gtb_gt in Hchk.
    apply Z.gt_lt, Hchk.
Qed.

