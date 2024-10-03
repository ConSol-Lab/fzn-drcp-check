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

Fixpoint evaluate_linear (x : list (Z * Var)) (sol : Assignment) : option Z :=
  match x with
  | [] => Some 0
  | (coef, v) :: xs =>
      match find_value sol v with
      | None => None
      | Some a => 
          match evaluate_linear xs sol with
          | None => None
          | Some rest => Some (coef * a + rest)
          end
      end
  end.

Definition satisfies_linear (cons : LinearConstraint) (sol : Assignment) : bool :=
  match evaluate_linear (terms cons) sol with
  | Some lhs => lhs >=? bound cons
  | None => false
  end.

Definition is_valid_linear_inference 
  (inference : list Atomic) (constraint : LinearConstraint) : Prop := 
  forall (sol : Assignment), Is_true (satisfies_linear constraint sol) -> satisfies_nogood inference sol = Some true.

Definition scaled_upper_bound (w : Z) (x : Var) :=
  w * if w >? 0 then var_upper_bound x else var_lower_bound x.

Theorem valid_scaled_upper_bound : forall (w : Z) (x : Var) (v : Z),
  Is_true (is_in x v) -> w * v <= scaled_upper_bound w x.
Proof.
  intros.
  specialize (Z.gtb_spec w 0) as wbound.
  destruct wbound as [wpos|wneg].
  - assert (Hrhs: scaled_upper_bound w x = w * var_upper_bound x). {
      unfold scaled_upper_bound.
      apply Z.lt_gt, Z.gtb_gt in wpos.
      rewrite wpos.
      reflexivity.
    }
    rewrite Hrhs.
    apply Z.mul_le_mono_nonneg_l.
    + apply Z.lt_le_incl, wpos.
    + apply is_in_implies_upper_bound, H.
  - assert (Hrhs: scaled_upper_bound w x = w * var_lower_bound x). {
      unfold scaled_upper_bound.
      rewrite Z.gtb_ltb.
      rewrite negb_involutive_reverse with (0 <? w).
      rewrite <- Z.leb_antisym.
      Search (_ <=? _ = negb _).
      apply Z.leb_le in wneg.
      rewrite wneg.
      reflexivity.
    }
    rewrite Hrhs.
    apply Z.mul_le_mono_nonpos_l.
    + apply wneg.
    + apply Z.ge_le, is_in_implies_lower_bound, H.
Qed.

Definition evaluate_optimistic_scaled (w : Z) (x : Var) (atomic : Atomic) :=
  match (comparator atomic) with
  | less_equal => if w <? 0 then w * var_lower_bound x else w * value atomic
  | greater_equal => if w >=? 0 then w * var_upper_bound x else w * value atomic
  | equal => w * value atomic
  | _ => scaled_upper_bound w x
  end.

Lemma valid_scaled_atomic_nonneg : forall (w : Z) (x : Var) (atomic : Atomic) (v : Z),
  Is_true (is_in x v) ->
  Is_true (test_atomic atomic v) ->
  w >= 0 -> 
  w * v <= evaluate_optimistic_scaled w x atomic.
Proof.
  intros w x atomic v Hin Hatomic Hnonneg.
  unfold evaluate_optimistic_scaled.
  destruct (comparator atomic) eqn:cmp ;
  unfold test_atomic in Hatomic ;
  rewrite cmp in Hatomic ;
  apply Is_true_eq_true in Hatomic.
  - rewrite Z.ltb_antisym.
    apply Z.ge_le, Zle_imp_le_bool in Hnonneg as Hnonnegb. 
    rewrite Hnonnegb.
    simpl.
    apply Z.mul_le_mono_nonneg_l.
    * apply Hnonneg.
    * apply Z.leb_le in Hatomic.
      apply Hatomic.
  - apply Z.geb_ge in Hnonneg as Hnonnegb. 
    rewrite Hnonnegb.
    apply Z.mul_le_mono_nonneg_l.
    * apply Z.ge_le, Hnonneg.
    * apply is_in_implies_upper_bound, Hin.
  - apply valid_scaled_upper_bound, Hin.
  - apply Z.eqb_eq in Hatomic.
    rewrite Hatomic.
    reflexivity.
Qed.

Lemma valid_scaled_atomic_neg : forall (w : Z) (x : Var) (atomic : Atomic) (v : Z),
  Is_true (is_in x v) ->
  Is_true (test_atomic atomic v) ->
  w < 0 -> 
  w * v <= evaluate_optimistic_scaled w x atomic.
Proof.
  intros w x atomic v Hin Hatomic Hneg.
  unfold evaluate_optimistic_scaled.
  destruct (comparator atomic) eqn:cmp ;
  unfold test_atomic in Hatomic ;
  rewrite cmp in Hatomic ;
  apply Is_true_eq_true in Hatomic.
  - apply Z.ltb_lt in Hneg as Hnegb.  
    rewrite Hnegb.
    apply Z.mul_le_mono_nonpos_l.
    * apply Z.lt_le_incl, Hneg.
    * apply Z.ge_le, is_in_implies_lower_bound, Hin.
  - rewrite Z.geb_leb, Z.leb_antisym.
    apply Z.ltb_lt in Hneg as Hnegb.  
    rewrite Hnegb.
    simpl.
    apply Z.mul_le_mono_nonpos_l.
    * apply Z.lt_le_incl, Hneg.
    * apply Z.geb_ge, Z.ge_le in Hatomic.
      apply Hatomic.
  - apply valid_scaled_upper_bound, Hin.
  - apply Z.eqb_eq in Hatomic.
    rewrite Hatomic.
    reflexivity.
Qed.

Theorem valid_scaled_atomic : forall (w : Z) (x : Var) (atomic : Atomic) (v : Z),
  Is_true (is_in x v) ->
  Is_true (test_atomic atomic v) ->
  w * v <= evaluate_optimistic_scaled w x atomic.
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
    Z.min (scaled_upper_bound w x)
    (map (evaluate_optimistic_scaled w x) atomics).

Theorem valid_scaled_atomic_list : forall
  (w : Z) (x : Var) (atomics : list Atomic) (v : Z),
  Is_true (is_in x v) ->
  (forall (atomic : Atomic), In atomic atomics -> Is_true(test_atomic atomic v)) ->
  w * v <= evaluate_optimistic_scaled_list w x atomics.
Proof.
  intros w x atomics v Hin Hlist.
  unfold evaluate_optimistic_scaled_list.
  induction atomics.
  - simpl.
    apply valid_scaled_upper_bound, Hin.
  - assert (Htail: forall atomic : Atomic, In atomic atomics -> Is_true (test_atomic atomic v)). {
      intros.
      apply Hlist.
      simpl.
      right.
      apply H.
    }
    apply IHatomics in Htail.
    simpl.
    apply Z.min_glb.
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


Definition test_atomic_assignment (atomic : Atomic) (sol : Assignment) :=
  match (find_value sol (var atomic)) with
  | Some v => test_atomic atomic v
  | None => false
  end.


Theorem evaluate_optimistic_linear_falsifies : forall
  (x : list (Z * Var)) (inference : list Atomic) (sol : Assignment) (ev : Z),
  evaluate_linear x sol = Some ev ->
  (forall (atomic : Atomic), In atomic inference -> Is_true (test_atomic_assignment atomic sol)) ->
  ev <= evaluate_optimistic_linear x inference.
Proof.
  intros x inference sol ev Heval Hsat.
  generalize dependent ev.
  induction x ; simpl ; intros ev Heval.
  - inversion Heval.
    reflexivity.
  - destruct a as [coef v].
    destruct (find_value sol v) as [found_val|] eqn:Hfind.
    + destruct (evaluate_linear x sol) as [rest|].
      * inversion Heval.
        apply Z.add_le_mono.
        -- apply valid_scaled_atomic_list ;
           unfold find_value in Hfind;
           destruct (find (fun x => eqb (variable x) v)) as [var|] eqn:Hfind_var;
           inversion Hfind.
           ++ rewrite H1.
              apply find_some in Hfind_var.
              destruct Hfind_var as [Hvar_in Heqvar].
              apply Is_true_eq_left, eqb_eq in Heqvar.
              assert (Hin: Is_true (is_in (variable var) found_val) -> Is_true (is_in v found_val)). {
                rewrite Heqvar.
                intros H.
                apply H.
              }
              apply Hin.
              specialize (consistency_prop sol) as Hcons.
              apply Is_true_eq_true in Hcons.
              rewrite forallb_forall in Hcons.
              specialize (Hcons var).
              apply Hcons in Hvar_in.
              unfold consistent in Hvar_in.
              inversion Hfind.
              apply Is_true_eq_left in Hvar_in.
              apply Hvar_in.
           ++ intros atomic Hatomic_filter.
              assert (Hatomic: In atomic inference). {
                apply filter_In in Hatomic_filter.
                destruct Hatomic_filter as [Hin _].
                apply Hin.
              }
              apply Hsat in Hatomic.
              unfold test_atomic_assignment in Hatomic.
              destruct (find_value sol (Atomic.var atomic)) as [sol_val|] eqn:Hsol.
              ** unfold find_value in Hsol.
                 destruct (find (fun x => eqb (variable x) (Atomic.var atomic))) as [atomic_var|] eqn:Hatomic_var;
                 inversion Hsol as [Hassigned].
                 apply filter_In in Hatomic_filter.
                 destruct Hatomic_filter as [_ Heq_var].
                 apply Is_true_eq_left, eqb_eq in Heq_var.
                 assert (Heqb_rw: forall (t : VariableAssignment), eqb (variable t) (Atomic.var atomic) = eqb (variable t) v). {
                   intros t.
                   rewrite Heq_var.
                   reflexivity.
                 }
                 assert (Hfn_rw: (fun t : VariableAssignment => eqb (variable t) (Atomic.var atomic)) = (fun t : VariableAssignment => eqb (variable t) v)). {
                   apply functional_extensionality, Heqb_rw.
                 }
                 rewrite Hfn_rw in Hatomic_var.
                 rewrite Hatomic_var in Hfind_var.
                 inversion Hfind_var as [Hvar_def_eq].
                 rewrite <- Hvar_def_eq, Hassigned.
                 apply Hatomic.
              ** simpl in Hatomic.
                 exfalso.
                 apply Hatomic.
        -- apply IHx. reflexivity.
      * discriminate.
    + discriminate.
Qed.



Definition linear_checker
  (inference : list Atomic) (constraint : LinearConstraint) : bool := 
  let expr_upper_bound := evaluate_optimistic_linear
    (terms constraint)
    (map atomic_not inference) in
    expr_upper_bound <? bound constraint.


Lemma unsat_nogood : (forall (atomic : Atomic) (i : list Atomic) (s : Assignment), satisfies_nogood i s = Some false -> In atomic (map atomic_not i) -> Is_true (test_atomic_assignment atomic s)).
Proof.
  intros atomic i.
  generalize dependent atomic.
  induction i ; simpl ; intros.
  - exfalso.
    apply H0.
  - destruct (find_value s (var a)) as [s_val|] eqn:Hs_val.
    + destruct (test_atomic a s_val) eqn:Ha_test.
      * discriminate.
      * destruct H0 as [Hfound|Htail].
        -- unfold test_atomic_assignment. 
           assert (Hvareq: var a = var atomic). {
             rewrite <- Hfound.
             destruct (comparator a) eqn:Hcmp ;
             unfold atomic_not ;
             rewrite Hcmp ;
             reflexivity.
           }
           rewrite <- Hvareq, Hs_val, <- Hfound, atomic_not_involution, Ha_test.
           reflexivity.
        -- apply IHi.
           ++ apply H.
           ++ apply Htail.
    + discriminate.
Qed.


Theorem linear_inference_checker_correct : 
  forall (inference : list Atomic) (constraint : LinearConstraint),
    linear_checker inference constraint = true ->
    is_valid_linear_inference inference constraint.
Proof.
  unfold is_valid_linear_inference, satisfies_linear, linear_checker.
  intros inference constraint Hchk sol Hnogood.
  destruct (evaluate_linear (terms constraint) sol) as [ev|] eqn:Heval.
  - destruct (satisfies_nogood inference sol) as [sat|] eqn:Hsat. destruct sat.
    + reflexivity.
    + exfalso.
      assert (Hfalse: forall (atomic : Atomic), In atomic (map atomic_not inference) -> Is_true (test_atomic_assignment atomic sol)). {
        intros.
        apply unsat_nogood with (i := inference) (s := sol).
        apply Hsat.
        apply H.
      }
      specialize (evaluate_optimistic_linear_falsifies
        (terms constraint)
        (map atomic_not inference)
        sol ev
        Heval
        Hfalse
      ).
      intros Hev_bound.
      remember (evaluate_optimistic_linear (terms constraint) (map atomic_not inference)) as opt_ev.
      apply Is_true_eq_true, Z.geb_ge, Z.ge_le in Hnogood.
      specialize (Z.le_trans (bound constraint) ev opt_ev Hnogood Hev_bound) as Hcons_bound.
      apply Z.ltb_lt in Hchk.
      apply Z.lt_irrefl with opt_ev.
      apply Z.lt_le_trans with (bound constraint).
      * apply Hchk.
      * apply Hcons_bound.
    + exfalso.
      (* TODO How to handle incomplete assignments? *)
      admit.
  - simpl in Hnogood.
    exfalso.
    apply Hnogood.
Admitted.

