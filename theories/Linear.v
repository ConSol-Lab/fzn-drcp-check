Require Import Bool.
Require Import ZArith.
Require Import Int.
Require Import Checker.Variable.
Require Import Checker.Deduction.
Require Import Checker.DomainVar.
Require Import Checker.Nogood.
Require Import List.
Require Import Logic.FunctionalExtensionality.
Require Import String.
Require Import Lia.
Import Utility.Maps.
Open Scope Z_scope.
Import ListNotations.

Record LinearConstraint :=
  {
    l_terms : list (Z * string);
    l_bound : Z;
  }.

Fixpoint evaluate_linear (x : list (Z * string)) (sol : string -> Z) : Z :=
  match x with
  | [] => 0
  | (coef, v) :: xs => coef * (sol v) + (evaluate_linear xs sol)
  end.

Definition linear_leq (c : LinearConstraint) (sol : string -> Z) :=
  evaluate_linear (c.(l_terms)) (sol) <= c.(l_bound).

Definition term_lower_bound (coef : Z) (var : string) (dom : Domain.Domain) : option Z :=
  if coef >? 0
  then match (Domain.d_lb dom) with
       | Some lb => Some (coef * lb)
       | None => None
       end
  else match (Domain.d_ub dom) with
       | Some ub => Some (coef * ub)
       | None => None
       end.

Fixpoint lower_bound (terms : list (Z * string)) (doms : DomainMap) :=
  match terms with
  | [] => Some 0
  | (coef, v) :: tail =>
      match smap.find v doms with
      | Some dom => 
          match term_lower_bound coef v dom, lower_bound tail doms with
          | Some term_lb, Some tail_lb => Some (term_lb + tail_lb)
          | _, _ => None
          end
      | None => None
      end
  end.

Definition linear_checker (fact : Deduction.Inference) (c : LinearConstraint) :=
  (* TODO Handle the implication case by normalization *)
  match fact.(i_consequent) with
  | None =>
      let doms := DomainVar.domains_from_var_atomics_all fact.(i_premises) None
      in 
      match doms with
        (* TODO What does the none mean here? *)
      | None => false
      | Some doms => 
          match lower_bound (c.(l_terms)) doms with
          | None => false
          | Some lb => lb >? c.(l_bound)
          end
      end
  | Some _ => false
  end.

Lemma term_bound_validity : forall
  (coef : Z) (var : string) (dom : Domain.Domain)
  (val : Z)
  (bound : Z),
  Domain.is_in_dom val (Some dom) ->
  term_lower_bound coef var dom = Some bound ->
  bound <= coef * val.
Proof.
  intros coef var dom sol bound Hvalid Elb.
  unfold Domain.is_in_dom in Hvalid.
  destruct dom.
  destruct Hvalid as [Hub [Hlb _]].
  unfold term_lower_bound in Elb.
  simpl in Elb.
  destruct (coef >? 0) eqn:Hsign.
  - destruct d_lb ; inversion Elb as [Elb'].
    apply OrdersEx.Z_as_OT.mul_le_mono_nonneg_l ; lia.
  - destruct d_ub ; inversion Elb as [Elb'].
    apply OrdersEx.Z_as_OT.mul_le_mono_nonpos_l ; lia.
Qed.

Lemma bound_validity : forall
  (terms : list (Z * string)) (doms : DomainMap)
  (sol : string -> Z)
  (bound : Z),
  doms_hold_for_sol sol doms -> lower_bound terms doms = Some bound ->
  bound <= evaluate_linear terms sol.
Proof.
  intros terms doms sol bound Hvalid.
  generalize dependent bound.
  Opaque term_lower_bound.
  induction terms ; simpl ; intros bound Elb ; inversion Elb ; try easy.
  destruct a as [coef var].
  destruct (smap.find var doms) as [dom|] eqn:Efind ; inversion Elb.
  destruct (term_lower_bound coef var dom) as [term_bound|] eqn:Eterm_bound ;
      inversion Elb.
  assert (Htail_bound: term_bound <= coef * sol var). {
    unfold DomainVar.doms_hold_for_sol in Hvalid.
    apply term_bound_validity with (var := var) (dom := dom).
    - apply Hvalid, smap_prps.find_2, Efind.
    - assumption.
  }
  destruct (lower_bound terms doms) as [tail_bound|] eqn:Etail_bound ;
      inversion Etail_bound ; inversion Elb.
  assert (Hbound: tail_bound <= evaluate_linear terms sol). {
    apply IHterms.
    reflexivity.
  }
  lia.
Qed.

Theorem linear_checker_soundness : forall
  (fact : Deduction.Inference) (sol : string -> Z) (c : LinearConstraint),
  linear_leq c sol ->
  Is_true (linear_checker fact c)
  -> Deduction.inference_valid sol fact.
Proof.
  intros fact sol c.
  unfold linear_checker.
  unfold inference_valid.
  destruct fact.(i_consequent) ; try contradiction.
  destruct c as [lin_terms lin_bound].
  unfold linear_leq.
  simpl.
  remember (fact.(i_premises)) as atoms.
  clear Heqatoms.
  intros Hsat Hbound Hatoms.
  destruct (domains_from_var_atomics_all atoms None) as [doms|] eqn:Edoms.
  - destruct (lower_bound lin_terms doms) eqn:Elb ; try contradiction.
    apply Is_true_eq_true, Z.gtb_gt, Z.gt_lt in Hbound.
    apply doms_from_var_all_hold with (vs := None) (doms := doms) in Hatoms.
    + apply bound_validity with (terms := lin_terms) (bound := z) in Hatoms.
      * lia.
      * exact Elb.
    + exact Edoms.
  - contradiction.
Qed.

