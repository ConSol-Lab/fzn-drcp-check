Require Import Bool.
Require Import ZArith.
Require Import Checker.Deduction.
Require Import Checker.DomainVar.
Require Import Checker.Zext.
Require Import Checker.Domain.
Require Import Checker.Spec.
Import Spec.ConstraintDefinitions.
Import Spec.ProofFacts.
Require Import List.
Require Import String.
Require Import Lia.
Import Utility.Maps.
Import Utility.ListEx.
Open Scope Z_scope.
Import ListNotations.

Definition dom_term_lower_bound (coef : Z) (dom : Domain.Domain) : option Z :=
  if coef >? 0
  then match (Domain.d_lb dom) with
       | zz lb => Some (coef * lb)
       | _ => None
       end
  else match (Domain.d_ub dom) with
       | zz ub => Some (coef * ub)
       | _ => None
       end.

Definition term_lower_bound (term : Z * Var) (doms : Domains) : option Z :=
  match term with
  | (coef, var_name ident) => match smap.find ident doms with
      | Some dom => dom_term_lower_bound coef dom
      | None => None
      end
  | (coef, const value) => Some (coef * value)
  end.

Definition accumulate_terms (doms: Domains) (accumulator : Z) (term : Z * Var) : option Z :=
  match term_lower_bound term doms with
  | Some value => Some (accumulator + value)
  | None => None
  end.

(*Definition compute_linear_lower_bound (terms : list (Z * Var)) (doms : Domains) : option Z := 
   fold_left_error (accumulate_terms doms) terms Z.zero.*)

Fixpoint compute_linear_lower_bound (terms : list (Z * Var)) (doms : Domains) : option Z := 
  match terms with
  | [] => Some Z.zero
  | cons term tail => match term_lower_bound term doms, compute_linear_lower_bound tail doms with
                      | Some value, Some acc => Some (value + acc)
                      | _, _ => None
                      end
  end.

Definition linear_checker (fact : ProofFact) (c : LinearConstraint) :=
  match Deduction.infer_domains fact with
  (* Currently information on what variable is r.h.s. is not used. *)
  | Some (doms, _) => 
    match compute_linear_lower_bound (c.(l_terms)) doms with
    | None => false
    | Some lb => lb >? c.(l_bound)
    end
  (* Trivial, maybe accept them in linear's case? *)
  | None => false
  end.

Lemma dom_bound_validity : forall
  (coef : Z) (dom : Domain.Domain)
  (val : Z)
  (bound : Z),
  Domain.is_in_dom val dom ->
  dom_term_lower_bound coef dom = Some bound ->
  bound <= coef * val.
Proof.
  intros coef dom sol bound Hvalid Elb.
  unfold Domain.is_in_dom in Hvalid.
  destruct dom; simpl in Hvalid.
  destruct Hvalid as [Hub [Hlb _]].
  unfold dom_term_lower_bound in Elb.
  simpl in Elb.
  destruct (coef >? 0) eqn:Hsign.
  - destruct d_lb; zext_as_z; inversion Elb as [Elb'].
    apply Z.mul_le_mono_nonneg_l ; lia.
  - destruct d_ub; zext_as_z; inversion Elb as [Elb'].
    apply Z.mul_le_mono_nonpos_l ; lia.
Qed.

Lemma term_bound_validity : forall
  (term : Z * Var) (doms : Domains) (sol : Assignment) (bound : Z),
  sol_in_doms sol doms ->
  term_lower_bound term doms = Some bound ->
  bound <= evaluate_term sol term.
Proof.
  intros terms doms sol bound Hvalid Hlb.
  destruct terms as [coef var].
  destruct var ; simpl ; inversion Hlb ; try lia.
  destruct (smap.find ident doms) as [dom|] eqn:Edom ; inversion H0.
  unfold sol_in_doms in Hvalid.
  specialize (Hvalid ident).
  unfold dom_from_domains in Hvalid.
  rewrite Edom in Hvalid.
  simpl in Hvalid.
  apply dom_bound_validity with (dom:=dom) ; assumption.
Qed.

Lemma bound_validity : forall
  (terms : list (Z * Var)) (doms : Domains)
  (sol : Assignment)
  (bound : Z),
  sol_in_doms sol doms -> compute_linear_lower_bound terms doms = Some bound ->
  bound <= evaluate_linear terms sol.
Proof.
  intros terms doms sol bound Hvalid.
  generalize dependent bound.
  Opaque term_lower_bound.
  induction terms ; simpl ; intros bound Elb ; inversion Elb ; try easy.
  destruct a as [coef var].
  destruct (term_lower_bound (coef, var) doms) as [term_bound|] eqn:Eterm_bound.
    - destruct (compute_linear_lower_bound terms doms) as [tail_bound|] eqn:Etail ; inversion Elb.
      specialize (IHterms tail_bound).
      assert (Htrivial: Some tail_bound = Some tail_bound). {
        reflexivity.
      }
      specialize (IHterms Htrivial).
      specialize (term_bound_validity (coef, var) doms sol term_bound Hvalid Eterm_bound) as Hterm_bound.
      lia.

    - unfold compute_linear_lower_bound in Elb.
      simpl in Elb.
      unfold accumulate_terms in Elb.
      inversion Elb.

Qed.

Theorem linear_checker_soundness : forall
  (fact : ProofFact) (sol : Assignment) (c : LinearConstraint),
  Linear c sol ->
  linear_checker fact c = true ->
  fact_valid sol fact.
Proof.
  intros fact sol c.
  unfold linear_checker.
  destruct c as [lin_terms lin_bound].
  unfold Linear.
  simpl.
  intros Hsat Hbound.
  destruct (infer_domains fact) as [[doms rhs_var]|] eqn:Edoms ; inversion Hbound.
  apply infer_domains_correct with (doms := doms) (xconsq := rhs_var) ; try apply Edoms.
  destruct (compute_linear_lower_bound lin_terms doms) as [lb|] eqn:Elb ; try contradiction.
  apply Z.gtb_gt, Z.gt_lt in Hbound.
  intros Hvalid.
  enough (lb <= evaluate_linear lin_terms sol) by lia.
  apply bound_validity with (doms := doms) ; assumption.
Qed.
