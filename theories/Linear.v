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

Definition linear_store_checker (fact : ProofFact) (c : LinearConstraint) :=
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

Theorem linear_store_checker_soundness : forall
  (fact : ProofFact) (sol : Assignment) (c : LinearConstraint),
  Linear c sol ->
  Is_true (linear_store_checker fact c)
  -> fact_valid sol fact.
Proof.
  intros fact sol c.
  unfold linear_store_checker.
  destruct c as [lin_terms lin_bound].
  unfold Linear.
  simpl.
  intros Hsat Hbound.
  destruct (infer_domains fact) as [[doms rhs_var]|] eqn:Edoms ; try contradiction.
  apply infer_domains_correct with (doms := doms) (xconsq := rhs_var) ; try apply Edoms.
  destruct (compute_linear_lower_bound lin_terms doms) as [lb|] eqn:Elb ; try contradiction.
  apply Is_true_eq_true, Z.gtb_gt, Z.gt_lt in Hbound.
  intros Hvalid.
  enough (lb <= evaluate_linear lin_terms sol) by lia.
  apply bound_validity with (doms := doms) ; assumption.
Qed.

(** Lower bound on [coef * x] implied by an atom on [x]. *)
Definition atom_term_lower_bound (coef : Z) (a : Atomic) : option Z :=
  match a.(atm_cmp), coef >? 0 with
  | equal, _ | greater_equal, true | less_equal, false => Some (coef * a.(atm_val))
  | _, _ => None
  end.

(** The negated consequent if it is on [x]. *)
Definition negated_atom_on (x : string) (premises : list BoundAtomic) (negated : option BoundAtomic) :=
  match negated with
  | Some (y, a) => if String.eqb x y then Some (a, premises) else None
  | None => None
  end.

(** The next premise if it is on [x], else the negated consequent if it is on [x]. *)
Definition next_atom_on (x : string) (premises : list BoundAtomic) (negated : option BoundAtomic) :=
  match premises with
  | (y, a) :: premises' => if String.eqb x y then Some (a, premises') else negated_atom_on x premises negated
  | [] => negated_atom_on x premises negated
  end.

Fixpoint scan_linear_lower_bound (terms : list (Z * Var)) (premises : list BoundAtomic) (negated : option BoundAtomic) : option Z :=
  match terms with
  | [] => Some 0
  | (coef, const value) :: tail =>
    match scan_linear_lower_bound tail premises negated with
    | Some acc => Some (coef * value + acc)
    | None => None
    end
  | (coef, var_name x) :: tail =>
    match next_atom_on x premises negated with
    | Some (a, premises') =>
      match atom_term_lower_bound coef a, scan_linear_lower_bound tail premises' negated with
      | Some value, Some acc => Some (value + acc)
      | _, _ => None
      end
    | None => None
    end
  end.

(** Pair each term with an atom by one in-order scan of the premises, without building domains. *)
Definition linear_scan_checker (fact : ProofFact) (c : LinearConstraint) :=
  match scan_linear_lower_bound c.(l_terms) fact.(i_premises) (option_map negate_bound_atomic fact.(i_consequent)) with
  | Some lb => lb >? c.(l_bound)
  | None => false
  end.

Lemma atom_term_lower_bound_validity : forall coef a val bound,
  atomic_holds val a ->
  atom_term_lower_bound coef a = Some bound ->
  bound <= coef * val.
Proof.
  unfold atom_term_lower_bound, atomic_holds.
  intros coef [[] v] val bound Hholds Hbound; simpl in *;
    destruct (coef >? 0) eqn:Hsign; inversion Hbound; subst; try nia.
Qed.

Lemma negated_atom_on_valid : forall sol x premises negated a premises',
  (forall y b, negated = Some (y, b) -> atomic_holds (sol y) b) ->
  negated_atom_on x premises negated = Some (a, premises') ->
  atomic_holds (sol x) a /\ premises' = premises.
Proof.
  unfold negated_atom_on.
  intros sol x premises [[y b]|] a premises' Hnegated Hnext; try discriminate.
  destruct (String.eqb_spec x y); inversion Hnext; subst; eauto.
Qed.

Lemma next_atom_on_valid : forall sol x premises negated a premises',
  valid_atoms sol premises ->
  (forall y b, negated = Some (y, b) -> atomic_holds (sol y) b) ->
  next_atom_on x premises negated = Some (a, premises') ->
  atomic_holds (sol x) a /\ valid_atoms sol premises'.
Proof.
  unfold next_atom_on, valid_atoms.
  intros sol x [|[y b] tail] negated a premises' Hpremises Hnegated Hnext; simpl in *.
  - apply negated_atom_on_valid with (sol := sol) in Hnext as [? ->]; eauto.
  - destruct (String.eqb_spec x y).
    + inversion Hnext; subst; split; eauto.
    + apply negated_atom_on_valid with (sol := sol) in Hnext as [? ->]; eauto.
Qed.

Lemma scan_bound_validity : forall terms sol premises negated bound,
  valid_atoms sol premises ->
  (forall y b, negated = Some (y, b) -> atomic_holds (sol y) b) ->
  scan_linear_lower_bound terms premises negated = Some bound ->
  bound <= evaluate_linear terms sol.
Proof.
  induction terms as [|[coef [x|value]] tail IH]; simpl;
    intros sol premises negated bound Hpremises Hnegated Hscan.
  - inversion Hscan; lia.
  - destruct next_atom_on as [[a premises']|] eqn:Hnext; try discriminate.
    apply next_atom_on_valid with (sol := sol) in Hnext as [Ha Hpremises']; eauto.
    destruct atom_term_lower_bound as [value|] eqn:Hterm; try discriminate.
    destruct scan_linear_lower_bound as [acc|] eqn:Htail; inversion Hscan; subst.
    apply atom_term_lower_bound_validity with (val := sol x) in Hterm; try assumption.
    enough (acc <= evaluate_linear tail sol) by lia.
    eauto.
  - destruct scan_linear_lower_bound as [acc|] eqn:Htail; inversion Hscan; subst.
    enough (acc <= evaluate_linear tail sol) by lia.
    eauto.
Qed.

Theorem linear_scan_checker_soundness : forall
  (fact : ProofFact) (sol : Assignment) (c : LinearConstraint),
  Linear c sol ->
  linear_scan_checker fact c = true ->
  fact_valid sol fact.
Proof.
  unfold linear_scan_checker, Linear.
  intros [premises consequent] sol c Hsat Hcheck; simpl in *.
  destruct scan_linear_lower_bound as [lb|] eqn:Hscan; try discriminate.
  apply Z.gtb_gt in Hcheck.
  destruct consequent as [consequent|].
  - apply inference_valid_neg_rhs.
    intros Hatoms.
    enough (lb <= evaluate_linear (l_terms c) sol) by lia.
    apply scan_bound_validity with (premises := premises) (negated := Some (negate_bound_atomic consequent)); eauto.
    + intros x a Hin; apply Hatoms; simpl; eauto.
    + intros y b Hneg; apply Hatoms; left; congruence.
  - intros Hpremises.
    enough (lb <= evaluate_linear (l_terms c) sol) by lia.
    apply scan_bound_validity with (premises := premises) (negated := None); easy.
Qed.

Definition linear_checker (fact : ProofFact) (c : LinearConstraint) :=
  linear_scan_checker fact c || linear_store_checker fact c.

Theorem linear_checker_soundness : forall
  (fact : ProofFact) (sol : Assignment) (c : LinearConstraint),
  Linear c sol ->
  Is_true (linear_checker fact c)
  -> fact_valid sol fact.
Proof.
  unfold linear_checker.
  intros fact sol c Hsat Hcheck.
  destruct linear_scan_checker eqn:Hscan; eauto using linear_scan_checker_soundness, linear_store_checker_soundness.
Qed.


Definition negate (c : LinearConstraint) :=
  {|
    l_terms := map (fun x : (Z * Var) => let (coef, var) := x in (-coef, var)) (l_terms c);
    l_bound := -(l_bound c)
  |}.

Lemma equality_via_negate : forall (c : LinearConstraint) (sol : string -> Z),
  LinearEq c sol -> Linear c sol /\ Linear (negate c) sol.
Proof.
  unfold LinearEq, Linear.
  intros c sol Heq.
  split ; apply Z.eq_le_incl ; try assumption.
  unfold negate.
  simpl.
  remember (l_terms c) as terms.
  remember (l_bound c) as bound.
  clear Heqterms Heqbound c.
  generalize dependent bound.
  induction terms ; simpl ; intros bound Heq.
  - rewrite <- Heq.
    reflexivity.
  - destruct a.
    remember (evaluate_linear terms sol) as tail_bound.
    rewrite Heqtail_bound in IHterms.
    symmetry in Heqtail_bound.
    specialize (IHterms tail_bound Heqtail_bound).
    rewrite IHterms.
    unfold evaluate_term.
    unfold evaluate_term in Heq.
    lia.
Qed.

Definition linear_eq_checker (fact : ProofFact) (c : LinearConstraint) :=
  linear_scan_checker fact c || linear_scan_checker fact (negate c)
  || linear_store_checker fact c || linear_store_checker fact (negate c).

Theorem linear_eq_checker_soundness : forall
  (fact : ProofFact) (sol : string -> Z) (c : LinearConstraint),
  LinearEq c sol ->
  linear_eq_checker fact c = true ->
  fact_valid sol fact.
Proof.
  intros fact sol c Heq Hvalid.
  apply equality_via_negate in Heq as [Hbound Hneg].
  unfold linear_eq_checker in Hvalid.
  repeat rewrite orb_true_iff in Hvalid.
  destruct Hvalid as [[[Hvalid | Hvalid] | Hvalid] | Hvalid];
    eauto using linear_scan_checker_soundness, linear_store_checker_soundness, Is_true_eq_left.
Qed.
