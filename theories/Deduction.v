Require Import Coq.ZArith.ZArith.
Require Import String.
Require Import Coq.Lists.List.
Require Import Arith.PeanoNat.
Require Import Bool.
Require Import Lia.
Require Checker.Utility.
Import Utility.ListEx.
Import Utility.ListInd.
Import Utility.Maps.
Import Utility.Tactics.
Import Utility.Sets.
Require Import Checker.Domain.
Require Import Checker.DomainVar.
Require Import Checker.Spec.
Import Spec.ProofFacts.
Local Open Scope Domain_scope.
(** This file represents the process of verifying a deduction step, although it does not actually mention the deduction itself so there is still some freedom to implement it. Given a number of valid inferences and premises we assume to hold, if the checker returns true we know we have a contradiction (hence of the premises must have been incorrect). *)



Definition negate_bound_atomic (atomic : BoundAtomic) :=
  match atomic with
  | (x, atomic) =>
    (x, negate_atomic atomic)
  end.



(** Check whether a premise holds. *)
Definition check_premise (domains : Domains) (premise : BoundAtomic) := 
  match premise with
  | (x, a) =>
    match smap.find x domains with
    | Some dom =>
      check_holds a dom
    | None => false
    end
  end.

(** We either reject if not all the premises hold, apply the consequent or indicate it is valid because we derived a conflict. Note that we use add_apply without any condition on the variables (vs = None) since here we want to consider all variables. *)
Inductive DeductStep :=
| deduct_domains (domains : smap.t Domain)
| deduct_valid
| deduct_reject.

Definition step_inference (fact : ProofFact) (domains : Domains) :=
  if forallb (check_premise domains) fact.(i_premises)
    then
      match fact.(i_consequent) with
      | None => deduct_valid
      | Some consequent =>
        match doms_apply_tighten domains consequent with
        | None => deduct_valid
        | Some domains => deduct_domains domains
        end
      end
    else deduct_reject.

Fixpoint deduct_check_inferences (facts : list ProofFact) (domains : Domains) : bool :=
  match facts with
  | nil => false
  | fact :: facts' =>
    match step_inference fact domains with
    | deduct_domains domains' => deduct_check_inferences facts' domains'
    | deduct_valid => true
    | deduct_reject => false
    end
  end.

Definition check_deduct (premises : list BoundAtomic) (steps : list ProofFact) :=
  let doms := domains_from_atomics premises in
  let doms_tight := tighten_doms doms in
    if check_domains_consistent doms
      then deduct_check_inferences steps doms_tight
      (* Inconsistent premises, which we do not expect *)
      else false.

Lemma inference_valid_neg_rhs :
  forall sol premises consequent,
    fact_valid sol (mkFact premises (Some consequent))
      <->
    fact_valid sol (mkFact ((negate_bound_atomic consequent) :: premises) None).
Proof.
  intros sol premises consq.
  unfold fact_valid.
  destruct consq as [x consqa]; simpl.
  split; intros Hvalid; intros H.
  - assert (valid_atoms sol premises) as Hpremises.
    { unfold valid_atoms; intros x' a' Hin.
      apply H. right; assumption. }
    apply Hvalid in Hpremises.
    apply negate_atomic_not in Hpremises.
    apply Hpremises.
    apply H.
    left. reflexivity.
  - rewrite negate_atomic_not.
    intros Hneg.
    apply Hvalid.
    intros x' a' [Hisx | Hinpremises].
    + inversion Hisx; subst; clear Hisx.
      exact Hneg.
    + apply H.
      exact Hinpremises.
Qed. 

Lemma forall_premises :
  forall doms assignment atoms premises,
  forallb (check_premise doms) premises = true
    ->
  valid_atoms assignment atoms
    ->
  valid_domains doms atoms
    ->
  valid_atoms assignment premises.
Proof.
  intros doms assignment atoms premises.
  intros Hforall Hvalid Hequiv.
  unfold valid_atoms.
  intros x a Hin.
  apply check_holds_implies with (dom := doms d-> x).
  - rewrite (Hequiv x).
    unfold applied_dom. rewrite dom_effect_atomics.
    split; try easy.
    intros a' Hin'.
    apply Hvalid.
    rewrite <- filter_pair_on_key_spec.
    apply Hin'.
  - rewrite forallb_forall in Hforall.
    apply Hforall in Hin; clear Hforall.
    unfold check_premise in Hin.
    destruct smap.find eqn:Hfind; try discriminate Hin.
    rewrite smap.find_spec in Hfind.
    rewrite <- smap_in_spec in Hfind.
    apply dom_from_domains_if_in in Hfind; subst d.
    assumption.
 Qed.

(** This is the main inductive proof. Separating it out is important so that we can put domains_equiv_atoms as a hypothesis so that we have enough information in our induction hypothesis. *)
Lemma deduct_check_inferences_correct :
  forall assignment steps domains atoms,
    valid_atoms assignment atoms
      ->
    valid_domains domains atoms
      ->
    (forall fact, In fact steps -> fact_valid assignment fact)
      ->
    deduct_check_inferences steps domains = true
      ->
    False.
Proof.
  intros assignment.
  induction steps as [|step steps IH].
  { easy. }
  intros doms atoms Hatoms Hequiv Hinfs.
  simpl.
  assert (forall fact, In fact steps -> fact_valid assignment fact) as Hprev.
  { intros fact Hin. apply Hinfs. now right. }
  assert (fact_valid assignment step) as Hstep.
  { apply Hinfs. now left. }
  clear Hinfs.
  destruct step_inference as [doms' | |] eqn:Hinf.
  - unfold step_inference in Hinf.
    destruct forallb eqn:Hforall in Hinf;
    try discriminate Hinf.
    unfold fact_valid in Hstep.
    destruct i_consequent as [conseq|];
    try discriminate Hinf.
    apply forall_premises with (assignment := assignment) (atoms := atoms) in Hforall; try assumption.
    apply Hstep in Hforall as Hconseq; clear Hstep Hforall.
    apply IH with (domains := doms') (atoms := conseq :: atoms); try apply Hprev; clear IH.
    {
      unfold valid_atoms. intros x a.
      intros Hin.
      destruct Hin as [Hconseqxa | Hprevatoms].
      - subst conseq. apply Hconseq.
      - apply Hatoms. exact Hprevatoms.
    }
    destruct conseq as [x a].
    clear Hprev.
    specialize (doms_apply_tighten_step doms atoms Hequiv x a) as Happly_spec.
    destruct doms_apply_tighten as [doms_apply|] eqn:Happly;
    try discriminate Hinf.
    inversion Hinf; subst doms_apply; clear Hinf.
    apply Happly_spec.
  - intros _; clear IH.
    unfold step_inference in Hinf.
    destruct forallb eqn:Hforall in Hinf;
    try discriminate Hinf.
    unfold fact_valid in Hstep.
    destruct i_consequent as [conseq|].
    + destruct conseq as [x a].
      specialize (doms_apply_tighten_step doms atoms Hequiv x a) as Happly_spec.
      destruct doms_apply_tighten eqn:Happly;
      try discriminate Hinf.
      apply Happly_spec; clear Happly_spec Happly.
      apply dom_consistent_if_valid_atoms with (sol := assignment).
      unfold valid_atoms.
      intros x' a'.
      intros [Hxx' | Hin].
      * inversion Hxx'; subst. apply Hstep.
        apply forall_premises with (doms := doms) (atoms := atoms); assumption.
      * apply Hatoms. exact Hin.
    + apply Hstep.
      apply forall_premises with (doms := doms) (atoms := atoms); assumption.
  - easy.
Qed. 

(** This is the main correctness proof that factors out the use of the domain map. *)
Lemma check_deduct_correct :
  forall assignment premises steps,
    valid_atoms assignment premises
      ->
    (forall inf, In inf steps -> fact_valid assignment inf)
      ->
    check_deduct premises steps = true
      ->
    False.
Proof.
  intros assignment.
  intros premises steps Hvalid Hinfs.
  specialize domains_from_atomics_correct with (atoms := premises) as Hdomains.
  unfold check_deduct.
  destruct check_domains_consistent; try easy.
  apply deduct_check_inferences_correct with (assignment := assignment) (atoms := premises).
  - exact Hvalid.
  - unfold valid_domains.
    intros x. 
    rewrite tighten_doms_equiv.
    apply Hdomains. reflexivity.
  - exact Hinfs.
Qed.

Definition check_in_vs (vs : sstr.t) (a : BoundAtomic) :=
  match a with 
  | (x, atom) => sstr.mem x vs
  end.

Definition atomics_from_fact (fact : ProofFact) :=
  match fact.(i_consequent) with
  | None => (None, fact.(i_premises))
  | Some (x, consq) => (Some x, (negate_bound_atomic (x, consq)) :: fact.(i_premises))
  end.

Definition infer_domains (fact : ProofFact) :=
  let (x, atomics) := atomics_from_fact fact in
  let doms := domains_from_atomics atomics in
  let doms_tight := tighten_doms doms in
  if check_domains_consistent doms_tight
    then Some (doms_tight, x)
    else None.

Lemma infer_domains_valid_as_nogood fact doms xconsq :
  forall sol, 
    infer_domains fact = Some (doms, xconsq)
      ->
    exists atoms,
      valid_domains doms atoms
        /\
      (fact_valid sol (mkFact atoms None) <-> fact_valid sol fact).
Proof.
  intros sol.
  unfold infer_domains.
  destruct atomics_from_fact as [x atomics'] eqn:Hatomics'.
  destruct check_domains_consistent; try discriminate.
  intros H; inversion H; subst; clear H.
  unfold atomics_from_fact in Hatomics'.
  destruct i_consequent as [(x & consq)|] eqn:Hconsq.
  - inversion Hatomics'; subst; clear Hatomics'.
    exists ((x, negate_atomic consq) :: i_premises fact). 
    destruct fact as [premises [[x' consq'] | ]].
    2: { discriminate Hconsq. }
    simpl in *; inversion Hconsq; subst x' consq'; clear Hconsq.
    split.
    + remember ((x, negate_atomic consq) :: premises) as atoms; clear.
      intros x. rewrite tighten_doms_equiv.
      apply domains_from_atomics_correct.
      reflexivity.
    + rewrite inference_valid_neg_rhs.
      reflexivity.
  - exists (i_premises fact).
    inversion Hatomics'; subst.
    destruct fact as [premises [xconsq | ]]; simpl in *; try discriminate. 
    split.
    + clear.
      intros x. rewrite tighten_doms_equiv.
      apply domains_from_atomics_correct.
      reflexivity.
    + reflexivity.
Qed.

(** This lemma is primarily useful for inference checkers. *)
Lemma infer_domains_correct fact doms xconsq :
  forall sol, 
    infer_domains fact = Some (doms, xconsq)
      ->
    ~ sol_in_doms sol doms 
      <->
    fact_valid sol fact.
Proof.
  intros sol.
  intros Hinfer.
  apply infer_domains_valid_as_nogood with (sol := sol) in Hinfer.
  destruct Hinfer as (atoms & Hvalid & Hinf_valid_atoms).
  rewrite <- Hinf_valid_atoms; clear Hinf_valid_atoms.
  unfold fact_valid; simpl.
  now rewrite <- valid_domains_sol_in_doms_iff_valid_atoms with (atoms := atoms).
Qed.

Lemma equiv_domains (sol : string -> Z) :
  forall doms doms',
  smap.Equivb Domain.eqb doms doms'
    ->
  sol_in_doms sol doms
    <->
  sol_in_doms sol doms'.
Proof.
  intros doms doms'.
  intros Hequiv.
  unfold smap.Equivb in Hequiv.
  destruct Hequiv as [Heqdoms Heqmaps].
  unfold smap.Eqdom in Heqdoms.
  assert (forall x, dom_equiv (doms d-> x) (doms' d-> x)) as Hdom_equiv.
  {
    assert (forall x, smap.MapsTo x (doms d-> x) doms <-> smap.MapsTo x (doms' d-> x) doms').
    {
      clear Heqmaps.
      intros x.
      specialize (Heqdoms x).
      setoid_rewrite smap_prps.in_find in Heqdoms.
      unfold dom_from_domains.
      setoid_rewrite <- smap.find_spec.
      destruct (smap.find x doms) eqn:Hfind; destruct (smap.find x doms') eqn:Hfind'; simpl; try easy.
      - exfalso.      
        assert (Some d <> None) by easy.
        now rewrite Heqdoms in H.
      - exfalso.
        assert (Some d <> None) by easy.
        now rewrite <- Heqdoms in H.
    }
    intros x.
    destruct (doms_maps_or_not_included doms x) as [Hmaps | [Hinitial Hnin]].
    2: { 
      rewrite Hinitial. 
      destruct (doms_maps_or_not_included doms' x) as [Hmaps' | [Hinitial' Hnin']].
      - rewrite <- H in Hmaps'.
        rewrite <- smap_in_spec in Hmaps'.
        specialize (Hnin (doms d-> x)). 
        contradiction.
      - rewrite Hinitial'.
        reflexivity.
    }
    pose proof Hmaps as Hmaps'.
    rewrite H in Hmaps'.
    specialize (Heqmaps x (doms d-> x) (doms' d-> x) Hmaps Hmaps').
    unfold Raw.Cmp in Heqmaps.
    apply Domain.eqb_eq.
    exact Heqmaps.
  }
  split; intros H.
  - intros x. 
    rewrite <- Hdom_equiv.
    apply H.
  - intros x.
    rewrite Hdom_equiv.
    apply H.
Qed.

(* TODO: currently eqb assumes the holes are exactly the same, but infer_domains does not remove redundant holes. To fix this, Domain.eqb should be changed to be more like an 'equivb', i.e. it should only look for equality of the holes within the bounds. Note: infer_domains DOES already tighten the bounds themselves, so there equality is totally fine. *)
Definition equiv (lhs : ProofFact) (rhs : ProofFact) :=
  match (infer_domains lhs), (infer_domains rhs) with
  | Some (lhs_doms, _), Some (rhs_doms, _) =>
      smap.equal Domain.eqb lhs_doms rhs_doms
  | _, _ => false
  end.

Lemma equiv_implies_equisat : forall lhs rhs,
  equiv lhs rhs = true ->
  (forall sol, fact_valid sol lhs <-> fact_valid sol rhs).
Proof.
  intros lhs rhs Hequiv sol.
  unfold equiv in Hequiv.
  destruct (infer_domains lhs) as [[dom_lhs str_lhs] | ] eqn:Elhs ;
  destruct (infer_domains rhs) as [[dom_rhs str_rhs] | ] eqn:Erhs ;
  inversion Hequiv.
  apply smap_prps.equal_2 in Hequiv.
  apply equiv_domains with (sol := sol )in Hequiv.
  rewrite <- infer_domains_correct with (doms := dom_lhs).
  rewrite <- infer_domains_correct with (doms := dom_rhs).
  - rewrite Hequiv. reflexivity.
  - apply Erhs.
  - apply Elhs.
Qed.
