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

(** This file represents the process of verifying a deduction step, although it does not actually mention the deduction itself so there is still some freedom to implement it. Given a number of valid inferences and premises we assume to hold, if the checker returns true we know we have a contradiction (hence of the premises must have been incorrect). *)

(** An inference is a set of premises and a consequent. If the consequent is None, it represents a nogood. *)
Record Inference := mkInf {
  i_premises : list BoundAtomic;
  i_consequent : option BoundAtomic
}.


Definition negate_bound_atomic (atomic : BoundAtomic) :=
  match atomic with
  | (x, atomic) =>
    (x, negate_atomic atomic)
  end.



(** Check whether a premise holds. *)
Definition check_premise (domains : DomainMap) (premise : BoundAtomic) := 
  match premise with
  | (x, a) =>
    match smap.find x domains with
    | Some dom =>
      check_holds a dom.(d_lb) dom.(d_ub) dom.(d_holes)
    | None => false
    end
  end.

(** We either reject if not all the premises hold, apply the consequent or indicate it is valid because we derived a conflict. Note that we use add_apply without any condition on the variables (vs = None) since here we want to consider all variables. *)
Inductive DeductStep :=
| deduct_domains (domains : smap.t Domain)
| deduct_valid
| deduct_reject.

Definition step_inference (inference : Inference) (domains : DomainMap) :=
  if forallb (check_premise domains) inference.(i_premises)
    then
      match inference.(i_consequent) with
      | None => deduct_valid
      | Some consequent =>
        match add_apply None domains consequent with
        | None => deduct_valid
        | Some domains => deduct_domains domains
        end
      end
    else deduct_reject.

Fixpoint deduct_check_inferences (inferences : list Inference) (domains : DomainMap) : bool :=
  match inferences with
  | nil => false
  | inf :: inferences' =>
    match step_inference inf domains with
    | deduct_domains domains' => deduct_check_inferences inferences' domains'
    | deduct_valid => true
    | deduct_reject => false
    end
  end.

Definition check_deduct (premises : list BoundAtomic) (steps : list Inference) :=
  match domains_from_var_atomics_all premises None with
  | None =>
    (** This means we have a trivial nogood, decide what to do *)
      true
  | Some domains => deduct_check_inferences steps domains
  end.

Definition bound_atomic_holds (assignment : string -> Z) (atom : BoundAtomic) :=
  match atom with
  | (x, atom) =>
    atomic_holds (assignment x) atom
  end.

(** If the premises hold for the assignment, then the consequent holds *)
Definition inference_valid (assignment : string -> Z) (inference : Inference) :=
  valid_atoms assignment inference.(i_premises)
    ->
  match inference.(i_consequent) with
  | None => False
  | Some consequent => bound_atomic_holds assignment consequent
  end.

Lemma inference_valid_neg_rhs :
  forall sol premises consequent,
    inference_valid sol (mkInf premises (Some consequent))
      <->
    inference_valid sol (mkInf ((negate_bound_atomic consequent) :: premises) None).
Proof.
  intros sol premises consq.
  unfold inference_valid.
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
  forall doms assignment atoms cpremises,
  forallb (check_premise doms) cpremises = true
    ->
  valid_atoms assignment atoms
    ->
  domains_equiv_atoms atoms doms   
    ->
  valid_atoms assignment cpremises.
Proof.
  intros doms assignment atoms cpremises.
  intros Hforall Hvalid Hequiv. 
  rewrite forallb_forall in Hforall.
  unfold valid_atoms.
  intros x a Hin.
  apply Hforall in Hin; clear Hforall.
  unfold check_premise in Hin.
  specialize (Hequiv x).
  destruct smap.find; try discriminate Hin.
  apply dom_equiv_holds with (y := assignment x) in Hequiv.
  - apply check_holds_implies with (dom := d); assumption.
  - intros a' Hinprem.
    apply Hvalid.
    rewrite <- filter_pair_on_key_spec.
    apply Hinprem.
Qed.

(** This is the main inductive proof. Separating it out is important so that we can put domains_equiv_atoms as a hypothesis so that we have enough information in our induction hypothesis. *)
Lemma deduct_check_inferences_correct :
  forall assignment steps domains atoms,
    valid_atoms assignment atoms
      ->
    domains_equiv_atoms atoms domains
      ->
    (forall inf, In inf steps -> inference_valid assignment inf)
      ->
    deduct_check_inferences steps domains = true
      ->
    False.
Proof.
  intros assignment.
  induction steps as [|step steps IH].
  - intros doms atoms Hequiv Hinfs.
    easy.
  - intros doms atoms Hatoms Hequiv Hinfs.
    simpl.
    assert (forall inf, In inf steps -> inference_valid assignment inf) as Hprev.
    { intros inf Hin. apply Hinfs. now right. }
    assert (inference_valid assignment step) as Hstep.
    { apply Hinfs. now left. }
    clear Hinfs.
    destruct step_inference as [doms' | |] eqn:Hinf.
    + unfold step_inference in Hinf.
      destruct forallb eqn:Hforall in Hinf;
      try discriminate Hinf.
      unfold inference_valid in Hstep.
      destruct i_consequent as [conseq|];
      try discriminate Hinf.
      apply forall_premises with (assignment := assignment) (atoms := atoms) in Hforall; try assumption.
      apply Hstep in Hforall as Hconseq; clear Hstep Hforall.
      destruct add_apply eqn:Happly in Hinf;
      try discriminate Hinf.
      inversion Hinf; subst d; clear Hinf.
      apply IH with (domains := doms') (atoms := conseq :: atoms); try apply Hprev; clear IH.
      {
        unfold valid_atoms. intros x a.
        intros Hin.
        destruct Hin as [Hconseqxa | Hprevatoms].
        - subst conseq. apply Hconseq.
        - apply Hatoms. exact Hprevatoms.
      }
      clear Hprev.
      destruct conseq as [x a].
      specialize add_apply_step with (vs := None) as Hadd_apply.
      setoid_rewrite check_in_vs_none_domains_equiv in Hadd_apply.
      apply Hadd_apply with (x := x) (a := a) in Hequiv;
      clear Hadd_apply.
      rewrite Happly in Hequiv.
      setoid_rewrite check_in_vs_none_domains_equiv in Hequiv.
      apply Hequiv.
    + clear IH.
      unfold step_inference in Hstep.
      intros _.
      unfold step_inference in Hinf.
      destruct forallb eqn:Hforall in Hinf;
      try discriminate Hinf.
      unfold inference_valid in Hstep.
      destruct i_consequent as [conseq|].
      * destruct add_apply eqn:Happly in Hinf;
        try discriminate Hinf.
        clear Hinf.
        destruct conseq as [x a].
        specialize add_apply_step with (vs := None) as Hadd_apply.
        setoid_rewrite check_in_vs_none_domains_equiv in Hadd_apply.
        pose proof Hequiv as Hequiv'.
        apply Hadd_apply with (x := x) (a := a) in Hequiv;
        clear Hadd_apply.
        rewrite Happly in Hequiv.
        apply applied_dom_none_false with (f := assignment) (x := x) (atoms := (x, a) :: atoms).
        -- unfold valid_atoms.
          intros x' a' [Hxa | Hin].
          ++ inversion Hxa; subst; clear Hxa.
            apply Hstep.
            apply forall_premises with (doms := doms) (atoms := atoms); assumption.
          ++ apply Hatoms.
            exact Hin.
        -- apply Hequiv.
      * clear Hinf. apply Hstep.
        apply forall_premises with (doms := doms) (atoms := atoms); assumption.
    + easy.
Qed. 

(** This is the main correctness proof that factors out the use of the domain map. *)
Lemma check_deduct_correct :
  forall assignment premises steps,
    valid_atoms assignment premises
      ->
    (forall inf, In inf steps -> inference_valid assignment inf)
      ->
    check_deduct premises steps = true
      ->
    False.
Proof.
  intros assignment.
  intros premises steps Hvalid Hinfs.
  specialize domains_from_var_atomics_all_correct with (vs := None) (atoms := premises) as Hdomains.
  unfold domains_from_vars_P in Hdomains.
  unfold check_deduct.
  destruct domains_from_var_atomics_all as [doms|].
  - apply deduct_check_inferences_correct with (assignment := assignment) (atoms := premises).
    + exact Hvalid.
    + unfold domains_equiv_atoms.
      intros x. specialize (Hdomains x).
      destruct smap.find.
      * now apply Hdomains.
      * now destruct Hdomains.
    + exact Hinfs.
  - intros _.
    destruct Hdomains as [x H].
    apply applied_dom_none_false with (f := assignment) (atoms := premises) (x := x); assumption.
Qed.

Definition infer_domains (vs : option sstr.t) (fact : Inference) :=
  match domains_from_var_atomics_all (fact.(i_premises)) vs with
  | None => None
  | Some doms =>
    match fact.(i_consequent) with
    | None => Some (doms, None)
    | Some (x, consq) =>
      match add_apply vs doms (x, (negate_atomic consq)) with
      | None => None
      | Some doms => Some (doms, Some x)
      end
    end
  end.

(** This is the main lemma to make use of vs, which ensures that all output variables will be in a particular set. Useful for ensuring that you get a result when matching against some map of parameters (see e.g. cumulative).  *)
Lemma infer_domains_vs :
  forall vs fact x dom doms c,
    infer_domains (Some vs) fact = Some (doms, c)
      ->
    In (x, dom) (smap.bindings doms)
      ->
    sstr.In x vs.
Proof.
  intros vs fact x dom doms c.
  unfold infer_domains.
  destruct domains_from_var_atomics_all as [doms'|] eqn:Hdoms_from; try discriminate.
  intros Hdoms.
  enough (exists atoms, domains_equiv_atoms_vs (Some vs) atoms doms) as Hvs.
  { clear -Hvs.
    destruct Hvs as [atoms Hvs].
    unfold domains_equiv_atoms_vs, domains_equiv_atoms_cond in Hvs.
    rewrite In_to_InA_Duo_eq.
    rewrite smap.bindings_spec1.
    rewrite <- smap.find_spec.
    intros Hfind.
    specialize (Hvs x).
    rewrite Hfind in Hvs.
    destruct Hvs as [Hvs _].
    unfold check_in_vs in Hvs.
    rewrite <- sstr.mem_spec.
    exact Hvs.
  }
  assert (domains_equiv_atoms_vs (Some vs) (i_premises fact) doms') as Hdoms'.
    { enough (domains_from_vars_P (Some vs) (i_premises fact) (Some doms')).
      - assumption.
      - setoid_rewrite <- Hdoms_from. apply domains_from_var_atomics_all_correct. }
  destruct i_consequent as [[cx ca]|].
  - destruct add_apply as [doms''|] eqn:Hadd_apply;
    try discriminate.
    inversion Hdoms; subst; clear Hdoms.
    specialize (add_apply_step (Some vs) doms' (i_premises fact)) as Hstep.
    rename Hdoms' into Hstep'.
    apply Hstep with (x := cx) (a := (negate_atomic ca)) in Hstep'; clear Hstep.
    rewrite Hadd_apply in Hstep'.
    exists ((cx, negate_atomic ca) :: i_premises fact).
    exact Hstep'.
  - inversion Hdoms; subst; clear Hdoms.
    exists (i_premises fact).
    exact Hdoms'.
Qed.

(** This lemma is primarily useful for inference checkers. *)
Lemma infer_domains_correct fact vs doms xconsq :
  forall sol, 
    infer_domains vs fact = Some (doms, xconsq)
      ->
    (doms_hold_for_sol sol doms
      ->
    False)
      ->
    inference_valid sol fact.
Proof.
  intros sol.
  unfold infer_domains.
  destruct domains_from_var_atomics_all as [doms'|] eqn:Hdoms_from; try discriminate.
  destruct i_consequent as [[x consq]|] eqn:Hconsq.
  - destruct add_apply as [doms_x|] eqn:Happly; try discriminate.
    intros H; inversion H; subst; clear H.
    intros Hdoms_hold.
    assert (fact = mkInf (i_premises fact) (Some (x, consq))).
    { destruct fact. simpl in Hconsq. subst. reflexivity. }
    rewrite H. apply inference_valid_neg_rhs.
    unfold inference_valid. simpl.
    intros Hatoms.
    apply Hdoms_hold; clear Hdoms_hold.
    remember ((x, negate_atomic consq) :: i_premises fact) as atoms.
    enough (domains_from_vars_P vs atoms (Some doms)) as Henough.
    { apply doms_hold_for_sol_from_domains_var_P with (vs := vs) (atoms := atoms).
      - apply Hatoms.
      - apply Henough. }
    unfold domains_from_vars_P.
    rewrite Heqatoms.
    specialize (add_apply_step vs doms' (i_premises fact)) with (x := x) (a := (negate_atomic consq)) as Hstep.
    rewrite Happly in Hstep.
    apply Hstep.
    clear -Hdoms_from.
    enough (domains_from_vars_P vs (i_premises fact) (Some doms')).
    + apply H.
    + setoid_rewrite <- Hdoms_from. 
      apply domains_from_var_atomics_all_correct.
  - intros H; inversion H; subst; clear H.
    intros Hdoms_hold.
    unfold inference_valid.
    intros Hatoms.
    rewrite Hconsq.
    apply Hdoms_hold.
    now apply doms_from_var_all_hold with (vs := vs) (atoms := (i_premises fact)).
Qed.