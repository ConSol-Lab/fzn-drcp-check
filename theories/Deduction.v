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
Require Import Checker.Domain.
Require Import Checker.DomainVar.

Definition BoundAtomic := (string * Atomic)%type.
Record Inference := {
  i_premises : list BoundAtomic;
  i_consequent : option BoundAtomic
}.

Definition check_premise (domains : DomainMap) (premise : BoundAtomic) := 
  match premise with
  | (x, a) =>
    match smap.find x domains with
    | Some dom =>
      check_holds a dom.(d_lb) dom.(d_ub) dom.(d_holes)
    | None => false
    end
  end.

(* Definition apply_variable_atomic (domains : smap.t Domain) (consequent : string * Atomic) : option (smap.t Domain) :=
  match consequent with
  | (x, a) =>
    let (bounds, holes) := 
      match smap.find x domains with
      | Some dom => (dom.(d_lb), dom.(d_ub), dom.(holes))
      | None => (None, None, sint.empty)
      end in
    let (lb, ub) := bounds in
    match apply_atomics (a :: nil) lb ub holes with
    | None => None
    | Some (lb, ub, holes) => 
      let new_dom := mkDom x lb ub holes in
      Some (smap.add x new_dom domains)
    end
  end.
 *)
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

Definition domains_equiv_atoms (atoms : list BoundAtomic) (domains : DomainMap) :=
  forall x,
    match smap.find x domains with
    | None => forall a, ~ In (x, a) atoms
    | Some dom => dom_equiv (Some dom) (applied_dom x atoms)
    end.

Definition check_deduct (premises : list BoundAtomic) (steps : list Inference) :=
  match domains_from_var_atomics_all premises None with
  | None =>
    (* This means we have a trivial nogood, decide what to do *)
      true
  | Some domains => deduct_check_inferences steps domains
  end.

Definition bound_atomic_holds (assignment : string -> Z) (atom : BoundAtomic) :=
  match atom with
  | (x, atom) =>
    atomic_holds (assignment x) atom
  end.

Definition inference_valid (assignment : string -> Z) (inference : Inference) :=
  valid_atoms assignment inference.(i_premises)
    ->
  match inference.(i_consequent) with
  | None => False
  | Some consequent => bound_atomic_holds assignment consequent
  end.

Ltac clean_if_easy H :=
  match type of H with
  | ?P => 
    try (
      assert P by easy;
      clear H
    )
  end.

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

Lemma check_in_vs_none_domains_equiv :
  forall atoms doms,
  (forall x : string,
  check_in_vs None x = true ->
  domains_equiv_atoms_x atoms doms x)
    <->
  domains_equiv_atoms atoms doms.
Proof.
  intros atoms doms.
  split; intros; 
  unfold domains_equiv_atoms, domains_equiv_atoms_x in *.
  - intros x.
    apply H.
    reflexivity.
  - apply H.
Qed.


Lemma deduct_check_inferences_cons :
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
  specialize domains_from_var_atomics_all_correct with (vs := None) as Hdomains.
  unfold domains_from_vars_P in Hdomains.
  induction steps as [|step steps IH].
  - intros Hpremises Hinf.
    unfold check_deduct.
    specialize (Hdomains premises).
    destruct domains_from_var_atomics_all as [doms|].
    + simpl. easy.
    + intros _.
      destruct Hdomains as [x H].
      apply applied_dom_none_false with (f := assignment) (atoms := premises) (x := x); assumption.
  - intros Hpremises. specialize (IH Hpremises).
    intros Hinfs.
    assert (forall inf, In inf steps -> inference_valid assignment inf) as Hprev.
    { intros inf Hin. apply Hinfs. now right. }
    assert (inference_valid assignment step) as Hstep.
    { apply Hinfs. now left. }
    clear Hinfs; specialize (IH Hprev).
    unfold check_deduct in *.
    specialize (Hdomains premises).
    destruct domains_from_var_atomics_all as [doms|].
    + simpl. destruct step_inference as [doms'| |] eqn:Hinf.
      { 
        intros Hsteps_true.
        unfold step_inference in Hinf.
        destruct forallb eqn:Hforall in Hinf;
        try discriminate Hinf.
        destruct i_consequent as [conseq|] in Hinf;
        try discriminate Hinf.
        destruct add_apply eqn:Happly in Hinf;
        try discriminate Hinf.
        inversion Hinf; subst d; clear Hinf.
        simpl in Hdomains.
        admit.
        (* apply forall_premises with (assignment := assignment) (atoms := ) in Hforall.
 *)
      }
      {
        unfold step_inference in Hinf.
        unfold inference_valid in Hstep.
        destruct forallb eqn:Hforall in Hinf;
        try discriminate Hinf.
        destruct i_consequent as [conseq|] eqn:Hconseq.
        { 
          destruct add_apply eqn:Happly in Hinf;
          try discriminate Hinf.
          intros _; clear Hinf.
          admit.
        }
        { 
          intros _.
          clear IH Hinf.
          apply Hstep.
          apply forall_premises with (dom_map := doms) (atoms := premises).
          - apply Hforall.
          - apply Hpremises.
          - apply Hdomains. 
        }
      }
      { easy. }
    + intros _.
      destruct Hdomains as [x H].
      apply applied_dom_none_false with (f := assignment) (atoms := premises) (x := x); assumption.
Qed.


  intros Hatoms.
  intros Hinfs.
  unfold check_deduct.
  specialize domains_from_var_atomics_all_correct with (atoms := premises) (vs := None) as Hdomains.
  unfold domains_from_vars_P in Hdomains.
  destruct domains_from_var_atomics_all as [doms|].
  - generalize dependent doms.
    induction steps as [| step steps IH]; try easy.
    simpl. intros doms.
    assert (forall inf, In inf steps -> inference_valid assignment inf) as Hprev.
    { intros inf Hin. apply Hinfs. now right. }
    assert (inference_valid assignment step) as Hstep.
    { apply Hinfs. now left. }
    clear Hinfs.
    specialize (IH Hprev); clear Hprev.
    intros H.
    destruct step_inference as [doms'| |] eqn:Hinf.
    + apply IH; clear IH. intros x Hcheck.
      unfold step_inference in Hinf.
      destruct forallb eqn:Hforall in Hinf;
      try discriminate Hinf.
      destruct i_consequent as [conseq|] in Hinf;
      try discriminate Hinf.
      destruct add_apply eqn:Happly in Hinf;
      try discriminate Hinf.
      inversion Hinf; subst d; clear Hinf.
      admit.
    + unfold step_inference in Hinf.
      destruct forallb eqn:Hforall in Hinf;
      try discriminate Hinf.
      unfold inference_valid in Hstep.
      destruct i_consequent as [conseq|] eqn:Hconseq.
      { 
        clear IH.
        destruct add_apply eqn:Happly in Hinf;
        try discriminate Hinf.
        apply forall_premises with (assignment := assignment) (atoms := premises) in Hforall;
        try assumption.
        apply Hstep in Hforall; clear Hstep.

        admit.  
      }
      { 
        intros _.
        clear IH Hinf.
        apply Hstep.
        apply forall_premises with (dom_map := doms) (atoms := premises).
        - apply Hforall.
        - apply Hatoms.
        - apply H. 
      }
    + easy.
  - intros _.
    destruct Hdomains as [x H].
    apply applied_dom_none_false with (f := assignment) (atoms := premises) (x := x).
    + exact Hatoms.
    + apply H.
Qed.


