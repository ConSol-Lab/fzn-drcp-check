Require Import ZArith.
Require Import Bool.
Require Import String.
Require Import List.
Require Checker.Spec.
Import Spec.ProofFacts.
Import Spec.ConstraintDefinitions.

Require Utility.
Import Utility.Sets.
Import Utility.Maps.
Import Utility.ZRange.
Require Import Checker.Domain.
Require Import Checker.DomainVar.
Require Import Checker.Deduction.


(* Open Scope Z_scope. *)

Definition materialize_dom (dom : Domain) : sint.t :=
  match lb_ub_from_dom dom with
  | Some (lb, ub) =>
    let values := range lb ub in
    let values_set := sint.build values in
      sint.fold sint.remove dom.(d_holes) values_set
  | None => sint.empty
  end
.

Open Scope Domain_scope.

Definition is_bounded (dom : Domain) :=
  match lb_ub_from_dom dom with
  | Some _ => true
  | None => false
  end.

Lemma materialize_dom_iff_in_dom :
  forall y dom,
    is_bounded dom = true
      ->
    is_in_dom y dom <-> sint.In y (materialize_dom dom).
Proof.
Admitted.

(** A more efficient implementation that avoids a lot of the iterations is definitely possible.  *)
Definition union_doms_for_var (doms : Domains) (acc : sint.t) (var : Var) :=
  match var with
  | var_name x =>
    match smap.find x doms with
    | None => acc
    | Some dom => sint.union acc (materialize_dom dom)
    end
  | _ => acc
  end.
(* Question: if we have constants... then they have no variable and our proof cannot refer to them, correct? *)

(* Definition fact_keys := smap.bindings. *)


Definition FullDomain := sint.t.
Definition state := string -> FullDomain.

Open Scope nat_scope.

Definition alldifferent_checker (fact : ProofFact) (constraint : AlldifferentConstraint) : bool :=
  match infer_domains fact with
  | None => false
  | Some (domains, _) =>
    let union := (fold_left (union_doms_for_var domains) constraint.(diff_variables) sint.empty) in
    sint.cardinal union <? smap.cardinal domains
  end.

Definition valuation_in_state (st : state) (vs : list string) (v : string -> Z) : Prop :=
  forall x, In x vs -> sint.In (v x) (st x).

Definition Alldifferent_l (vs : list string) (sol : string -> Z) : Prop :=
    forall x y, 
      In x vs -> 
      In y vs -> 
        sol x <> sol y
  .

Definition AllDifferent_sat (st : state) (vs : list string) :=
  exists v, valuation_in_state st vs v /\ Alldifferent_l vs v.

Definition is_domain_union (st : state) (variables : list string) (domain_union : list Z) :=
  NoDup domain_union
    /\
  forall n, In n domain_union <-> (exists x, In x variables /\ sint.In n (st x)).

Definition exists_conflict_variables (st : state) (constraint_variables : list string) := 
  exists conflict_variables conflict_domain_union,
    NoDup conflict_variables
      /\
    incl conflict_variables constraint_variables
      /\ 
    is_domain_union st conflict_variables conflict_domain_union
      /\ 
    length conflict_domain_union < length conflict_variables.

Lemma Injective_map_NoDup_in A B (f:A->B) (l:list A) :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
 pose proof @in_cons. pose proof @in_eq.
 intros Ij N; revert Ij; induction N; cbn [map]; constructor; auto.
 rewrite in_map_iff. intros (y & E & Y). apply Ij in E; auto; congruence.
Qed.


Lemma conflict_if_ex_confl_vars' (st : state) (vars : list string) (domain_union : list Z) :
  NoDup domain_union
    ->
  NoDup vars
    ->
  (forall n, In n domain_union <-> (exists x, In x vars /\ sint.In n (st x)))
    ->
  length domain_union < length vars
    -> 
  ~ AllDifferent_sat st vars.
Proof.
Admitted.


(* TODO get rid of subset reasoning, not necessary. *)
Lemma conflict_if_ex_confl_vars (st : state) (constraint_variables : list string) :
  exists_conflict_variables st constraint_variables -> ~ AllDifferent_sat st constraint_variables.
Proof.
  intros (conflict_variables & conflict_domain_union & Hnodup & Hsub & Hunion & Hlengths).
  intros [A [Hastate Halldiff]].
  enough (length conflict_domain_union >= length conflict_variables).
  { apply Nat.lt_nge in Hlengths.
    contradiction. }
  clear Hlengths; rewrite <- length_map with (f := A).
  apply NoDup_incl_length.
  - clear -Hnodup Halldiff Hsub. 
    apply Injective_map_NoDup_in.
    * intros x y Hinx Hiny Hvxvy.
      destruct (String.string_dec x y) as [Hxy | Hxy].
      { assumption. }
      enough (A x <> A y) by contradiction.
      apply Halldiff; try apply Hsub; assumption.
    * apply Hnodup.
  - clear -Hunion Hastate Hsub. 
    unfold incl. intros n Hin. 
    apply Hunion; clear Hunion.
    rewrite in_map_iff in Hin.
    destruct Hin as (x & Hvx & Hxin).
    exists x. split.
    + exact Hxin.
    + rewrite <- Hvx. apply Hastate.
      apply Hsub. exact Hxin.
Qed.

Definition bounded_vars (doms : Domains) :=
  filter (fun x => is_bounded (doms d-> x)) (map fst (smap.bindings doms)).

Lemma bounded_vars_spec :
  forall x doms,
    In x (bounded_vars doms) ->
    is_bounded (doms d-> x) = true.
Proof.
  intros x doms.
  unfold bounded_vars.
  rewrite filter_In; easy.
  (* rewrite in_map_iff.
  intros [Hex Hbounded].
  destruct Hex as ([x' xdom] & Hxx' & _).
  simpl in Hxx'; subst x'.
  revert Hbounded; unfold is_bounded.
  destruct lb_ub_from_dom eqn:Hlb_ub.
  - intros. destruct p; reflexivity.
  - easy. *)
Qed.

Definition same_ident (x : string) (var : Var) : bool :=
  match var with
  | var_name y => (x =? y)%string
  | _ => false
  end.

Definition constr_vars (vs : list string) (constr : AlldifferentConstraint) :=
  filter (fun x => existsb (same_ident x) constr.(diff_variables)) vs.

Lemma checker_alldifferent :
  forall fact sol constr,
  Alldifferent constr sol
  -> alldifferent_checker fact constr = true
  -> fact_valid sol fact.
Proof.
  intros fact sol constr.
  unfold alldifferent_checker.
  destruct infer_domains as [(doms & cnsq)|] eqn:Hinfer; try easy.
  apply infer_domains_correct with (sol := sol) in Hinfer.
  rewrite <- Hinfer; clear Hinfer.
  intros Halldiff Hconfl Hin_doms.
  remember (fun x => materialize_dom (doms d-> x)) as st.
  unfold sol_in_doms in Hin_doms.
  assert (valuation_in_state st (bounded_vars doms)  sol) as Hbounded_in_state.
  {
    clear -Heqst Hin_doms.
    unfold valuation_in_state.
    intros x.
    subst st.
    unfold bounded_vars.
    rewrite filter_In.
    intros [_ Hbounded].
    apply materialize_dom_iff_in_dom with (y := sol x) in Hbounded.
    apply Hbounded.
    apply Hin_doms.
  }
  assert (valuation_in_state st (constr_vars (bounded_vars doms) constr) sol) as Hvars_state.
  {
    intros x. unfold constr_vars. rewrite filter_In.
    intros [Hin _]. apply Hbounded_in_state. exact Hin.
  }
  clear Hbounded_in_state.
  enough (~ Alldifferent_l (constr_vars (bounded_vars doms) constr) sol) as Halldiff_l.
  {
    clear -Halldiff Halldiff_l.
    apply Halldiff_l; clear Halldiff_l.
    intros x y.
    unfold constr_vars. setoid_rewrite filter_In.
    intros [_ Hexx] [_ Hexy].
    revert Hexx Hexy.
    setoid_rewrite existsb_exists.
    intros (x' & Hx') (y' & Hy').
    revert Hx' Hy'.
    unfold same_ident. destruct y' as [y'|]; destruct x' as [x'|]; try easy.
    setoid_rewrite String.eqb_eq.
    intros [Hinx Hxx'] [Hiny Hyy']; subst x' y'.
    specialize (Halldiff (var_name x) (var_name y)).
    simpl in Halldiff. apply Halldiff; assumption.
  }
  remember (constr_vars (bounded_vars doms) constr) as vars.
  enough (~ AllDifferent_sat st vars) as Halldiff_sat.
  {
    intros Halldiff_l. apply Halldiff_sat; clear Halldiff_sat.
    unfold AllDifferent_sat.
    exists sol.
    split.
    - exact Hvars_state.
    - exact Halldiff_l.
  }



Admitted.
