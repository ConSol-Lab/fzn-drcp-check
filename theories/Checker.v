Require Import Checker.Deduction.
Require Import Checker.CumulativeCheck.
Require Import Checker.ConstraintProblem.
Require Import Checker.AlldifferentCheck.
Import Utility.Maps.
Import Utility.Sets.
Require Import Bool.
Require Import List.
Require Import Coq.Strings.String.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Checker.Spec.
Import Spec.ConstraintDefinitions.
Import Spec.Proofs.
Import Spec.ProofFacts.
Import Coq.Lists.List.ListNotations.
Open Scope Z_scope.

Module InferenceRule.
  Definition validator :=
    forall (csp_domains : smap.t IntSet) (fact : ProofFact) (hint : list Constraint), bool.

  Definition validator_ok (v : validator) :=
    forall (doms : smap.t IntSet) (fact : ProofFact) (hint : list Constraint) (sol : string -> Z),
      (forall (c : Constraint), In c hint -> satisfies_constraint c sol) ->
      satisfies_domains doms sol ->
      v doms fact hint = true ->
      fact_valid sol fact.

  Module Type Impl.
    Parameter r_label: string.
    Parameter r_validate: validator.
    Parameter r_validate_ok: validator_ok r_validate.
  End Impl.

  Record t :=
    { r_label: string;
      r_validate: validator;
      r_validate_ok: validator_ok r_validate }.

  Module Make (I: Impl).
    Definition rule: t :=
      {| r_label := I.r_label;
         r_validate := I.r_validate;
         r_validate_ok := I.r_validate_ok |}.
    Include I.
  End Make.
End InferenceRule.

Record IndexedInference := {
    iinf_index : N ;
    iinf_fact : ProofFacts.ProofFact ;
    iinf_hint : list N ;
    iinf_rule : string
  }.

Record ProofStage := {
    s_inferences : list IndexedInference ;
    s_chain : list N ;
    s_conclusion : ProofFacts.ProofFact ;
    s_conclusion_index : N
  }.

Inductive proof_stream :=
| Conclusion (conc : ProofFacts.ProofFact)
| Cons (stage : ProofStage) (tl : proof_stream)
| Thunk (next : unit -> proof_stream).

Inductive CheckerErrorType : Type :=
  | unknown_inference (id : N) (name: string)
  | invalid_inference (id : N)
  (* If failed_inferences is None, the premises of the deduction are contradictory *)
  | invalid_deduction (id : N) (failed_inferences : option (list FailedInference))
  | deduction_implies_not_false
  | invalid_conclusion.

Definition CheckerError := CheckResult CheckerErrorType.

Record HydratedInference := {
  hinf_index : N ;
  hinf_fact : ProofFact ;
  hinf_hint : list Constraint ;
  hinf_rule : string
}.

Record HydratedProofStage := {
  hs_inferences : list HydratedInference ;
  hs_chain : list ProofFact ;
  hs_conclusion : ProofFact ;
  hs_conclusion_index : N
}.

Definition min_value (domain : IntSet) :=
  match domain with
  | interval lb ub => Some lb
  | sparse_set vals => sint.min_elt vals
  end.

Lemma min_value_lt : forall (domain : IntSet) (min_val : Z) (el : Z),
  in_int_set domain el ->
  min_value domain = Some min_val ->
  el >= min_val.
Proof.
  intros domain.
  destruct domain ; simpl ; intros min_val el Hin Hmin.
  - inversion Hmin.
    rewrite <- H0.
    destruct Hin.
    apply Z.ge_le_iff.
    assumption.
  - apply sint.min_elt_spec2 with (y := el) in Hmin ; try assumption.
Qed.

Lemma min_value_exists : forall (domain : IntSet) (witness : Z),
  in_int_set domain witness -> (exists (m : Z), min_value domain = Some m).
Proof.
  intros domain witness Hin.
  unfold min_value.
  destruct domain.
  - exists lower_bound.
    reflexivity.
  - destruct (sint.min_elt vals) eqn:Emin.
    + exists e.
      reflexivity.
    + exfalso.
      simpl in Hin.
      apply sint.min_elt_spec3 in Emin.
      unfold sint.Empty, not in Emin.
      specialize (Emin witness Hin).
      contradiction.
Qed.

Definition max_value (domain : IntSet) :=
  match domain with
  | interval lb ub => Some ub
  | sparse_set vals => sint.max_elt vals
  end.

Lemma max_value_lt : forall (domain : IntSet) (max_val : Z) (el : Z),
  in_int_set domain el ->
  max_value domain = Some max_val ->
  el <= max_val.
Proof.
  intros domain.
  destruct domain ; simpl ; intros max_val el Hin Hmin.
  - inversion Hmin.
    rewrite <- H0.
    destruct Hin.
    assumption.
  - apply sint.max_elt_spec2 with (y := el) in Hmin ; try assumption.
    destruct (max_val ?= el) eqn:Ecmp; try contradiction.
    + apply OrdersEx.Z_as_OT.compare_eq in Ecmp.
      rewrite Ecmp.
      easy.
    + apply OrdersEx.Z_as_OT.compare_gt_iff in Ecmp.
      apply OrdersEx.Z_as_OT.lt_le_incl.
      assumption.
Qed.

Lemma max_value_exists : forall (domain : IntSet) (witness : Z),
  in_int_set domain witness -> (exists (m : Z), max_value domain = Some m).
Proof.
  intros domain witness Hin.
  unfold max_value.
  destruct domain.
  - exists upper_bound.
    reflexivity.
  - destruct (sint.max_elt vals) eqn:Emin.
    + exists e.
      reflexivity.
    + exfalso.
      simpl in Hin.
      apply sint.max_elt_spec3 in Emin.
      unfold sint.Empty, not in Emin.
      specialize (Emin witness Hin).
      contradiction.
Qed.

Definition validate_set (domain : IntSet) (atom : Atomic) :=
  match atom.(atm_cmp) with
  | greater_equal =>
      match min_value domain with
      | Some min_val => min_val >=? atom.(atm_val)
      | None => true
      end
  | less_equal =>
      match max_value domain with
      | Some max_val => max_val <=? atom.(atm_val)
      | None => true
      end
  | equal =>
      match min_value domain, max_value domain with
      | Some min_val, Some max_val => (min_val =? atom.(atm_val)) && (max_val =? atom.(atm_val))
      | _, _ => false
      end
  | not_equal =>
      match domain with
      | interval lb ub => (lb >? atom.(atm_val)) || (ub <? atom.(atm_val))
      | sparse_set vals => negb (sint.mem atom.(atm_val) vals)
      end
  end.

Lemma validate_set_if_holds : forall (domain : IntSet) (atom : Atomic) (el : Z),
  in_int_set domain el ->
  validate_set domain atom = true ->
  atomic_holds el atom.
Proof.
  intros domain atom el Hin Hvalid.
  unfold atomic_holds.
  destruct atom as [cmp val].
  specialize (max_value_exists domain el Hin) as Hmax.
  destruct Hmax as [ub Emax].
  specialize (min_value_exists domain el Hin) as Hmin.
  destruct Hmin as [lb Emin].
  destruct cmp ;
  simpl in Hvalid ; unfold validate_set in Hvalid ;
  inversion Hvalid ; simpl in Hvalid ;
  simpl.
  - apply OrdersEx.Z_as_OT.le_trans with (m := ub).
    + apply max_value_lt with (domain := domain) ; assumption.
    + rewrite Emax in Hvalid.
      apply Z.leb_le in Hvalid.
      assumption.
  - apply Zge_trans with (m := lb).
    + apply min_value_lt with (domain := domain) ; assumption.
    + rewrite Emin in Hvalid.
      apply Z.geb_ge in Hvalid.
      assumption.
  - rewrite Emax, Emin in Hvalid.
    apply andb_prop in Hvalid.
    destruct Hvalid as [El Eu].
    rewrite Z.eqb_eq in El.
    rewrite Z.eqb_eq in Eu.
    apply max_value_lt with (domain := domain) (el := el) in Emax ; try assumption.
    apply min_value_lt with (domain := domain) (el := el) in Emin ; try assumption.
    rewrite El in Emin.
    rewrite Eu in Emax.
    apply Z.ge_le in Emin.
    apply Z.le_antisymm ; assumption.
  - unfold in_int_set in Hin.
    destruct domain ; inversion Emax ; inversion Emin.
    + apply orb_prop in Hvalid.
      destruct Hvalid as [Hvalid|Hvalid].
      * apply Z.gtb_gt in Hvalid.
        destruct Hin as [Hlb _].
        symmetry.
        apply Z.gt_lt in Hvalid.
        apply OrdersEx.Z_as_OT.lt_neq, Z.lt_le_trans with (m := lower_bound) ; assumption.
      * apply Z.ltb_lt in Hvalid.
        destruct Hin as [_ Hub].
        apply OrdersEx.Z_as_OT.lt_neq, Z.le_lt_trans with (m := upper_bound) ; assumption.
    + apply negb_true_iff in Hvalid.
      unfold not.
      intros Heq.
      rewrite <- Heq in Hvalid.
      apply sint_prps.FM.not_mem_iff in Hvalid.
      contradiction.
Qed.


Definition validate_domain (csp_domains : smap.t IntSet) (fact : ProofFact) :=
  match i_consequent fact, i_premises fact with
  | Some (ident, atom), [] =>
      match smap.find ident csp_domains with
      | Some domain => validate_set domain atom
      | None => false
      end
  | _, _ => false
  end.

Lemma validate_if_holds : forall (csp_domains : smap.t IntSet) (fact : ProofFact) (sol : string -> Z),
  validate_domain csp_domains fact = true ->
  satisfies_domains csp_domains sol ->
  fact_valid sol fact.
Proof.
  intros csp_domains fact.
  generalize dependent csp_domains.
  destruct fact as [premises conseq].
  unfold fact_valid, validate_domain.
  simpl.
  intros csp_domains sol Hvalid Hsat Hvalid_atoms.
  destruct conseq as [(ident, atom)|] ; inversion Hvalid.
  destruct premises as [|F] ; inversion Hvalid.
  destruct (smap.find ident csp_domains) as [dom|] eqn:Emap; inversion Hvalid.
  unfold bound_atomic_holds.
  apply validate_set_if_holds with (domain := dom) ; try assumption.
  unfold satisfies_domains in Hsat.
  specialize (Hsat ident dom).
  apply Hsat, smap_prps.find_2, Emap.
Qed.

Create HintDb validate_ok discriminated.
Hint Resolve Is_true_eq_left : validate_ok.

Ltac validate_ok_t :=
    repeat lazymatch goal with
      | [ H: false = true |- _ ] => discriminate H
      | [ H: match ?x with _ => _ end = _ |- _ ] => destruct x
      | [ H: forall c : Constraint, In c [?cst] -> satisfies_constraint c _ |- _ ] => specialize (H cst (in_eq _ _))
      | [  |- InferenceRule.validator_ok ?v ] => unfold v; red; intros
      end;
    eauto with validate_ok.

(* TODO: see the comment above Deduction.equiv, currently some equivalent inferences might still return false. *)
(* TODO each of these modules should be moved to the corresponding file *)
Module fact_equiv_Impl <: InferenceRule.Impl.
  Definition r_label := "nogood".

  Definition r_validate : InferenceRule.validator :=
    fun _domains fact hint =>
      match hint with
      | [fact_c ref_fact] => Deduction.fact_implies_fact ref_fact fact
      | _ => false
      end.

  Hint Resolve Deduction.fact_implies_fact_entails : validate_ok.
  Lemma r_validate_ok : InferenceRule.validator_ok r_validate.
  Proof. validate_ok_t. Qed.
End fact_equiv_Impl.

Module fact_equiv := InferenceRule.Make fact_equiv_Impl.

Module dom_Impl <: InferenceRule.Impl.
  Definition r_label := "initial_domain".

  Definition r_validate : InferenceRule.validator :=
    fun domains fact _hint =>
      validate_domain domains fact.

  Hint Resolve validate_if_holds : validate_ok.
  Lemma r_validate_ok : InferenceRule.validator_ok r_validate.
  Proof. validate_ok_t. Qed.
End dom_Impl.

Module dom := InferenceRule.Make dom_Impl.

Module linear_Impl <: InferenceRule.Impl.
  Definition r_label := "linear_bounds".

  Definition r_validate : InferenceRule.validator :=
    fun _domains fact hint =>
      match hint with
      | [linear_leq c] => Linear.linear_checker fact c
      | [linear_eq c]  => Linear.linear_eq_checker fact c
      | _ => false
      end.

  Hint Resolve Linear.linear_checker_soundness Linear.linear_eq_checker_soundness : validate_ok.
  Lemma r_validate_ok : InferenceRule.validator_ok r_validate.
  Proof. validate_ok_t. Qed.
End linear_Impl.

Module linear := InferenceRule.Make linear_Impl.

Module cumulative_Impl <: InferenceRule.Impl.
  Definition r_label := "time_table".

  Definition r_validate : InferenceRule.validator :=
    fun _domains fact hint =>
      match hint with
      | [cumulative_c c] => cumulative_checker fact c
      | _ => false
      end.

  Hint Resolve checker_cumulative : validate_ok.
  Lemma r_validate_ok : InferenceRule.validator_ok r_validate.
  Proof. validate_ok_t. Qed.
End cumulative_Impl.

Module cumulative := InferenceRule.Make cumulative_Impl.

Module alldifferent_Impl <: InferenceRule.Impl.
  Definition r_label := "all_different".

  Definition r_validate : InferenceRule.validator :=
    fun _domains fact hint =>
      match hint with
      | [alldifferent_c c] => alldifferent_checker fact c
      | _ => false
      end.

  Hint Resolve checker_alldifferent : validate_ok.
  Lemma r_validate_ok : InferenceRule.validator_ok r_validate.
  Proof. validate_ok_t. Qed.
End alldifferent_Impl.

Module alldifferent := InferenceRule.Make alldifferent_Impl.

Module Type RULES.
  Parameter rules : string -> option InferenceRule.t.
End RULES.

Definition default_rules s :=
  Eval simpl in
    List.find (fun r => String.eqb s r.(InferenceRule.r_label))
      [linear.rule; cumulative.rule; alldifferent.rule; fact_equiv.rule; dom.rule].

Module DefaultRules <: RULES.
  Definition rules := default_rules.
End DefaultRules.

(*
Compute fact_equiv.validate
  smap.empty
  {|
    i_premises := [("x", Domain.mk_atm_le 5 )];
    i_consequent := Some (("y", Domain.mk_atm_le 3 ));
  |}
  [
  fact_c {|
    i_premises := [("x", Domain.mk_atm_le 5 ) ; ("y", Domain.mk_atm_ge 4)];
    i_consequent := None;
  |}
  ].
Compute fact_equiv.validate
  smap.empty
  {|
    i_premises := [("x", Domain.mk_atm_le 5 ) ; ("y", Domain.mk_atm_ge 4)];
    i_consequent := None;
  |}
  [
  fact_c {|
    i_premises := [("x", Domain.mk_atm_le 5 )];
    i_consequent := Some (("y", Domain.mk_atm_le 3 ));
  |}
  ].
 *)

Definition ProofStream := proof_stream.

Section CheckerImpl.
  Variable rules : string -> option InferenceRule.t.

  Inductive StageResult :=
  | valid_single_stage
  | invalid_single_stage (e : CheckerErrorType).

  Definition validate_nogood (id : N) (fact : ProofFact) (chain : list ProofFact) : StageResult :=
    match (i_consequent fact) with
    | None => match check_deduct fact.(i_premises) chain with
              | deduced => valid_single_stage
              | inconsistent_premises => invalid_single_stage (invalid_deduction id None)
              | failed failed_inferences => invalid_single_stage (invalid_deduction id (Some failed_inferences))
              end
    | Some _ => invalid_single_stage deduction_implies_not_false
    end.

  Definition validate_inference_within_stage
    (doms : smap.t IntSet) (step : HydratedInference) :=
    match rules step.(hinf_rule) with
    | Some rule =>
        if rule.(InferenceRule.r_validate) doms step.(hinf_fact) step.(hinf_hint) then
          valid_single_stage
        else
          invalid_single_stage (invalid_inference step.(hinf_index))
    | None =>
        invalid_single_stage (unknown_inference step.(hinf_index) step.(hinf_rule))
    end.

  Fixpoint validate_inferences (doms : smap.t IntSet) (inferences : list HydratedInference) : StageResult :=
    match inferences with
    | nil => valid_single_stage
    | inf :: tail =>
        match validate_inference_within_stage doms inf with
        | valid_single_stage => validate_inferences doms tail
        | error => error
        end
    end.

  Lemma validate_inferences_forall : forall
      (doms : smap.t IntSet) (inferences : list HydratedInference) ,
      validate_inferences doms inferences = valid_single_stage -> Forall (fun inf => validate_inference_within_stage doms inf = valid_single_stage) inferences.
  Proof.
    intros doms inferences Hvalid.
    rewrite Forall_forall.
    induction inferences ; simpl ; simpl in Hvalid ; try easy.
    intros x Hin'.
    destruct Hin' ; destruct (validate_inference_within_stage doms a) eqn:Estage ; try inversion Hvalid.
    - congruence.
    - rewrite IHinferences; congruence.
  Qed.

  Definition validate_proof_stage (doms : smap.t IntSet) (stage : HydratedProofStage) : StageResult :=
    match validate_inferences doms stage.(hs_inferences) with
    | valid_single_stage => validate_nogood stage.(hs_conclusion_index) stage.(hs_conclusion) stage.(hs_chain)
    | invalid_single_stage e => invalid_single_stage e
    end.

  Definition used_constraints (stage : HydratedProofStage) :=
    let hints := flat_map hinf_hint stage.(hs_inferences)
    in
    let inferences := map fact_c stage.(hs_chain)
    in
    hints ++ inferences.


  Lemma valid_proof_stage_implies_conclusion : forall
      (doms : smap.t IntSet) (stage : HydratedProofStage) (sol : string -> Z),
      validate_proof_stage doms stage = valid_single_stage ->
      (forall (c : Constraint),
          In c (used_constraints stage) -> satisfies_constraint c sol
      ) ->
      satisfies_domains doms sol ->
      fact_valid sol (stage.(hs_conclusion)).
  Proof.
    intros doms stage sol Hvalid Hcons_sat Hdoms.
    unfold validate_proof_stage in Hvalid.
    destruct (validate_inferences doms (hs_inferences stage)) eqn:Hinf_valid ; try inversion Hvalid.
    destruct (validate_nogood (hs_conclusion_index stage) (hs_conclusion stage) (hs_chain stage)) eqn:Hnogood_valid ; try inversion Hvalid.
    unfold validate_nogood in Hnogood_valid.
    destruct stage.(hs_conclusion).(i_consequent) eqn:Econs in Hnogood_valid ; try inversion Hnogood_valid.
    destruct stage.(hs_conclusion) as [conclusion_premises conseq]; simpl in *; subst conseq.
    apply check_deduct_correct with
      (assignment := sol)
      (premises := conclusion_premises)
      (steps := stage.(hs_chain)).
    - intros inf Hin_inf.
      specialize (Hcons_sat (fact_c inf)).
      simpl in Hcons_sat.
      apply Hcons_sat.
      unfold used_constraints.
      apply in_or_app.
      right.
      apply in_map, Hin_inf.
    - destruct (check_deduct conclusion_premises (hs_chain stage)) ; try inversion Hnogood_valid.
      reflexivity.
  Qed.

  (* Index inferences by id to speed up `hydrate_deduction_chain`. *)
  Definition build_inf_map_step (m : nmap.t ProofFact) (inf : IndexedInference)
    : nmap.t ProofFact :=
    nmap.add inf.(iinf_index) inf.(iinf_fact) m.

  Definition build_inf_map (infs : list IndexedInference) : nmap.t ProofFact :=
    fold_left build_inf_map_step infs nmap.empty.

  Fixpoint hydrate_deduction_chain_aux (csp : ConstraintProblem) (infmap : nmap.t ProofFact) (index_chain : list N) (acc : list ProofFact) : list ProofFact :=
    match index_chain with
    | nil => List.rev acc
    | index :: tail =>
        let chain_head :=
          match ConstraintProblem.lookup csp index with
          | Some (fact_c i) => [i]
          | _ => match nmap.find index infmap with Some f => [f] | None => [] end
          end
        in
        hydrate_deduction_chain_aux csp infmap tail (List.rev_append chain_head acc)
    end.

  Definition hydrate_deduction_chain (csp : ConstraintProblem) (infs : list IndexedInference) (index_chain : list N) : list ProofFact :=
    hydrate_deduction_chain_aux csp (build_inf_map infs) index_chain [].

  Lemma build_inf_map_fold_spec : forall infs m index fact,
      nmap.find index (fold_left build_inf_map_step infs m) = Some fact ->
      (exists inf, In inf infs /\ inf.(iinf_fact) = fact) \/
        nmap.find index m = Some fact.
  Proof.
    induction infs as [|inf rest IH]; intros m index fact Hfind.
    - eauto.
    - cbn [fold_left] in Hfind.
      specialize (IH (build_inf_map_step m inf) index fact Hfind).
      destruct IH as [[inf' [Hin' Heq]] | Hfind0].
      + eauto using in_cons.
      + unfold build_inf_map_step in Hfind0.
        destruct (N.eq_dec inf.(iinf_index) index) as [Heq | Hneq].
        * subst index. rewrite nmap.add_spec1 in Hfind0.
          injection Hfind0 as Hfeq. eauto using in_eq.
        * rewrite nmap.add_spec2 in Hfind0 by exact Hneq.
          eauto.
  Qed.

  Lemma in_build_inf_map : forall infs index fact,
      nmap.find index (build_inf_map infs) = Some fact ->
      exists inf, In inf infs /\ inf.(iinf_fact) = fact.
  Proof.
    intros infs index fact Hfind.
    unfold build_inf_map in Hfind.
    destruct (build_inf_map_fold_spec infs nmap.empty index fact Hfind)
      as [? | Hempty]; eauto.
    rewrite nmap.empty_spec in Hempty; discriminate.
  Qed.

  Lemma hydrated_chain_lookup_aux
    (csp : ConstraintProblem) (infmap : nmap.t ProofFact) (index_chain : list N)
    (fact : ProofFact) (acc : list ProofFact) :
    In fact (hydrate_deduction_chain_aux csp infmap index_chain acc) ->
    (exists x, ConstraintProblem.lookup csp x = Some (fact_c fact)) \/
      (exists index, nmap.find index infmap = Some fact) \/
      In fact acc.
  Proof.
    intros.
    generalize dependent fact.
    generalize dependent acc.
    induction index_chain as [|index tail].
    - simpl. intros acc fact Hin.
      apply in_rev in Hin; repeat right; assumption.
    - intros fact acc Hin. apply IHtail in Hin.
      destruct Hin as [Hlookup | [Hin_infs | Hin_acc]].
      + left. exact Hlookup.
      + right. left. exact Hin_infs.
      + rewrite rev_append_rev in Hin_acc.
        apply in_app_iff in Hin_acc.
        destruct Hin_acc as [Hin_lookup | Hin_rec].
        * destruct (lookup csp index) as [c|] eqn:Elookup ;
            try destruct c;

            try (
                right ;
                left ;
                apply in_rev in Hin_lookup ;
                destruct (nmap.find index infmap) as [f|] eqn:Efind ;
                simpl in Hin_lookup ;
                [ destruct Hin_lookup as [-> | []] | contradiction ] ;
                eauto
              ).

          left.
          exists index.
          inversion Hin_lookup ; try easy.
          rewrite <- H, Elookup.
          reflexivity.
        * right. right. exact Hin_rec.
  Qed.


  Lemma hydrated_chain_lookup : forall
      (csp : ConstraintProblem) (infs : list IndexedInference) (index_chain : list N)
      (fact : ProofFact),
      In fact (hydrate_deduction_chain csp infs index_chain) ->
      (exists x, ConstraintProblem.lookup csp x = Some (fact_c fact)) \/
        (exists inf, In inf infs /\ inf.(iinf_fact) = fact).
  Proof.
    intros csp infs index_chain fact Hin.
    unfold hydrate_deduction_chain in Hin.
    apply hydrated_chain_lookup_aux in Hin.
    destruct Hin as [Hlookup | [[index Hfind] | Hin_acc]].
    - left. exact Hlookup.
    - eauto using in_build_inf_map.
    - destruct Hin_acc.
  Qed.

  Definition hydrate_inference (csp : ConstraintProblem) (inf : IndexedInference) : HydratedInference :=
    let hint := flat_map (
                    fun index =>
                      match ConstraintProblem.lookup csp index with
                      | Some c => [c]
                      | None => []
                      end
                  )
                  (inf.(iinf_hint))
    in
    {|
      hinf_index := inf.(iinf_index) ;
      hinf_fact := inf.(iinf_fact) ;
      hinf_hint := hint ;
      hinf_rule := inf.(iinf_rule)
    |}.


  Definition hydrate (csp : ConstraintProblem) (stage : ProofStage) : HydratedProofStage :=
    let inferences := map (hydrate_inference csp) stage.(s_inferences)
    in
    let chain := hydrate_deduction_chain csp stage.(s_inferences) stage.(s_chain)
    in
    {|
      hs_inferences := inferences ;
      hs_conclusion := stage.(s_conclusion) ;
      hs_chain := chain ;
      hs_conclusion_index := stage.(s_conclusion_index) ;
    |}
  .

  Inductive CheckStagesResult :=
  | valid_stage (csp : ConstraintProblem)
  | invalid_stage (error : CheckerErrorType).

  Definition compare_with_fact (rhs : ProofFact) (lhs : Constraint) :=
    match lhs with
    | fact_c lhs => equiv lhs rhs
    | _ => false
    end.

End CheckerImpl.

Module SequentialCheckerImpl.
  Definition Proof := (list ProofStage * ProofFact)%type.

  Section Impl.
  Variable rules : string -> option InferenceRule.t.

  Definition step (csp : ConstraintProblem) (stage : ProofStage) : CheckStagesResult :=
    match validate_proof_stage rules (csp.(domains)) (hydrate csp stage) with
    | valid_single_stage =>
        valid_stage (ConstraintProblem.add stage.(s_conclusion_index) stage.(s_conclusion) csp)
    | invalid_single_stage e => invalid_stage e
    end.

  Definition finalize (r : CheckStagesResult) (conclusion : ProofFact) : CheckerError :=
    match r with
    | valid_stage csp' =>
        if nmap.exists_ (fun k => compare_with_fact conclusion) csp'.(constraints)
        then valid conclusion
        else invalid invalid_conclusion
    | invalid_stage e => invalid e
    end.

  Arguments step /.
  Arguments finalize /.

  Fixpoint validate_stages (csp : ConstraintProblem) (p : list ProofStage) : CheckStagesResult :=
    match p with
    | nil => valid_stage csp
    | stage :: p' =>
        match step csp stage with
        | valid_stage csp' => validate_stages csp' p'
        | invalid_stage e => invalid_stage e
        end
    end.

  Theorem step_soundness : forall
      (csp : ConstraintProblem) (p : list ProofStage) (stage : ProofStage),
      (exists csp', validate_stages csp (stage :: p) = valid_stage csp') ->
      fact_holds csp (stage.(s_conclusion)).
  Proof.
    intros csp p stage Hvalid.
    simpl in Hvalid.
    destruct Hvalid as [csp' Hvalid].
    (* Show that the proof checker on the hydrated stage returns true *)
    remember (hydrate csp stage) as h_stage.
    destruct (validate_proof_stage rules csp.(domains) h_stage) eqn:Evalid ; try inversion Hvalid.
    clear Hvalid.
    (* Destruct all parts of the stage definition *)
    destruct stage as [inferences chain conclusion conclusion_index].
    simpl.
    rewrite Heqh_stage in Evalid.
    unfold hydrate in Evalid.
    simpl in Evalid.
    (* Appeal to the proof stage checker soundness *)
    unfold fact_holds.
    intros sol Hsat.
    assert (Hrewrite: conclusion = (hs_conclusion h_stage)). {
      rewrite Heqh_stage.
      simpl.
      reflexivity.
    }
    rewrite Hrewrite.
    clear Hrewrite.
    apply valid_proof_stage_implies_conclusion with (rules := rules) (doms := csp.(domains)).
    - (* Rewrite into the proof checker validity *)
      unfold hydrate in Heqh_stage.
      simpl in Heqh_stage.
      rewrite <- Heqh_stage in Evalid.
      rewrite Evalid.
      reflexivity.
    - (* Show that any constraint used by the _hydrated_ stage is valid *)
      intros c Hin_cons.
      unfold used_constraints in Hin_cons.
      apply in_app_iff in Hin_cons.
      destruct Hin_cons as [Hin_hint | Hin_chain].
      + (* The constraint in question has been found in the hint.
           Look up the constraint in the CSP and appeal to the CSP definition. *)
        apply in_flat_map in Hin_hint.
        destruct Hin_hint as [h_inf [Hin_inf Hin_hint]].
        rewrite Heqh_stage in Hin_inf.
        simpl in Hin_inf.
        apply in_map_iff in Hin_inf.
        destruct Hin_inf as [i_inf [Eh_inf Hin_inf]].
        rewrite <- Eh_inf in Hin_hint.
        simpl in Hin_hint.
        apply in_flat_map in Hin_hint.
        destruct Hin_hint as [index [Hin_hint Hin_c]].
        destruct (lookup csp index) eqn:Elookup; try contradiction.
        simpl in Hin_c.
        destruct Hin_c as [Hin_c | F] ; try contradiction.
        rewrite Hin_c in Elookup.
        apply sat_csp_implies_sat_lookup with
          (csp := csp) (index := index) ; easy.
      + (* The constraint in question has been found in the inference chain.
           Use the lemma `hydrated_chain_lookup` *)
        apply in_map_iff in Hin_chain.
        destruct Hin_chain as [fact [Efact_c Hin_chain]].
        rewrite Heqh_stage in Hin_chain.
        simpl in Hin_chain.
        apply hydrated_chain_lookup in Hin_chain.
        destruct Hin_chain as [Hlookup|Hin_inferences].
        * (* The fact was introduced from the CSP; appeal to the CSP definition. *)
          destruct Hlookup as [index Elookup].
          rewrite <- Efact_c.
          apply sat_csp_implies_sat_lookup with
            (csp := csp) (index := index) ; easy.
        * (* The fact was introduced from the inference chain. Appeal to the
             correctness of the inference checker. *)
          destruct Hin_inferences as [inf [Hin_inf Einf_fact]].
          unfold validate_proof_stage in Evalid.
          simpl in Evalid.
          destruct (validate_inferences rules (domains csp) (map (hydrate_inference csp) inferences)) eqn:Hvalid_inferences ; try inversion Evalid.
          apply validate_inferences_forall in Hvalid_inferences.
          unfold validate_inference_within_stage in Hvalid_inferences.
          rewrite <- Efact_c.
          simpl.
          set (hydrate_inference csp inf) as hinf.
          rewrite Forall_forall in Hvalid_inferences.
          specialize (Hvalid_inferences hinf ltac:(eauto using in_map)).
          destruct rules as [rule | ]; [ | discriminate Hvalid_inferences].
          apply rule.(InferenceRule.r_validate_ok) with
            (hint := (hinf_hint hinf))
            (doms := csp.(domains)).
            -- (* Check that the hydrated hints are in the CSP *)
               intros c' Hin_hint.
               simpl in Hin_hint.
               apply in_flat_map in Hin_hint.
               destruct Hin_hint as [index' [Hin_inf' Hin_c']].
               destruct (lookup csp index') eqn:Elookup' ; try contradiction.
               simpl in Hin_c'.
               destruct Hin_c' as [Hin_c' | F] ; try contradiction.
               rewrite Hin_c' in Elookup'.
               apply sat_csp_implies_sat_lookup with (csp := csp) (index := index') ;
               try easy.
            -- (* Check that the solution satisfies the CSP domains *)
               unfold satisfies_problem in Hsat.
               destruct Hsat as [_ Hdoms].
               assumption.
            -- (* Check that the inference checker returns true *)
               assert (Hrewrite: fact = (hinf_fact hinf)). {
                 simpl.
                 rewrite Einf_fact.
                 reflexivity.
               }
               rewrite Hrewrite.
               clear Hrewrite.
               destruct InferenceRule.r_validate; congruence.
    - unfold satisfies_problem in Hsat.
      destruct Hsat as [_ Hdoms].
      assumption.
  Qed.

  Definition validate (csp : ConstraintProblem) (proof: Proof) :=
    finalize (validate_stages csp (fst proof)) (snd proof).


  Theorem soundness : checker_sound validate.
  Proof.
    unfold checker_sound.
    intros csp proof conclusion Hvalid.
    destruct proof as [stages conc_ret].
    assert (conclusion = conc_ret) as Hconc by (
      unfold validate in Hvalid; simpl in Hvalid; destruct (validate_stages csp stages) eqn:Evalid; inversion Hvalid;
      destruct (nmap.exists_); inversion Hvalid; reflexivity
    ).

    generalize dependent csp.
    simpl.
    (* Induction by the sequence of stages *)
    induction stages as [|stage].
    (* Base case is a simple lookup in the original CSP *)
    - unfold validate.
      simpl.
      intros csp Hexists' sol Hsat.
      destruct nmap.exists_ eqn:Hexists ; try inversion Hexists'.
      apply nmap_prps.exists_iff in Hexists.
      + destruct Hexists as [index [fact_cons [Hmaps Hequiv]]].
        unfold compare_with_fact in Hequiv.
        destruct fact_cons ; inversion Hequiv.
        apply equiv_implies_equisat with (sol := sol) in Hequiv.
        rewrite Hconc.
        apply Hequiv.
        unfold satisfies_problem in Hsat.
        destruct Hsat as [Hsat_constr Hsat_doms].
        specialize (Hsat_constr index (fact_c constraint) Hmaps).
        easy.
      + unfold Morphisms.Proper, Morphisms.respectful.
        intros ix iy Ei cx cy Ec.
        rewrite Ec.
        reflexivity.
    (* Use the induction hypothesis for the remainder of the proof and
       the mutated CSP problem instance *)
    - intros csp Hvalid.
      assert (Hholds: fact_holds csp (stage.(s_conclusion))). {
        apply step_soundness with (p := stages).
        unfold validate in Hvalid.
        Opaque validate_stages.
        simpl in Hvalid.
        Transparent validate_stages.
        destruct (
            validate_stages csp (stage :: stages)
          ) as [csp'|] eqn:Evalid ; inversion Hvalid.
        exists csp'.
        reflexivity.
      }
      unfold fact_holds.
      apply entailed_addition with
        (fact := stage.(s_conclusion))
        (index := stage.(s_conclusion_index)) ;
        try exact Hholds.
      remember (add (stage.(s_conclusion_index)) (stage.(s_conclusion)) csp) as csp'.
      apply IHstages with (csp := csp').
      (* Proof conclusion stays the same, as it is not empty. *)
      unfold validate in Hvalid.
      simpl in Hvalid.
      unfold validate.
      simpl.
      destruct (validate_proof_stage rules csp.(domains) (hydrate csp stage)) eqn:Estage ; inversion Hvalid.
      rewrite <- Heqcsp'.
      destruct (validate_stages csp' stages) ; try reflexivity.
  Qed.
  End Impl.
End SequentialCheckerImpl.

Arguments SequentialCheckerImpl.step /.
Arguments SequentialCheckerImpl.finalize /.

Module StreamingCheckerImpl.
  Definition Proof := ProofStream.

  Section Impl.
  Variable rules : string -> option InferenceRule.t.

  Fixpoint validate_stages (csp : ConstraintProblem) (p : ProofStream)
    : (option ProofFact * CheckStagesResult) :=
    match p with
    | Conclusion conc => (Some conc, valid_stage csp)
    | Thunk next => validate_stages csp (next tt)
    | Cons stage p' =>
        match SequentialCheckerImpl.step rules csp stage with
        | valid_stage csp' => validate_stages csp' p'
        | invalid_stage e => (None, invalid_stage e)
        end
    end.

  Definition validate (csp : ConstraintProblem) (proof_stages : ProofStream) : CheckerError :=
    match validate_stages csp proof_stages with
    | (Some conclusion, r) => SequentialCheckerImpl.finalize r conclusion
    | (None, invalid_stage e) => invalid e
    | (None, valid_stage _) => invalid invalid_conclusion
    end.

  (* A proof stream denotes exactly the stages obtained by forcing its thunks.  *)
  Fixpoint force_stages (t : ProofStream) : list ProofStage :=
    match t with
    | Conclusion _ => nil
    | Cons hd tl => hd :: force_stages tl
    | Thunk next => force_stages (next tt)
    end.

  (* The stream checker traverses the same data as the sequential one, so its
     proof is simply an induction that relates `SequentialCheckerImpl.validate_stages`
     to `StreamingChecker.validate_stages`. *)
  Lemma force_validate_stages : forall t csp,
      SequentialCheckerImpl.validate_stages rules csp (force_stages t) =
        snd (validate_stages csp t).
  Proof.
    induction t; simpl; intros.
    2: destruct validate_proof_stage.
    all: congruence || eauto.
  Qed.

  Theorem soundness : checker_sound validate.
  Proof.
    unfold checker_sound. intros csp t fact Hvalid.
    apply (SequentialCheckerImpl.soundness rules _ (force_stages t, fact)).
    unfold SequentialCheckerImpl.validate, validate in *; simpl in *.
    rewrite force_validate_stages.
    destruct validate_stages as [[conclusion |] [csp' | e]]; simpl; try discriminate; [].
    destruct nmap.exists_ eqn:Heq; try discriminate; [].
    inversion Hvalid; subst; rewrite Heq; reflexivity.
  Qed.
  End Impl.
End StreamingCheckerImpl.

Module SequentialChecker (R: RULES) <: CHECKER.
  Definition Proof := SequentialCheckerImpl.Proof.
  Definition Error := CheckerErrorType.
  Definition validate := SequentialCheckerImpl.validate R.rules.
  Definition validate_sound := SequentialCheckerImpl.soundness R.rules.
End SequentialChecker.

Module StreamingChecker (R: RULES) <: CHECKER.
  Definition Proof := StreamingCheckerImpl.Proof.
  Definition Error := CheckerErrorType.
  Definition validate := StreamingCheckerImpl.validate R.rules.
  Definition validate_sound := StreamingCheckerImpl.soundness R.rules.
End StreamingChecker.
