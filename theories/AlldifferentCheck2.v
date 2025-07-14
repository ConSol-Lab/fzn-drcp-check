Require Import ZArith.
Require Import Bool.
Require Import String.
Require Import List.
Require Import Lia.
Require Checker.Spec.
Import Spec.ProofFacts.
Import Spec.ConstraintDefinitions.

Require Utility.
Import Utility.Sets.
Import Utility.Maps.
Import Utility.ZRange.
Import Utility.ListEx.
Import Utility.ListInd.
Import Utility.SubList.
Require Import Checker.Zext.
Require Import Checker.Domain.
Require Import Checker.DomainVar.
Require Import Checker.Deduction.

Open Scope nat_scope.

(** * Core proof. *)
(** The below section is fully independent from the checker's implementation. It highlights the main idea on which the checker is based: there is no solution to an alldifferent constraint (given a current state of variable domains) if we can find variables such that the union of their domains is smaller than the number of variables. These are 'tight sets' according to the language of Van Hoeve (2001). *)

Definition MaterializedDomain := sint.t.
Definition state := string -> MaterializedDomain.

Definition valuation_in_state (st : state) (vs : list string) (v : string -> Z) : Prop :=
  forall x, In x vs -> sint.In (v x) (st x).

Definition Alldifferent_l (vs : list string) (sol : string -> Z) : Prop :=
    forall x y, 
      In x vs -> 
      In y vs -> 
        sol x <> sol y.

Definition AllDifferent_sat (st : state) (vs : list string) :=
  exists v, valuation_in_state st vs v /\ Alldifferent_l vs v.

(** Copied from Coq stdlib 9.0 *)
Lemma Injective_map_NoDup_in A B (f:A->B) (l:list A) :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
 pose proof @in_cons. pose proof @in_eq.
 intros Ij N; revert Ij; induction N; cbn [map]; constructor; auto.
 rewrite in_map_iff. intros (y & E & Y). apply Ij in E; auto; congruence.
Qed.

(** This is the main lemma that underpins the approach. *)
Lemma alldiff_conflict_if_union_lt_vars (st : state) (vars : list string) (domain_union : list Z) :
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
  intros Hunion_nd Hvars_nd Hunion Hlengths.
  intros [A [Hastate Halldiff]].
  enough (length domain_union >= length vars) by lia; clear Hlengths.
  rewrite <- length_map with (f := A).
  apply NoDup_incl_length.
  - clear -Hvars_nd Halldiff.
    apply Injective_map_NoDup_in.
    + intros x y Hxin Hyin Hxy_A.
      enough (A x <> A y) by contradiction; clear Hxy_A.
      apply Halldiff.
      * exact Hxin.
      * exact Hyin.
    + exact Hvars_nd.
  - intros n. rewrite in_map_iff.
    intros (x & Hx_A & Hxin).
    rewrite Hunion.
    exists x; split.
    + exact Hxin.
    + rewrite <- Hx_A.
      apply Hastate.
      exact Hxin.
Qed.

(** * Domain materialization  *)
(** We choose a simple approach for determining the union of a series of domains: we first materialize them by building a set of all elements and then merge these. Another, potentially faster, approach would be to determine the intersection of all holes and and use the min and max of the lower and upper bounds to construct a new Domain. If we seek to verify only range consistent propagators, we could skip the more expensive hole intersection step. *)

Open Scope Domain_scope.

(** This is not the most efficient way to materialize it, as first we build a range, then turn it into a set and then remove the holes one by one, but for alldifferent we mostly care that it works. *)
Definition materialize_dom (dom : Domain) : option sint.t :=
  match lb_ub_from_dom dom with
  | Some (lb, ub) =>
    let values := range lb ub in
    let values_set := sint.build values in
      Some (sint.fold sint.remove dom.(d_holes)values_set)
  | None => None
  end.

Definition is_bounded (dom : Domain) :=
  match lb_ub_from_dom dom with
  | Some _ => true
  | None => false
  end.

(** This lemma captures the correctness of the procedure of the materialize_dom procedure. *)
Lemma materialize_dom_iff_in_dom :
  forall y dom,
    is_bounded dom = true
      ->
    is_in_dom y dom <-> sint.In y (option_default sint.empty (materialize_dom dom)).
Proof.
  intros y dom. unfold is_bounded, is_in_dom, materialize_dom, lb_ub_from_dom.
  destruct d_lb as [lb| |]; destruct d_ub as [ub| |]; try easy.
  intros _. simpl. zext_as_z.
  rewrite <- sint.elements_in.
  rewrite sint.fold_spec. rewrite <- fold_left_rev_right.
  remember (sint.elements (d_holes dom)) as holes.
  clear Heqholes dom.
  generalize dependent y.
  set (P := fun (holes : list Z) (acc : sint.t) =>
      forall y, (lb <= y /\ y <= ub /\ ~ In y holes <-> sint.In y acc)%Z).
  enough (P (rev holes) (fold_right sint.remove (sint.build (range lb ub)) (rev holes))).
  { 
    unfold P in H; clear P.
    intros y. rewrite in_rev.
    apply H.  
  }
  apply fold_ind; clear holes; unfold P; clear P.
  - intros y.
    rewrite sint.build_spec.
    rewrite <- in_range.
    split; intros H; repeat split; try lia.
    intros Hnil; destruct Hnil.
  - intros h values holes IH.
    intros y. rewrite sint.remove_spec.
    rewrite <- IH. 
    assert (~ In y (h :: holes) <-> y <> h /\ ~ In y holes).
    { clear. simpl. repeat split.
      - intros Hyh. apply H.
        left. symmetry. exact Hyh.
      - intros Hin.
        apply H. right. exact Hin.
      - intros [Hnyh Hnin] [Hhy | Hin].
        + subst y. contradiction.
        + contradiction. }
    rewrite H.
    repeat split; easy.
Qed. 

(** Given a domain map, we want to get the materialized domain corresponding to a var. We ignore constants, so if we have constants in our alldifferent constraint it might not completely work. It should be possible to add support by simply returning a singleton set containing the constant in that case, but we do not do that here. *)
Definition materialized_dom_for_var (doms: Domains) (var : Var) : option sint.t :=
  match var with
  | var_name x =>
    match smap.find x doms with
    | None => None
    | Some dom => materialize_dom dom
    end
  | _ => None
  end.

Definition materialize_vars_doms (vars : list Var) (doms : Domains) :=
  flat_map_option (materialized_dom_for_var doms) vars.

(** The below code could be moved to Utility.Sets as it is not specific to alldifferent. *)
Definition union_sets (sets : list sint.t) :=
  fold_left sint.union sets sint.empty.

Lemma union_sets_spec (sets : list sint.t) :
  forall n,
    sint.In n (union_sets sets) <-> exists s, In s sets /\ sint.In n s.
Proof.
  intros n.
  unfold union_sets.
  rewrite <- fold_left_rev_right.
  set (P := fun (sets : list sint.t) (acc : sint.t) =>
      forall n, sint.In n acc <-> exists s, In s sets /\ sint.In n s).
  enough (P (rev sets) (fold_right (fun y x => sint.union x y) sint.empty (rev sets))).
  {
    unfold P in H; clear P. setoid_rewrite in_rev at 1. apply H.
  }
  apply fold_ind; clear.
  { unfold P; clear P. intros n. split; intros H.
    - destruct (sint.empty_spec H).
    - destruct H as [n' [Hnil _]]. destruct Hnil. }
  unfold P; clear P.
  intros s s' sets IH n.
  split; intros H.
  - rewrite sint.union_spec in H.
    destruct H as [Hin' | Hin].
    + rewrite IH in Hin'. destruct Hin' as (s_set & Hssets & Hin_s_set).
      exists s_set; split.
      * right. exact Hssets.
      * exact Hin_s_set.
    + exists s. split.
      * left. reflexivity.
      * exact Hin.
  - rewrite sint.union_spec. destruct H as (s_set & Hssets & Hin_s_set).
    destruct Hssets as [Hs_set_s | Hssets].
    + subst s_set. right. exact Hin_s_set.
    + left. apply IH. exists s_set.
      split.
      * exact Hssets.
      * exact Hin_s_set.
Qed.

(** * Checker  *)
(** This is the actual checker. If assumptions are made using constant values in the constraint, we ignore them and they will not be checked. *)
Definition alldifferent_checker (fact : ProofFact) (constraint : AlldifferentConstraint) : bool :=
  match infer_domains fact with
  | None => false
  | Some (domains, _) =>
    let materialized_doms := materialize_vars_doms constraint.(diff_variables) domains in
    sint.cardinal (union_sets materialized_doms) <? length materialized_doms
  end.

Definition var_name_default (v : Var) :=
  match v with
  | var_name x => x
  | _ => ""%string
  end.

Lemma var_name_default_and_materialized doms :
  forall v x dom,
    var_name_default v = x
      ->
    materialized_dom_for_var doms v = Some dom
      ->
    v = var_name x.
Proof.
  intros v x dom.
  unfold var_name_default, materialized_dom_for_var.
  destruct v as [x'|]; try easy.
  intros Hxx'; subst x'.
  intros _. reflexivity.
Qed.

(** The proof is a bit large because we aim to explicitly decouple the implementation details and the core idea of checking alldifferent. *)
Lemma checker_alldifferent :
  forall fact sol constr,
  Alldifferent constr sol
  -> alldifferent_checker fact constr = true
  -> fact_valid sol fact.
Proof.
  intros fact sol constr.
  unfold alldifferent_checker.
  (* We aim to use `alldiff_conflict_if_union_lt_vars`, so we need to first construct a state and show that our solution adheres to it. For that we must first get the correctness information about oru domains. *)
  destruct infer_domains as [(doms & cnsq)|] eqn:Hinfer; try easy.
  apply infer_domains_correct with (sol := sol) in Hinfer.
  rewrite <- Hinfer; clear Hinfer cnsq fact.
  intros Halldiff Hconfl Hin_doms.
  (* unfold materialize_vars_doms in Hconfl. *)
  (* rewrite flat_map_option_as_filter_map with (d := sint.empty) in Hconfl. *)
  (* Now we have that sol adheres to domain, so let us build a state with it. We use materialize_dom for this. *)
  remember (fun x => option_map_default (materialized_dom_for_var doms) sint.empty (var_name x)) as st.
  (* unfold sol_in_doms in Hin_doms. *)
  remember (map var_name_default (filter (filter_f_option (materialized_dom_for_var doms)) (diff_variables constr))) as vars.
  (* We now show that our solution adheres to this state for the particular variables we care about. *)
  assert (valuation_in_state st vars sol) as Hvars_in_state.
  {
    subst st vars; clear -Hin_doms.
    intros x.
    rewrite in_map_iff. setoid_rewrite filter_In.
    unfold filter_f_option.
    intros (v & Hvx & Hin & Hmtrl).
    unfold option_map_default.
    destruct (materialized_dom_for_var doms v) as [dom_mtrl|] eqn:Hmtrl_v; try discriminate; clear Hmtrl.
    apply var_name_default_and_materialized with (doms := doms) (dom := dom_mtrl) in Hvx; try assumption.
    subst v. rewrite Hmtrl_v.
    specialize (Hin_doms x).
    rewrite materialize_dom_iff_in_dom in Hin_doms.
    - unfold materialized_dom_for_var in Hmtrl_v.
      destruct smap.find as [dom|] eqn:Hfind; try easy.
      unfold dom_from_domains in Hin_doms.
      rewrite Hfind in Hin_doms. simpl in Hin_doms.
      rewrite Hmtrl_v in Hin_doms. apply Hin_doms.
    - unfold materialized_dom_for_var in Hmtrl_v.
      destruct smap.find eqn:Hfind; try easy.
      unfold dom_from_domains.
      rewrite Hfind.
      revert Hmtrl_v. clear.
      unfold materialize_dom, is_bounded.
      simpl. destruct lb_ub_from_dom as [lb_ub|]; easy.
  }
  clear Hin_doms.
  (* We now show we get a conflict if we have that some of the values in the particular variables we chose are not all distinct. This brings us a step closer to applying our core proof. *)
  enough (~ Alldifferent_l vars sol) as Halldiff_l.
  {
    clear -Halldiff Halldiff_l Heqvars.
    apply Halldiff_l; clear Halldiff_l.
    intros x y.
    subst vars.
    setoid_rewrite in_map_iff.
    setoid_rewrite filter_In.
    unfold filter_f_option.
    intros (vx' & Hx') (vy' & Hy').
    destruct (materialized_dom_for_var doms vx') eqn:Hmtrl_x; try easy.
    destruct (materialized_dom_for_var doms vy') eqn:Hmtrl_y; try easy.
    apply var_name_default_and_materialized with (x := x) in Hmtrl_x; try apply Hx'.
    apply var_name_default_and_materialized with (x := y) in Hmtrl_y; try apply Hy'.
    subst vx' vy'. simpl in *; clear t t0.
    specialize (Halldiff (var_name x) (var_name y)).
    simpl in Halldiff. apply Halldiff.
    - apply Hx'.
    - apply Hy'.
  }
  clear Halldiff.
  enough (~ AllDifferent_sat st vars) as Halldiff_sat.
  {
    intros Halldiff_l. apply Halldiff_sat; clear Halldiff_sat.
    unfold AllDifferent_sat.
    exists sol.
    split.
    - exact Hvars_in_state.
    - exact Halldiff_l.
  }
  (* Our goal is now such that we can apply the core proof! We need to choose the domain union and show that it indeed is the union according to the core proof's conditions. *)
  remember (sint.elements (union_sets (materialize_vars_doms (diff_variables constr) doms))) as domain_union.
  apply alldiff_conflict_if_union_lt_vars with (domain_union := domain_union).
  { subst domain_union. apply sint.elements_nodup. }
  { subst vars. clear. admit. (* This is quite annoying... Previous strategy still better for that reason. *) }
  { 
    (* We now need to show that the union used by teh checker is indeed a valid union in the sense of the core proof. *)
    subst st domain_union vars. clear.
    intros n.
    rewrite sint.elements_in. rewrite union_sets_spec.
    split; intros H.
    - destruct H as (s & Hin_mtrl & Hin).
      revert Hin_mtrl. unfold materialize_vars_doms.
      rewrite in_flat_map_option. intros (v & Hvconstr & Hmtrl).
      remember (var_name_default v) as x.
      exists x.
      split.
      + rewrite Heqx. apply in_map.
        rewrite filter_In.
        unfold filter_f_option.
        rewrite Hmtrl.
        easy.
      + unfold option_map_default.
        symmetry in Heqx.
        apply var_name_default_and_materialized with (doms := doms) (dom := s) in Heqx; try assumption.
        rewrite <- Heqx. rewrite Hmtrl.
        exact Hin.
    - destruct H as (x & Hinx & Hinn).
      rewrite in_map_iff in Hinx.
      destruct Hinx as (v & Hvx & Hinv).
      rewrite filter_In in Hinv.
      unfold filter_f_option in Hinv.
      destruct materialized_dom_for_var as [s|] eqn:Hmtrl in Hinv; try easy.
      exists s.
      apply var_name_default_and_materialized with (doms := doms) (dom := s) in Hvx; try assumption.
      rewrite <- Hvx in Hinn.
      unfold option_map_default in Hinn.
      rewrite Hmtrl in Hinn.
      split.
      + unfold materialize_vars_doms. rewrite in_flat_map_option. exists v.
        split; easy.
      + exact Hinn.
  }
  clear Hvars_in_state Heqst st.
  subst domain_union. 
  rewrite <- sint.cardinal_spec.
  rewrite Nat.ltb_lt in Hconfl.
  (* We now just need to show the length of our chosen vars and the length of materialize_vars_doms are equal. *)
  enough (length vars = length (materialize_vars_doms constr.(diff_variables) doms)) by lia.
  subst vars. clear.
  unfold materialize_vars_doms.
  rewrite flat_map_option_as_filter_map with (d := sint.empty).
  setoid_rewrite length_map. reflexivity.
Admitted.
