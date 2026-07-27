Require Import ZArith.
Require Import Bool.
Require Import String.
Require Import List.
Require Import Lia.
Require Checker.Spec.
Import Spec.ProofFacts.
Import Spec.ConstraintDefinitions.
Require Import Logic.FinFun.
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
Definition state {V} := V -> MaterializedDomain.

Definition valuation_in_state {V} (st : state) (vs : list V) (v : V -> Z) : Prop :=
  forall x, In x vs -> sint.In (v x) (st x).

Definition Alldifferent_l {V} (vs : list V) (sol : V -> Z) : Prop :=
    NoDup (map sol vs).

Definition AllDifferent_sat {V} (st : state) (vs : list V) :=
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
Lemma alldiff_conflict_if_union_lt_vars {V} (st : state) (vars : list V) (domain_union : list Z) :
  NoDup domain_union
    ->
  (forall n, In n domain_union <-> (exists x, In x vars /\ sint.In n (st x)))
    ->
  length domain_union < length vars
    ->
  ~ AllDifferent_sat st vars.
Proof.
  intros Hunion_nd Hunion Hlengths.
  intros [A [Hastate Halldiff]].
  enough (length domain_union >= length vars) by lia; clear Hlengths.
  rewrite <- length_map with (f := A).
  apply NoDup_incl_length.
  - exact Halldiff.
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

(** Given a domain map, we want to get the materialized domain corresponding to a var. *)
Definition materialized_dom_for_var (doms: Domains) (var : Var) : option sint.t :=
  match var with
  | var_name x =>
    match smap.find x doms with
    | None => None
    | Some dom => materialize_dom dom
    end
  | const value => Some (sint.add value sint.empty)
  end.

Lemma in_materialized_iff_in_dom_for_var :
  forall n s doms x,
    materialized_dom_for_var doms (var_name x) = Some s
      ->
    (sint.In n s <-> sint.In n (option_default sint.empty (materialize_dom (doms d-> x)))) /\ is_bounded (doms d-> x) = true.
Proof.
  intros n s doms x.
  unfold materialized_dom_for_var, dom_from_domains, option_default, materialize_dom, is_bounded.
  destruct smap.find as [dom|] eqn:Hfind.
  - destruct lb_ub_from_dom as [[lb ub]|].
    + intros H; inversion H; subst s; clear H.
      split; reflexivity.
    + easy.
  - easy.
Qed.

Lemma in_materialized_const_if_is_const :
  forall n n' s doms,
    materialized_dom_for_var doms (const n) = Some s
      ->
    (sint.In n' s <-> n = n').
Proof.
  intros n n' s doms.
  unfold materialized_dom_for_var.
  intros H; inversion H; clear H; subst.
  rewrite sint.add_spec.
  split.
  - intros [H | Hfalse].
    + easy.
    + destruct (sint.empty_spec Hfalse).
  - intros; subst.
    left; reflexivity.
Qed.

 
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
(** This is the actual checker. *)
Definition alldifferent_checker (fact : ProofFact) (constraint : AlldifferentConstraint) : bool :=
  match infer_domains fact with
  | None => false
  | Some (domains, _) =>
    let materialized_doms := materialize_vars_doms constraint.(diff_variables) domains in
    sint.cardinal (union_sets materialized_doms) <? length materialized_doms
  end.

(** For efficiency, we do not explicitly compute the variables in the materialize_vars_doms, but we do want to reason about exactly which variables show will not be all different. First, we compute all variables with finite domains, as these are the only ones with a finite domain size that we can reason about. *)
(* Definition bounded_vars (doms : Domains) :=
  filter (fun x => is_bounded (doms d-> x)) (map fst (smap.bindings doms)).
*)
Definition same_ident (x : string) (var : Var) : bool :=
  match var with
  | var_name y => (x =? y)%string
  | _ => false
  end.

(** These are not used for computation, just for the proofs. In combination with bounded_vars they allow specifying exactly which variable domains are included in the domains of materialize_vars_doms. *)
(* Definition constr_vars (vs : list Var) (constr : AlldifferentConstraint) :=
  filter (fun x => existsb (same_var x) constr.(diff_variables)) vs.
 *)
Definition is_variable (v : Var) : Prop :=
  match v with
  | var_name x => True
  | _ => False
  end.

Definition bounded_in_vars (doms : Domains) (vars : list Var) : list Var :=
  flat_map_option (fun x =>
    match is_bounded (doms d-> x) && existsb (same_ident x) vars with
    | true => Some (var_name x)
    | false => None
    end
  ) (map fst (smap.bindings doms)).

Definition const_vars (vars : list Var) :=
  filter (fun v => match v with | const _ => true | _ => false end) vars.

Definition proof_variables (doms : Domains) (constr : AlldifferentConstraint) : list Var :=
  bounded_in_vars doms constr.(diff_variables) ++ const_vars constr.(diff_variables).

(* Lemma is_bounded_in_doms_ex_dom :
  forall doms x,
    is_bounded (doms d-> x) = true
      ->
    smap.find x doms = Some (doms d-> x).
Proof.
  intros doms x.
  unfold dom_from_domains.
  destruct is_bounded eqn:Hbounded; try easy.
  intros _.
  unfold option_default in Hbounded.
  destruct (smap.find x) as [dom|] eqn:Hfind.
  { exists dom. reflexivity. }
  exfalso.
  revert Hbounded.
  unfold is_bounded, initial_dom. 
  destruct lb_ub_from_dom as [[lb ub]|] eqn:Hlubub; unfold lb_ub_from_dom in Hlubub; easy.
Qed.
 *)

Lemma is_bounded_in_doms_ex_dom :
  forall doms x,
    is_bounded (doms d-> x) = true
      ->
    smap.find x doms = Some (doms d-> x).
Proof.
  intros doms x.
  unfold dom_from_domains.
  destruct is_bounded eqn:Hbounded; try easy.
  intros _.
  unfold option_default in *.
  destruct (smap.find x) as [dom|] eqn:Hfind.
  { reflexivity. }
  exfalso.
  revert Hbounded.
  unfold is_bounded, initial_dom. 
  destruct lb_ub_from_dom as [[lb ub]|] eqn:Hlubub; unfold lb_ub_from_dom in Hlubub; easy.
Qed.


Lemma in_bounded_in_vars :
  forall v doms vars,
    In v (bounded_in_vars doms vars)
      <->
    (In v vars
      /\
      match v with
      | var_name x => is_bounded (doms d-> x) = true
      | const n => False
      end
    ).
Proof.
  intros v doms vars.
  unfold bounded_in_vars.
  rewrite in_flat_map_option.
  assert (forall x, existsb (same_ident x) vars = true <-> In (var_name x) vars) as Hexists_ident_in.
  {
    intros x.  
    rewrite existsb_exists.
    unfold same_ident.
    split.
    - intros (v' & Hvin & Hsame).
      destruct v'; try discriminate.
      rewrite String.eqb_eq in Hsame.
      subst ident.
      exact Hvin.
    - intros Hin. exists (var_name x).
      rewrite String.eqb_eq.
      now split.
  }
  destruct v as [x|].
  - split.
    + intros (x' & (Hin & H)).
      destruct is_bounded eqn:Hbounded; 
      destruct existsb eqn:Hident;
      simpl in H; inversion H.
      subst x'.
      now rewrite Hexists_ident_in in Hident.
    + intros Hin.
      exists x.
      split.
      * rewrite in_map_iff.
        exists (x, doms d-> x).
        simpl; split; try easy.
        rewrite smap_in_spec.
        destruct Hin as [_ His_bounded].
        unfold is_bounded in His_bounded.
        destruct lb_ub_from_dom eqn:Hlbub; try discriminate.
        unfold dom_from_domains in *.
        destruct smap.find eqn:Hfind.
        2: { unfold lb_ub_from_dom in Hlbub. discriminate Hlbub. }
        simpl.
        rewrite <- smap.find_spec.
        exact Hfind.
      * destruct Hin as [Hin Hbounded].
        rewrite Hbounded.
        rewrite <- Hexists_ident_in in Hin.
        rewrite Hin. simpl.
        reflexivity.
  - split; try easy.
    intros (x & (Hin & H)).
    destruct is_bounded; destruct existsb;
    simpl in H; discriminate.
Qed.

Lemma proof_variables_or :
  forall v doms constr,
    In v (proof_variables doms constr)
      <->
    (In v constr.(diff_variables)
      /\
      match v with
      | var_name x => is_bounded (doms d-> x) = true
      | const _ => True
      end
    ).
Proof.
  intros v doms vars.
  unfold proof_variables.
  rewrite in_app_iff.
  rewrite in_bounded_in_vars.
  unfold const_vars.
  rewrite filter_In.
  destruct v.
  - split.
    + now intros [Hv | Hconst].
    + intros H.
      left. exact H.
  - repeat split; try easy.
    + now destruct H as [Hfalse | Hconst].
    + intros H.
      right.
      split; try reflexivity.
      apply H.
Qed.

(* Lemma const_in_bounded:
  forall n vars doms,
  In (const n) vars
    ->
  In (const n) (bounded_vars doms vars).
Proof.
  intros n vars doms.
  induction vars as [| v vars IH].
  { intros H. destruct H. }
  simpl. intros [Hveq | Hin].
  - subst v. left. reflexivity.
  - destruct v.
    + destruct is_bounded.
      * right. apply IH; exact Hin.
      * apply IH; exact Hin.
    + right. apply IH; exact Hin.
Qed.
   *)

(** Here we show that bounded constraint variables will have a materialized domain. This connects what we do in the checker with the function we use to denote the actual variables in the conflict. *)
(* Lemma materialized_in_constr_iff_in_constr_bounded :
  forall constr doms v,
  In v constr.(diff_variables)
    ->
  (materialized_dom_for_var doms v <> None
    <->
  In v (bounded_vars doms constr.(diff_variables))).
Proof.
  intros constr doms v.
  intros Hin.
  unfold materialized_dom_for_var.
  destruct v as [x|] eqn:Hvx.
  2: { 
    split. 
    - intros _. apply const_in_bounded. exact Hin.
    - intros _. now intros H.
  } 
  unfold bounded_vars.
  setoid_rewrite filter_In.
  unfold is_bounded, materialize_dom, option_default, dom_from_domains.
  destruct smap.find as [dom|] eqn:Hfind; repeat split; try easy; destruct lb_ub_from_dom as [[lb ub]|]; repeat split; try easy.
Qed. *)

Lemma proof_variables_nodup doms constr :
  NoDup constr.(diff_variables)
    ->
  NoDup (proof_variables doms constr).
Proof.
  intros Hconstr_nd.
  unfold proof_variables.
  apply NoDup_app.
  - unfold bounded_in_vars.
    rewrite flat_map_option_as_filter_map with (d := const 0).
    remember (fun x : string =>
      if
      is_bounded (doms d-> x) &&
      existsb (same_ident x)
      (diff_variables constr)
      then Some (var_name x)
      else None) as fn.
    apply Injective_map_NoDup_in.
    {
      intros x y. setoid_rewrite filter_In.
      unfold filter_f_option.
      unfold option_map_default.
      destruct (fn x) as [fx|] eqn:Hfnx; try easy.
      destruct (fn y) as [fy|] eqn:Hfny; try easy.
      intros [Hxin _] [Hyin _].
      subst fn.
      destruct is_bounded; destruct existsb;
      destruct is_bounded; destruct existsb;
      simpl in *;
      try discriminate.
      inversion Hfnx; inversion Hfny.
      intros H.
      inversion H.
      reflexivity.
    }
    apply NoDup_filter.
    apply nodup_bindings_keys.
  - unfold const_vars. apply NoDup_filter.
    exact Hconstr_nd.
  - intros v Hin.
    apply in_bounded_in_vars in Hin.
    intros Hinv.
    unfold const_vars in Hinv.
    rewrite filter_In in Hinv.
    destruct v; easy.
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
  (* Distinct values require distinct variables, so the constraint's variables are pairwise distinct. *)
  pose proof (NoDup_map_inv _ _ Halldiff) as Hconstr_nd.
  (* Now we have that sol adheres to domain, so let us build a state with it. We use materialize_dom_for_var for this. *)
  remember (fun v => option_default sint.empty (materialized_dom_for_var doms v)) as st.
  unfold sol_in_doms in Hin_doms.
  remember (proof_variables doms constr) as vars.
  (* We now show that our solution adheres to this state for the particular variables we care about. *)
  assert (valuation_in_state st vars (fun v => evaluate v sol)) as Hvars_in_state.
  {
    clear -Heqst Heqvars Hin_doms.
    intros v.
    subst st vars.
    intros Hin.
    apply proof_variables_or in Hin.
    unfold materialized_dom_for_var.
    destruct v as [x | n].
    - destruct Hin as (Hin & Hbounded).
      apply is_bounded_in_doms_ex_dom in Hbounded as Hdomex.
      rewrite Hdomex.
      simpl.
      apply materialize_dom_iff_in_dom with (y := sol x).
      + exact Hbounded.
      + apply Hin_doms.
    - simpl. rewrite sint.add_spec. left. reflexivity.
  }
  clear Hin_doms.
  assert (NoDup vars) as Hvars_nd
    by (subst vars; apply proof_variables_nodup, Hconstr_nd).
  (* We now show we get a conflict if we have that some of the values in the particular variables we chose are not all distinct. This brings us a step closer to applying our core proof. *)
  enough (~ Alldifferent_l vars (fun v => evaluate v sol)) as Halldiff_l.
  {
    clear -Halldiff Halldiff_l Heqvars Hvars_nd.
    apply Halldiff_l; clear Halldiff_l.
    apply nodup_sublist with (l2 := map (fun v => evaluate v sol) constr.(diff_variables)).
    - exact Halldiff.
    - apply sub_list_map, sublist_if_in_nodup; [| exact Hvars_nd ].
      subst vars.
      intros v Hin.
      apply proof_variables_or in Hin.
      apply Hin.
  }
  clear Halldiff.
  enough (~ AllDifferent_sat st vars) as Halldiff_sat.
  {
    intros Halldiff_l. apply Halldiff_sat; clear Halldiff_sat.
    unfold AllDifferent_sat.
    exists (fun v => evaluate v sol).
    split.
    - exact Hvars_in_state.
    - exact Halldiff_l.
  }
  (* Our goal is now such that we can apply the core proof! We need to choose the domain union and show that it indeed is the union according to the core proof's conditions. *)
  remember (sint.elements (union_sets (materialize_vars_doms (diff_variables constr) doms))) as domain_union.
  apply alldiff_conflict_if_union_lt_vars with (domain_union := domain_union).
  { subst domain_union. apply sint.elements_nodup. }
  { 
    (* We now need to show that the union used by the checker is indeed a valid union in the sense of the core proof. *)
    subst st domain_union vars. clear.
    intros n.
    rewrite sint.elements_in. rewrite union_sets_spec.
    split; intros H.
    - destruct H as (s & Hin_mtrl & Hin).
      revert Hin_mtrl. unfold materialize_vars_doms.
      rewrite in_flat_map_option. intros (v & Hvconstr & Hmtrl). 
      exists v.
      specialize (proof_variables_or v doms constr) as Hproof.
      destruct v as [x | c].
      + apply in_materialized_iff_in_dom_for_var with (n := n) in Hmtrl.
        split.
        * now apply Hproof.
        * destruct Hmtrl as [Hsin Hbounded].
          unfold materialized_dom_for_var.
          rewrite is_bounded_in_doms_ex_dom;
          try exact Hbounded.
          apply Hsin.
          exact Hin.
      + apply in_materialized_const_if_is_const with (n := c) (n' := n) in Hmtrl.
        unfold materialized_dom_for_var. simpl.
        rewrite Hmtrl in Hin. subst n.
        split.
        * apply Hproof.
          split; try reflexivity.
          apply Hvconstr.
        * rewrite sint.add_spec.
          left. reflexivity.
    - destruct H as (v & Hvin & Hndom).
      unfold materialize_vars_doms.
      setoid_rewrite in_flat_map_option.
      unfold option_default in Hndom.
      destruct materialized_dom_for_var as [s|] eqn:Hmtrl.
      2: { destruct (sint.empty_spec Hndom). }
      exists s.
      split; try exact Hndom.
      exists v.
      split; try exact Hmtrl.
      rewrite proof_variables_or in Hvin.
      apply Hvin.
  }
  clear Hvars_in_state Heqst st.
  subst domain_union. 
  rewrite <- sint.cardinal_spec.
  rewrite Nat.ltb_lt in Hconfl.
  (* The checker uses the length of the materialize_vars_doms, which we know to be the same as the number of bounded variables + constant values in our constraint. We must now show this correspondence. Unfortunately they are not exactly equal, but we only have to show that one is longer than the other for the bound to be tight enough. *)
  enough (length vars >= length (materialize_vars_doms constr.(diff_variables) doms)) by lia.
  clear Hconfl. subst vars.
  (* We want to compare lengths of lists of equal type, so we use the properties of flat_map_option to extract the variables. *)
  unfold materialize_vars_doms.
  rewrite flat_map_option_as_filter_map with (d := sint.empty).
  rewrite length_map.
  apply NoDup_incl_length.
  - apply NoDup_filter. exact Hconstr_nd.
  - intros v. rewrite filter_In. unfold filter_f_option.
    destruct materialized_dom_for_var as [s|] eqn:Hmtrl_doms; try easy.
    intros [Hinconstr _].
    rewrite proof_variables_or.
    split; try exact Hinconstr.
    destruct v as [x|]; try reflexivity.
    apply (in_materialized_iff_in_dom_for_var 0%Z) in Hmtrl_doms.
    apply Hmtrl_doms.
Qed.

Open Scope string_scope.

(* Should be true, there is a conflict. *)
Compute 
  let constr :=
    {| diff_variables := var_name "x" :: var_name "y" :: nil |} in
  let fact := 
    {| 
      i_premises :=
        ("x", mk_atm_eq 1) ::
        ("y", mk_atm_eq 1) :: nil ;
      i_consequent := None
    |}
  in
  alldifferent_checker fact constr.

(* Should be false. *)
Compute 
  let constr :=
    {| diff_variables := var_name "x" :: var_name "y" :: nil |} in
  let fact := 
    {| 
      i_premises :=
        ("x", mk_atm_le 3) ::
        ("x", mk_atm_ge 0) ::
        ("x", mk_atm_ne 2) ::
        ("y", mk_atm_eq 1) :: nil ;
      i_consequent := None
    |}
  in
  alldifferent_checker fact constr.

(* Should be true. Union is 3 and 5 but we have 3 variables. *)
Compute 
  let constr :=
    {| diff_variables := var_name "x" :: var_name "y" :: var_name "z" :: nil |} in
  let fact := 
    {| 
      i_premises :=
        ("x", mk_atm_le 5) ::
        ("x", mk_atm_ne 4) :: 
        ("x", mk_atm_ge 3) ::
        ("y", mk_atm_le 5) ::
        ("y", mk_atm_ge 3) :: 
        ("y", mk_atm_ne 4) :: 
        ("z", mk_atm_le 5) :: 
        ("z", mk_atm_ge 3) :: 
        ("z", mk_atm_ne 4) :: 
        nil ;
      i_consequent := None
    |}
  in
  alldifferent_checker fact constr.

(* Should be true. Constant 1 causes x to not be able to be 1. *)
Compute 
  let constr :=
    {| diff_variables := var_name "x" :: const 1%Z :: nil |} in
  let fact := 
    {| 
      i_premises :=
        ("x", mk_atm_eq 1) :: nil ;
      i_consequent := None
    |}
  in
  alldifferent_checker fact constr.
