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

Lemma in_materialized_iff_in_dom_for_var :
  forall n s doms x,
    materialized_dom_for_var doms (var_name x) = Some s
      ->
    (sint.In n s <-> sint.In n (option_default sint.empty (materialize_dom (doms d-> x)))).
Proof.
  intros n s doms x.
  unfold materialized_dom_for_var, dom_from_domains, option_default, materialize_dom.
  destruct smap.find as [dom|] eqn:Hfind.
  - destruct lb_ub_from_dom as [[lb ub]|].
    + intros H; inversion H; subst s; clear H.
      reflexivity.
    + easy.
  - easy.
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
(** This is the actual checker. If assumptions are made using constant values in the constraint, we ignore them and they will not be checked. *)
Definition alldifferent_checker (fact : ProofFact) (constraint : AlldifferentConstraint) : bool :=
  match infer_domains fact with
  | None => false
  | Some (domains, _) =>
    let materialized_doms := materialize_vars_doms constraint.(diff_variables) domains in
    sint.cardinal (union_sets materialized_doms) <? length materialized_doms
  end.

(** For efficiency, we do not explicitly compute the variables in the materialize_vars_doms, but we do want to reason about exactly which variables show will not be all different. First, we compute all variables with finite domains, as these are the only ones with a finite domain size that we can reason about. *)
Definition bounded_vars (doms : Domains) :=
  filter (fun x => is_bounded (doms d-> x)) (map fst (smap.bindings doms)).

Definition same_ident (x : string) (var : Var) : bool :=
  match var with
  | var_name y => (x =? y)%string
  | _ => false
  end.

(** These are not used for computation, just for the proofs. In combination with bounded_vars they allow specifying exactly which variable domains are included in the domains of materialize_vars_doms. *)
Definition constr_vars (vs : list string) (constr : AlldifferentConstraint) :=
  filter (fun x => existsb (same_ident x) constr.(diff_variables)) vs.

(** Here we show that bounded constraint variables will have a materialized domain. This connects what we do in the checker with the function we use to denote the actual variables in the conflict. *)
Lemma materialized_in_constr_iff_in_constr_bounded :
  forall constr doms v,
  (In v constr.(diff_variables)
    /\
  materialized_dom_for_var doms v <> None)
    <->
  In v (map var_name (constr_vars (bounded_vars doms) constr)).
Proof.
  intros constr doms v.
  unfold materialized_dom_for_var.
  rewrite in_map_iff.
  destruct v as [x|] eqn:Hvx.
  2: { split; intros H; try easy. destruct H as (x & Hfalse & _). discriminate. }
    enough (In (var_name x) (diff_variables constr) /\ match smap.find x doms with
  | Some dom => materialize_dom dom
  | None => None
  end <> None <-> In x (constr_vars (bounded_vars doms) constr)) as Henough. 
  { split; intros H.
    - exists x. split; try reflexivity.
      apply Henough. exact H.
    - destruct H as (x' & Hxx' & H).
      inversion Hxx'; subst x'.
      apply Henough. exact H. }
  unfold constr_vars, bounded_vars.
  setoid_rewrite filter_In; setoid_rewrite filter_In.
  unfold is_bounded, materialize_dom, dom_from_domains, option_default.
  setoid_rewrite existsb_exists.
  destruct smap.find as [dom|] eqn:Hfind.
  2: { simpl. repeat split; try easy. }
  destruct lb_ub_from_dom as [[lb ub]|]; try easy.
  repeat split; try easy.
  - rewrite in_map_iff.
    exists (x, dom).
    split; try reflexivity.
    rewrite smap_in_spec.
    rewrite <- smap.find_spec.
    exact Hfind.
  - exists (var_name x).
    split.
    + apply H.
    +  simpl. rewrite String.eqb_eq. reflexivity.
  - destruct H as (_ & (v' & Hin & Hxv')).
    unfold same_ident in Hxv'.
    destruct v' as [x'|]; try discriminate.
    rewrite String.eqb_eq in Hxv'; subst x'.
    exact Hin.
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
  (* Now we have that sol adheres to domain, so let us build a state with it. We use materialize_dom for this. *)
  remember (fun x => option_default sint.empty (materialize_dom (doms d-> x))) as st.
  unfold sol_in_doms in Hin_doms.
  remember (constr_vars (bounded_vars doms) constr) as vars.
  (* We now show that our solution adheres to this state for the particular variables we care about. *)
  assert (valuation_in_state st vars sol) as Hvars_in_state.
  {
    clear -Heqst Heqvars Hin_doms.
    intros x.
    subst st vars.
    unfold constr_vars, bounded_vars.
    rewrite filter_In; rewrite filter_In.
    intros ((_ & Hisbounded) & _).
    apply materialize_dom_iff_in_dom with (y := sol x) in Hisbounded.
    apply Hisbounded.
    apply Hin_doms.
  }
  clear Hin_doms.
  (* We now show we get a conflict if we have that some of the values in the particular variables we chose are not all distinct. This brings us a step closer to applying our core proof. *)
  enough (~ Alldifferent_l vars sol) as Halldiff_l.
  {
    clear -Halldiff Halldiff_l Heqvars.
    apply Halldiff_l; clear Halldiff_l.
    intros x y.
    subst vars.
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
  { subst vars. clear. unfold constr_vars, bounded_vars. apply NoDup_filter. apply NoDup_filter. apply nodup_bindings_keys. }
  { 
    (* We now need to show that the union used by teh checker is indeed a valid union in the sense of the core proof. *)
    subst st domain_union vars. clear.
    intros n.
    rewrite sint.elements_in. rewrite union_sets_spec.
    split; intros H.
    - destruct H as (s & Hin_mtrl & Hin).
      revert Hin_mtrl. unfold materialize_vars_doms.
      rewrite in_flat_map_option. intros (v & Hvconstr & Hmtrl). 
      assert (In v (map var_name (constr_vars (bounded_vars doms) constr))) as Hvin.
      { rewrite <- materialized_in_constr_iff_in_constr_bounded. split.
        - exact Hvconstr.
        - intros Hnone. rewrite Hnone in Hmtrl. discriminate Hmtrl. }
      rewrite in_map_iff in Hvin.
      destruct Hvin as (x & Hxv & Hxin).
      exists x.
      split; try exact Hxin.
      rewrite <- in_materialized_iff_in_dom_for_var.
      + exact Hin.
      + subst v. exact Hmtrl.
    - destruct H as (x & Hxin & Hndom).
      apply in_map with (f := var_name) in Hxin.
      rewrite <- materialized_in_constr_iff_in_constr_bounded in Hxin.
      destruct Hxin as [Hvin Hmtrl].
      destruct materialized_dom_for_var as [s|] eqn:Hs; try easy; clear Hmtrl.
      exists s.
      split.
      + unfold materialize_vars_doms. rewrite in_flat_map_option. exists (var_name x).
        split.
        * exact Hvin.
        * exact Hs.
      + apply in_materialized_iff_in_dom_for_var with (n := n) in Hs.
        apply Hs. exact Hndom.
  }
  clear Hvars_in_state Heqst st.
  subst domain_union. 
  rewrite <- sint.cardinal_spec.
  rewrite Nat.ltb_lt in Hconfl.
  (* The checker uses the length of the materialize_vars_doms, which we know to be the same as the number of bounded variables in our constraint. We must now show this correspondence. Unfortunately they are not exactly equal, but we only have to show that one is longer than the other for the bound to be tight enough. *)
  enough (length vars >= length (materialize_vars_doms constr.(diff_variables) doms)) by lia.
  clear Hconfl. subst vars.
  (* We want to compare lengths of lists of equal type, so we use the properties of flat_map_option to extract the variables. Note: if you try to use as vars the filtered constraint Var (with filter_f_option) you have to map it to default and that NoDup proof is not trivial. *)
  unfold materialize_vars_doms.
  rewrite flat_map_option_as_filter_map with (d := sint.empty).
  rewrite length_map.
  rewrite <- length_map with (f := var_name).
  apply NoDup_incl_length.
  - apply NoDup_filter. apply constr.(diff_unique_vars).
  - intros v. rewrite filter_In. unfold filter_f_option.
    destruct materialized_dom_for_var as [s|] eqn:Hmtrl_doms; try easy.
    intros [Hinconstr _].
    rewrite <- materialized_in_constr_iff_in_constr_bounded.
    split.
    + exact Hinconstr.
    + intros Hnone. rewrite Hnone in Hmtrl_doms; discriminate. 
Qed.

Lemma var_name_inj :
  forall l,
    NoDup l
      ->
    NoDup (map var_name l).
Proof.
  induction l.
  - simpl. intros. apply NoDup_nil.
  - simpl. intros Hnodup.
    inversion Hnodup; subst x l0.
    specialize (IHl H2).
    apply NoDup_cons.
    + intros Hin.
      apply H1.
      rewrite in_map_iff in Hin.
      destruct Hin as (a' & Haa' & Hin).
      inversion Haa'; subst a'.
      exact Hin.
    + exact IHl.
Qed.

Definition build_alldifferent (vs : list string) : AlldifferentConstraint :=
  let nodup_strs := sstr.elements (sstr.build vs) in 
  let nodup_vars := map var_name nodup_strs in
  {|
    diff_variables := nodup_vars;
    diff_unique_vars := var_name_inj nodup_strs (sstr.elements_nodup (sstr.build vs))
  |}.

Open Scope string_scope.

(* Should be true, there is a conflict. *)
Compute 
  let constr := build_alldifferent (
    "x" :: "y" :: nil
  ) in
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
  let constr := build_alldifferent (
    "x" :: "y" :: nil
  ) in
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
  let constr := build_alldifferent (
    "x" :: "y" :: "z" :: nil
  ) in
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
