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

(** This file adds variables to domains and the idea that atomic constraints can apply only to particular variables. It also provides functions to convert a list of atomic constraints into a map of domains, for which we use MMaps (defined in the Maps module in the Utility file). *)

(** We use a simple pair instead of a Record since it is just two things. *)
Definition BoundAtomic := (string * Atomic)%type.
(** smap is a map with string keys (short for `string_map`). *)
Definition DomainMap := smap.t Domain.

(** This is used when we want to ensure only a specific subset of variables ends up in the final map, which is useful when for example we want to prove we have parameters for all of them in a constraint. It is important in the implementation of the cumulative constraint. *)
Definition check_in_vs (vs : option sstr.t) (x : string) :=
  match vs with
  | None => true
  | Some vs => sstr.mem x vs
  end.

(** This applies a single atomic to the current domains, ensuring that only the domain of the variable it applies to is updated. It returns None if the domain of that variable becomes empty. *)
Definition add_apply (vs : option sstr.t) (domains : DomainMap) (atom : (string * Atomic)) : option DomainMap :=
  match atom with
  | (x, atom) =>
    if check_in_vs vs x then
      let dom := 
        match smap.find x domains with
        | Some dom => dom
        | None => initial_dom
        end in
      match apply_atomics (atom :: nil) (Some dom) with
      | None => None
      | Some new_dom => 
        Some (smap.add x new_dom domains)
      end
    else Some domains
  end.

(** This function is not very useful in practice, since it does 'apply_holes' for each single atomic, which is a lot of wasted work. However, it was developed first and shows that add_apply'ing multiple times is equivalent to using the domains_from_var_atomics_all below. Note, fold_left_error returns early when an intermediate step returns None. *)
Definition domains_from_var_atomics (atoms : list (string * Atomic)) (vs : option sstr.t) :=
  fold_left_error (add_apply vs) atoms smap.empty.

(** Not used in practice, but is used for the specification. It simply filters all atomics for a particular key. *)
Definition from_var_atoms (x : string) (atoms : list (string * Atomic)) : list Atomic :=
  filter_pair_on_key x atoms.

(** Given a list of atomics, it builds a map that maps every variable to the list of atomics in the map. *)
Definition build_atoms_map (atoms : list (string * Atomic)) (vs : option sstr.t) :=
  map_from_prod_list (check_in_vs vs) atoms.

Definition map_domains_apply_f (atoms : list Atomic) :=
  apply_atomics atoms (Some initial_dom).

(** If multiple atomics are to be applied at once, this function is much more efficient since apply_atomics is called only once per variable. Note that `smap_valid` uses the MMap map operation so that the tree is not rebuilt, but it does have to check whether a none exists, iterating over all values and then mapping again to unwrap the options. The final empty check is to ensure equivalent behavior compared to domains_from_var_atomics. Use this for building the domains when you have multiple atomics that you immediately know must hold (like in premises). *)
Definition domains_from_var_atomics_all (atoms : list (string * Atomic)) (vs : option sstr.t) :=
  let atoms_map := build_atoms_map atoms vs in
  let dom_map := smap_valid initial_dom map_domains_apply_f atoms_map in
  if smap.is_empty dom_map
    then 
      if smap.is_empty atoms_map
        then Some smap.empty
        else None
    else Some dom_map.

(** Not used in practice, but used in the specification. It represents applying all atomics for a particular variable in one go to an initial, full domain. *)
Definition applied_dom (x : string) (atoms : list (string * Atomic)) :=
  apply_atomics (from_var_atoms x atoms) (Some initial_dom).

(** Useful lemma that can be used to show that when a domain map does not contain a particular variable, that must be because there are no atomics in the original list that mention it. *)
Lemma applied_exists_none :
  forall x atoms,
  dom_equiv (Some initial_dom) (applied_dom x atoms)
    <->
  forall a, ~ In (x, a) atoms.
Proof.
  intros x atoms.
  split; intros H.
  - intros a. unfold applied_dom in H.
    unfold dom_equiv in H.
    setoid_rewrite dom_effect_atomics in H.
    assert (forall y, is_in_dom y (Some initial_dom)) as Hinit.
    { intros y. unfold initial_dom. simpl.
      repeat split; try reflexivity.
      intros Hin. apply (sint.empty_spec Hin). }
    setoid_rewrite H in Hinit; clear H.
    intros Hin.
    assert (In a (from_var_atoms x atoms)) as Hatoms.
    { unfold from_var_atoms. unfold filter_pair_on_key.
      rewrite in_flat_map_option.
      exists (x, a). split.
      - exact Hin.
      - simpl. destruct (x =? x)%string eqn:Hxx.
        + reflexivity.
        + rewrite String.eqb_neq in Hxx. contradiction. }
    destruct (atm_cmp a) eqn:Hcmp.
    + specialize (Hinit (atm_val a + 1)).
      apply Hinit in Hatoms.
      unfold atomic_holds in Hatoms.
      rewrite Hcmp in Hatoms.
      lia.
    + specialize (Hinit (atm_val a - 1)).
      apply Hinit in Hatoms.
      unfold atomic_holds in Hatoms.
      rewrite Hcmp in Hatoms.
      lia.
    + specialize (Hinit (atm_val a + 1)).
      apply Hinit in Hatoms.
      unfold atomic_holds in Hatoms.
      rewrite Hcmp in Hatoms.
      lia.
    + specialize (Hinit (atm_val a)).
      apply Hinit in Hatoms.
      unfold atomic_holds in Hatoms.
      rewrite Hcmp in Hatoms.
      contradiction.
  - apply filter_pair_on_key_no_x in H.
    unfold applied_dom.
    unfold from_var_atoms.
    rewrite H.
    unfold apply_atomics.
    simpl. apply apply_holes_equiv.
Qed.

(** f here represents some assignment/solution. Indicates that all atomics are valid for their paticular variable. *)
Definition valid_atoms (f : string -> Z) (atoms : list (string * Atomic)) :=
  forall x a,
    In (x, a) atoms
      ->
    atomic_holds (f x) a.

(** If all atomics are valid and we get a domain equivalent to None, that means we have a contradiction. *)
Lemma applied_dom_none_false :
  forall atoms (f : string -> Z) x,
    valid_atoms f atoms
      ->
    dom_equiv (applied_dom x atoms) None
      ->
    False.
Proof.
  intros atoms f x.
  intros Hvalid Hnone.
  assert (~ is_in_dom (f x) None).
  { intros Hin. simpl in Hin. exact Hin. }
  apply H.
  unfold dom_equiv in Hnone.
  rewrite <- Hnone.
  unfold applied_dom.
  rewrite dom_effect_atomics.
  split.
  - apply all_in_inital_dom.
  - intros a Hin. apply Hvalid.
    apply filter_pair_on_key_spec.
    exact Hin.
Qed.
    
Definition default_atom := mk_atm_le 0.

(** Copied from Rocq 9.0 stdlib *)
Lemma filter_rev {A} (pred : A -> bool) (l : list A) : filter pred (rev l) = rev (filter pred l).
Proof.
  induction l; cbn [rev]; trivial.
  rewrite filter_app, IHl; cbn [filter].
  case pred; cbn [app]; auto using app_nil_r.
Qed.

(** This proposition represents a map of domains being correct: i.e. the domain for each variable is equivalent to applying exactly all atomics related to that variable to the initial domain. It also supports a predicate so that certain variables can be ignored. *)
Definition domains_equiv_atoms_cond (pred : string -> bool) (atoms : list (string * Atomic)) (domains : DomainMap) :=
  forall x, 
  match smap.find x domains with
  | None => pred x = false \/ forall a, ~ In (x, a) atoms
  | Some dom => pred x = true /\ dom_equiv (Some dom) (applied_dom x atoms)
  end.

(** Same as above but the specific condition that the variable must be in vs or that vs is None. *)
Definition domains_equiv_atoms_vs (vs : option sstr.t) (atoms : list (string * Atomic)) (domains : DomainMap) :=
  domains_equiv_atoms_cond (check_in_vs vs) atoms domains.

(** Same but with no condition. *)
Definition domains_equiv_atoms (atoms : list BoundAtomic) (domains : DomainMap) :=
  forall x,
    match smap.find x domains with
    | None => forall a, ~ In (x, a) atoms
    | Some dom => dom_equiv (Some dom) (applied_dom x atoms)
    end.

Lemma check_in_vs_none_domains_equiv :
  forall atoms doms,
  domains_equiv_atoms_vs None atoms doms
    <->
  domains_equiv_atoms atoms doms.
Proof.
  intros atoms doms.
  split; intros; 
  unfold domains_equiv_atoms_vs, domains_equiv_atoms_cond, domains_equiv_atoms in *.
  - intros x; specialize (H x).
    simpl in H.
    destruct smap.find.
    + apply H.
    + now destruct H. 
  - intros x; specialize (H x).
    destruct smap.find.
    + easy.
    + right. easy.
Qed.

(** This represents the state of a domain map being correct. If it is None, that means at least one variable has an empty domain based on all the atomics. *)
Definition domains_from_vars_P vs (atoms : list (string * Atomic)) (dom_map : option DomainMap) :=
  match dom_map with
  | Some dom_map => domains_equiv_atoms_vs vs atoms dom_map
  | None => exists x,
    dom_equiv (applied_dom x atoms) None
  end.

(** Below a are a bunch of helper lemmas. *)
Lemma applied_dom_cons_swap :
  forall x a atoms,
    dom_equiv (applied_dom x ((x, a) :: atoms))
    (apply_atomics (a :: nil)
    (applied_dom x atoms)).
Proof.
  intros x a atoms.
  assert (x =? x = true)%string as Hxb.
  { rewrite String.eqb_eq. reflexivity. }
  unfold applied_dom.
  rewrite <- apply_atomics_app.
  simpl from_var_atoms.
  rewrite Hxb.
  rewrite apply_atomics_app_swap.
  reflexivity.
Qed.
 
Lemma applied_dom_cons_initial :
  forall x a atoms,
    (forall a, ~ In (x, a) atoms)
      ->
    dom_equiv (applied_dom x ((x, a) :: atoms))
    (apply_atomics (a :: nil) (Some initial_dom)).
Proof.
  intros x a atoms Hnin.
  assert (x =? x = true)%string as Hxb.
  { rewrite String.eqb_eq. reflexivity. }
  apply filter_pair_on_key_no_x in Hnin.
  unfold applied_dom, from_var_atoms.
  simpl; rewrite Hxb.
  rewrite Hnin. simpl. reflexivity.
Qed.

Lemma applied_dom_cons_neq :
  forall x x' a atoms,
    x <> x'
      ->
    dom_equiv (applied_dom x' ((x, a) :: atoms))
    (applied_dom x' atoms).
Proof.
  intros x x' a atoms Hnin.
  assert (x =? x' = false)%string as Hxb.
  { rewrite String.eqb_neq. assumption. }
  unfold applied_dom, from_var_atoms.
  simpl; rewrite Hxb; simpl.
  reflexivity.
Qed.

(** Now come the proofs, which are all a bit too long and complicated for my taste. *)

(** This represents the correctness of add_apply on its own so that it can be used when applying a single atomic at a time to a domain map. The proof is more complicated than it maybe should be and has a lot of duplciation. *)
Lemma add_apply_step :
  forall vs doms atoms,
    domains_equiv_atoms_vs vs atoms doms 
      ->
    forall x a,
      match add_apply vs doms (x, a) with
      | None => check_in_vs vs x = true /\ dom_equiv (applied_dom x ((x, a) :: atoms)) None
      | Some doms' => domains_equiv_atoms_vs vs ((x, a) :: atoms) doms'
      end.
Proof.
  intros vs doms atoms.
  intros Hequiv x a.
  destruct add_apply as [doms'|] eqn:Haddapply.
  - unfold domains_equiv_atoms_vs, domains_equiv_atoms_cond in *.
    intros x'.
    unfold add_apply in Haddapply.
    destruct apply_atomics as [d'|] eqn:Happly.
    + destruct (String.string_dec x x') as [Hxx' | Hxx'].
      * subst x'; specialize (Hequiv x).
        destruct smap.find as [d|] eqn:Hfind.
        -- destruct Hequiv as [Hcheck Hequiv].
          rewrite Hcheck in Haddapply.
          inversion Haddapply; subst doms'; clear Haddapply.
          rewrite smap.add_spec1.
          split; try assumption.
          rewrite <- Happly; rewrite Hequiv.
          symmetry. apply applied_dom_cons_swap.
        -- destruct (check_in_vs);
          destruct Hequiv as [Hcheckf | Hin].
          ++ discriminate Hcheckf.
          ++ inversion Haddapply; subst doms'.
            rewrite smap.add_spec1.
            split; try reflexivity.
            rewrite <- Happly.
            symmetry. apply applied_dom_cons_initial.
            apply Hin.
          ++ inversion Haddapply; subst doms'.
            rewrite Hfind. left. reflexivity.
          ++ inversion Haddapply; subst doms'.
            rewrite Hfind. left. reflexivity.
    * destruct check_in_vs eqn:Hcheck.
      -- inversion Haddapply; subst doms'.
        rewrite smap.add_spec2; try assumption.
        specialize (Hequiv x').
        destruct (smap.find x').
        ++ split; try apply Hequiv.
          rewrite (proj2 Hequiv). symmetry.
          apply applied_dom_cons_neq;
          assumption.
        ++ destruct Hequiv as [Hcheckf' | Hin].
          ** left. apply Hcheckf'.
          ** right. intros a' [H | H]; try inversion H; subst;
          try contradiction; apply (Hin a' H).
      -- inversion Haddapply; subst doms'.
        specialize (Hequiv x').
        destruct (smap.find x' doms) eqn:Hfind.
        ++ destruct Hequiv as [Hcheck' Hequiv].
          split; try assumption.
          rewrite Hequiv. symmetry.
          apply applied_dom_cons_neq;
          assumption.
        ++ destruct Hequiv as [Hcheckf' | Hin].
          ** left. apply Hcheckf'.
          ** right. intros a' [H | H]; try inversion H; subst;
          try contradiction; apply (Hin a' H).
    + destruct check_in_vs eqn:Hcheck.
      { discriminate Haddapply. }
      inversion Haddapply; subst doms'.
      destruct (String.string_dec x x') as [Hxx' | Hxx'].
      * subst x'.
        specialize (Hequiv x).
        destruct (smap.find x).
        { rewrite Hcheck in Hequiv. easy. }
        destruct Hequiv as [Hcheckf | Hin].
        -- left. apply Hcheck.
        -- left. apply Hcheck.
      * specialize (Hequiv x').
        destruct (smap.find x').
        -- split; try apply Hequiv.
          rewrite (proj2 Hequiv).
          symmetry.
          apply applied_dom_cons_neq;
          assumption.
        -- destruct Hequiv as [Hcheckf | Hin].
          ++ left. apply Hcheckf.
          ++ right. intros a' [H | H]; try inversion H; subst;
          try contradiction; apply (Hin a' H).
  - unfold add_apply in Haddapply.
    destruct check_in_vs eqn:Hcheck.
    + split; try reflexivity.
      destruct apply_atomics as [d'|] eqn:Happly.
      * discriminate Haddapply.
      * unfold domains_equiv_atoms_vs, domains_equiv_atoms_cond in Hequiv.
        specialize (Hequiv x).
        destruct smap.find.
        -- destruct Hequiv as [_ Hequiv].
          rewrite <- Happly; rewrite Hequiv.
          apply applied_dom_cons_swap.
        -- destruct Hequiv as [Hcheckf | Hin].
          ++ rewrite Hcheck in Hcheckf;
            discriminate Hcheckf.
          ++ rewrite <- Happly.
            apply applied_dom_cons_initial;
            assumption.
    + discriminate Haddapply.
Qed. 
 
Lemma domains_from_var_atomics_correct :
  forall vs atoms,
    domains_from_vars_P vs atoms (domains_from_var_atomics atoms vs). 
Proof.
  intros vs.
  intros atoms.
  enough (domains_from_vars_P vs (rev atoms) (domains_from_var_atomics atoms vs)).
  {
    unfold domains_from_vars_P in *.
    assert (forall x, dom_equiv (applied_dom x atoms)
      (applied_dom x (rev atoms))) as Hrev.
    {
      clear. intros x.
      unfold dom_equiv; intros y.
      assert (from_var_atoms x (rev atoms) = rev (from_var_atoms x atoms)) as Hrev.
      {
        unfold from_var_atoms, filter_pair_on_key.
        repeat rewrite flat_map_option_as_filter_map with (d := default_atom).
        rewrite <- map_rev.
        rewrite filter_rev.
        reflexivity. 
      }
      unfold applied_dom.
      repeat rewrite dom_effect_atomics.
      rewrite Hrev.
      setoid_rewrite <- in_rev.
      reflexivity.
    }
    destruct (domains_from_var_atomics atoms vs) eqn:Hres.
    - unfold domains_equiv_atoms_vs, domains_equiv_atoms_cond in *.
      intros x; specialize (H x).
      destruct smap.find.
      + rewrite Hrev. exact H.
      + setoid_rewrite in_rev. exact H.
   - setoid_rewrite <- Hrev in H.
      apply H.
  }
  unfold domains_from_var_atomics.
  rewrite fold_left_error_as_fold_left.
  rewrite <- fold_left_rev_right.
  apply fold_ind.
  - unfold domains_from_vars_P.
    unfold domains_equiv_atoms_vs, domains_equiv_atoms_cond.
    intros x.
    rewrite smap.empty_spec.
    right.
    intros a Hin.
    destruct Hin.
  - intros [x' a] dom_map s.
    unfold domains_from_vars_P.
    intros IH.
    specialize add_apply_step with (vs := vs) (atoms := s) (a := a) (x := x') as Hstep.
    destruct (fold_left_error_f (add_apply vs) dom_map (x', a)) as [dom_map'|] eqn:Happly.
    { 
      unfold fold_left_error_f in Happly.
      destruct dom_map as [dom_map|].
      - specialize (Hstep dom_map).
        apply Hstep in IH; clear Hstep.
        rewrite Happly in IH.
        apply IH.
      - discriminate Happly.
    }
    {
      unfold fold_left_error_f in Happly.
      destruct dom_map as [dom_map|].
      - apply Hstep in IH; clear Hstep.
        rewrite Happly in IH.
        exists x'.
        apply IH.
      - clear Happly Hstep. destruct IH as [x Hx].
        exists x.
        unfold applied_dom; simpl.
        rewrite apply_atomics_app_swap.
        rewrite apply_atomics_app.
        rewrite Hx.
        unfold apply_atomics.
        simpl.
        reflexivity.
    }
Qed.

Lemma domains_from_var_atomics_all_correct :
  forall vs atoms,
    domains_from_vars_P vs atoms (domains_from_var_atomics_all atoms vs). 
Proof.
  (* This proof was supposed to be easier... *)
  intros vs atoms.
  unfold domains_from_vars_P.
  destruct (domains_from_var_atomics_all atoms vs) as [dom_map|] eqn:Hdom_map.
  - intros x.
    unfold domains_from_var_atomics_all in Hdom_map.
    destruct smap.is_empty eqn:Hempty.
    + destruct smap.is_empty eqn:Hempty2 in Hdom_map.
      * unfold build_atoms_map in Hempty2.
        inversion Hdom_map; subst; clear Hdom_map.
        rewrite smap.empty_spec.
        destruct (from_var_atoms x atoms) eqn:Hxatoms.
        -- right. unfold from_var_atoms in Hxatoms.
          apply filter_pair_on_key_no_x.
          exact Hxatoms.
        -- left.
          rewrite smap.is_empty_spec in Hempty2.
          specialize map_from_prod_list_spec with (f := check_in_vs vs) (l := atoms) as Hprod_spec.
          unfold map_from_prod_list_P in Hprod_spec.
          specialize (Hprod_spec x).
          rewrite (Hempty2 x) in Hprod_spec; clear Hempty2.
          destruct Hprod_spec; try assumption.
          exfalso.
          rewrite filter_pair_on_key_no_x in H.
          unfold from_var_atoms in Hxatoms.
          rewrite H in Hxatoms.
          discriminate Hxatoms.
      * discriminate Hdom_map.
    + inversion Hdom_map as [Hdom_map']; clear Hdom_map Hdom_map'.
      apply is_empty_map_exists in Hempty.
      apply smap_valid_spec in Hempty as Hvalid.
      specialize (in_smap_not_none _ _ _ _ _ Hempty) as Hnotnone; clear Hempty.
      destruct smap.find eqn:Hfind.
      * rewrite smap.find_spec in Hfind.
        rewrite <- smap.bindings_spec1 in Hfind.
        rewrite Hvalid in Hfind; clear Hvalid.
        rewrite <- In_to_InA_Duo_eq in Hfind.
        rewrite in_map_iff in Hfind.
        destruct Hfind as [[x' xatoms] [Hvalid Hin]].
        apply Hnotnone in Hin as Happly_not_none;
        clear Hnotnone.
        unfold valid_f in Hvalid.
        inversion Hvalid; subst; clear Hvalid.
        unfold option_map_default.
        destruct map_domains_apply_f eqn:Happly; try contradiction.
        rewrite <- Happly. clear -Hin.
        unfold applied_dom, map_domains_apply_f.
        split.
        -- specialize map_from_prod_list_spec with (f := check_in_vs vs) (l := atoms) as Hspec.
          specialize (Hspec x).
          rewrite In_to_InA_Duo_eq in Hin;
          rewrite smap.bindings_spec1 in Hin;
          rewrite <- smap.find_spec in Hin.
          unfold build_atoms_map in Hin.
          rewrite Hin in Hspec.
          apply Hspec.
        -- unfold dom_equiv; intros y.
          repeat rewrite dom_effect_atomics.
          setoid_rewrite in_map_prod_list at 1.
          2: { unfold build_atoms_map in Hin. apply Hin. }
          reflexivity.
      * destruct (smap.find x (build_atoms_map atoms vs)) as [xatoms|] eqn:Hatoms.
        -- clear -Hfind Hvalid Hatoms. 
          specialize (find_none_bindings _ _ _ Hfind) as Hin.
          rewrite Hvalid in Hin; clear Hvalid.
          setoid_rewrite in_map_iff in Hin.
          remember (valid_f initial_dom map_domains_apply_f (x, xatoms)) as res.
          destruct res as [x' xdom].
          specialize (Hin xdom).
          exfalso. apply Hin; clear Hin.
          exists (x, xatoms).
          rewrite <- Heqres.
          unfold valid_f in Heqres.
          inversion Heqres; subst x'.
          split; try reflexivity.
          rewrite In_to_InA_Duo_eq.
          rewrite smap.bindings_spec1.
          rewrite <- smap.find_spec.
          exact Hatoms.
        -- clear -Hatoms.
          specialize map_from_prod_list_spec with (f := check_in_vs vs) (l := atoms) as Hspec.
          specialize (Hspec x).
          unfold build_atoms_map in Hatoms. 
          rewrite Hatoms in Hspec.
          destruct Hspec as [Hfalse | Hin].
          ++ now left.
          ++ now right. 
  - unfold domains_from_var_atomics_all in Hdom_map.
    destruct (smap.is_empty) eqn:Hempty.
    + unfold smap_valid in Hempty.
      destruct (check_none) eqn:Hcheck.
      2: { 
        apply smap_valid_nonempty_input with (d := initial_dom) in Hcheck as Hnot_empty.
        - unfold smap_valid in Hnot_empty.
          rewrite Hcheck in Hnot_empty.
          rewrite Hnot_empty in Hempty.
          discriminate Hempty.
        - destruct (smap.is_empty (build_atoms_map atoms vs)) eqn:Hbuild.
          { discriminate Hdom_map. }
          clear Hdom_map.
          rewrite smap_prps.not_empty_has_binding in Hbuild.
          destruct Hbuild as [x [xatoms Hin]].
          exists (x, xatoms).
          exact Hin.
      }
      clear Hdom_map Hempty.
      unfold check_none in Hcheck.
      rewrite smap.exists_spec in Hcheck.
      rewrite existsb_exists in Hcheck.
      destruct Hcheck as [[x d] [Hx Hopt]].
      exists x.
      rewrite smap.map_spec in Hx.
      rewrite in_map_iff in Hx.
      destruct Hx as [[x' xatoms] [Hmap Hin]].
      inversion Hmap; subst; clear Hmap.
      unfold map_domains_apply_f in Hopt.
      unfold opt_is_none in Hopt.
      destruct apply_atomics eqn:Happly in Hopt.
      { discriminate Hopt. }
      clear Hopt.
      rewrite <- Happly; clear Happly.
      unfold applied_dom, dom_equiv; intros y.
      repeat rewrite dom_effect_atomics.
      setoid_rewrite in_map_prod_list at 2.
      2: { apply Hin. }
      reflexivity.
    + discriminate Hdom_map.
Qed.