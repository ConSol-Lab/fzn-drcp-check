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

Definition AtomicsMap := smap.t (list Atomic).

Definition DomainMap := smap.t Domain.

(* This is used when we want to ensure only a specific subset of variables ends up in the final map, which is useful when for example we want to prove we have parameters for all of them in a constraint. *)
Definition check_in_vs (vs : option sstr.t) (x : string) :=
  match vs with
  | None => true
  | Some vs => sstr.mem x vs
  end.

(* This applies a single atomic to the current domains. *)
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

(* This function is not very useful in practice, since it does 'apply_holes' for each single atomic, which is a lot of wasted work. However, it was developed first and shows that add_apply'ing multiple times is equivalent to using the domains_from_var_atomics_all below. Note, fold_left_error returns early when an intermediate step returns None. *)
Definition domains_from_var_atomics (atoms : list (string * Atomic)) (vs : option sstr.t) :=
  fold_left_error (add_apply vs) atoms smap.empty.

(* Not used in practice, but is used for the specification. It simply filters all atomics for a particular key. *)
Definition from_var_atoms (x : string) (atoms : list (string * Atomic)) : list Atomic :=
  filter_pair_on_key x atoms.

(* Given a list of atomics, it builds a map that maps every variable to the list of atomics in the map. *)
Definition build_atoms_map (atoms : list (string * Atomic)) (vs : option sstr.t) :=
  map_from_prod_list (check_in_vs vs) atoms.

Definition map_domains_apply_f (atoms : list Atomic) :=
  apply_atomics atoms (Some initial_dom).

(* If multiple atomics are to be applied at once, this function is much more efficient since apply_atomics is called only once per variable. Note that `smap_valid` uses the MMap map operation so that the tree is not rebuilt, but it does have to check whether a none exists, iterating over all values and then mapping again to unwrap the options. The final empty check is to ensure equivalent behavior compared to domains_from_var_atomics. *)
Definition domains_from_var_atomics_all (atoms : list (string * Atomic)) (vs : option sstr.t) :=
  let atoms_map := build_atoms_map atoms vs in
  let dom_map := smap_valid initial_dom map_domains_apply_f atoms_map in
  if smap.is_empty dom_map
    then 
      if smap.is_empty atoms_map
        then Some smap.empty
        else None
    else Some dom_map.

(* Not used in practice, but used in the specification. It represents applying all atomics for a particular variable in one go to an initial, full domain. *)
Definition applied_dom (x : string) (atoms : list (string * Atomic)) :=
  apply_atomics (from_var_atoms x atoms) (Some initial_dom).

(* Useful lemma that can be used to show that when a domain map does not contain a particular variable, that must be because there are no atomics in the original list that mention it. *)
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

(* f here represents some assignment/solution. Indicates that all atomics are valid for their paticular variable. *)
Definition valid_atoms (f : string -> Z) (atoms : list (string * Atomic)) :=
  forall x a,
    In (x, a) atoms
      ->
    atomic_holds (f x) a.

(* If all atomics are valid and we get a domain equivalent to None, that means we have a contradiction. *)
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

(* Copied from Rocq 9.0 stdlib *)
Lemma filter_rev {A} (pred : A -> bool) (l : list A) : filter pred (rev l) = rev (filter pred l).
Proof.
  induction l; cbn [rev]; trivial.
  rewrite filter_app, IHl; cbn [filter].
  case pred; cbn [app]; auto using app_nil_r.
Qed.

Definition domains_from_vars_P vs (atoms : list (string * Atomic)) (dom_map : option DomainMap) :=
    match dom_map with
    | Some dom_map =>
      forall x,
      check_in_vs vs x = true
        ->
      dom_equiv (applied_dom x atoms) 
        (Some 
          match smap.find x dom_map with 
          | Some dom => dom
          | None => initial_dom
          end
        )
    | None => exists x,
      dom_equiv (applied_dom x atoms) None
    end.

(* Maybe return error saying which variable is incorrect? *)
Lemma domains_from_var_atomics_correct :
  forall vs atoms,
    domains_from_vars_P vs atoms (domains_from_var_atomics atoms vs). 
Proof.
  intros vs.
  intros atoms.
  enough (domains_from_vars_P vs (rev atoms) (domains_from_var_atomics atoms vs)).
  {
    unfold domains_from_vars_P in *.
    assert (forall dom x, dom_equiv (apply_atomics (from_var_atoms x (rev atoms)) dom)
      (apply_atomics (from_var_atoms x atoms) dom)) as Hrev.
    {
      clear. intros dom x.
      unfold dom_equiv; intros y.
      assert (from_var_atoms x (rev atoms) = rev (from_var_atoms x atoms)) as Hrev.
      {
        unfold from_var_atoms, filter_pair_on_key.
        repeat rewrite flat_map_option_as_filter_map with (d := default_atom).
        rewrite <- map_rev.
        rewrite filter_rev.
        reflexivity. 
      }
      repeat rewrite dom_effect_atomics.
      rewrite Hrev.
      setoid_rewrite <- in_rev.
      reflexivity.

    }
    destruct (domains_from_var_atomics atoms vs) eqn:Hres.
    - intros x Hcheck.
      unfold applied_dom.
      rewrite <- Hrev.
      apply H.
      exact Hcheck.
    - setoid_rewrite <- Hrev.
      apply H.
  }
  unfold domains_from_var_atomics.
  rewrite fold_left_error_as_fold_left.
  rewrite <- fold_left_rev_right.
  apply fold_ind.
  - unfold domains_from_vars_P.
    intros x Hcheck.
    simpl.
    unfold apply_atomics. simpl.
    specialize apply_holes_equiv as Heqv.
    specialize (Heqv (Some initial_dom)) .
    unfold apply_holes_opt in Heqv.
    unfold option_map_flat in Heqv.
    symmetry. exact Heqv.
  - intros [x' a] dom_map s.
    unfold domains_from_vars_P.
    intros IH.
    destruct (fold_left_error_f (add_apply vs) dom_map (x', a)) as [dom_map'|] eqn:Happly.
    { 
      intros x Hcheck.
      unfold applied_dom.
      simpl.
      rewrite apply_atomics_app.
      unfold fold_left_error_f in Happly.
      destruct dom_map as [dom_map|].
      - unfold add_apply in Happly.
        specialize (IH x Hcheck).
        destruct (check_in_vs vs x') eqn:Hcheck'.
        + clear Hcheck Hcheck'. 
          destruct (apply_atomics (a :: nil)) as [doma|] eqn:Happlya.
          2: { discriminate Happly. }
          inversion Happly; subst dom_map'; clear Happly.
          destruct (x' =? x)%string eqn:Hxx'.
          * rewrite String.eqb_eq in Hxx'; subst x'. 
            rewrite smap.add_spec1.
            rewrite <- apply_atomics_app.
            remember (match smap.find x dom_map with
              | Some dom => dom
              | None => initial_dom
              end); clear Heqd.
            rewrite <- Happlya.
            unfold dom_equiv in *; intros y.
            specialize (IH y).
            repeat rewrite dom_effect_atomics.
            rewrite <- IH.
            unfold applied_dom.
            rewrite dom_effect_atomics.
            simpl. clear. split; intros H;
            destruct_ands; repeat split; try easy.
            { intros a' Hin.
              apply H2. right. exact Hin. }
            { intros a' Ha.
              destruct Ha as [Haa'|Hfalse]; try contradiction.
              subst a'. apply H2.
              left. reflexivity. }
            { intros a' Hin.
              destruct Hin as [Haa' | Hin].
              { subst a'. apply H2. left. reflexivity. }
              { apply H12. exact Hin. } }
          * clear Happlya. 
            rewrite String.eqb_neq in Hxx'.
            rewrite smap.add_spec2; try assumption.
        + inversion Happly; subst dom_map'; clear Happly.
          remember (match smap.find x dom_map with
            | Some dom => dom
            | None => initial_dom
            end); clear Heqd.
          destruct (x' =? x)%string eqn:Hxx'.
          { rewrite String.eqb_eq in Hxx'; subst x'; rewrite Hcheck' in Hcheck. discriminate Hcheck. }
          rewrite <- apply_atomics_app. simpl.
          apply IH.
      - discriminate Happly.
    }
    {
      unfold fold_left_error_f in Happly.
      destruct dom_map as [dom_map|].
      - exists x'.
        unfold add_apply in Happly.
        destruct (check_in_vs vs x') eqn:Hcheck'.
        + specialize (IH x' Hcheck').
          remember (match smap.find x' dom_map with
            | Some dom => dom
            | None => initial_dom
            end).
          unfold applied_dom.
          simpl.
          destruct (x' =? x')%string eqn:Hxx'.
          2: { rewrite String.eqb_neq in Hxx'. contradiction.  }
          clear Hxx'.
          destruct (apply_atomics (a :: nil) (Some d)) eqn:Happlya.
          { discriminate Happly. }
          clear Happly.
          rewrite apply_atomics_app_swap.
          rewrite apply_atomics_app.
          rewrite IH.
          rewrite Happlya.
          reflexivity.
        + discriminate Happly.
      - clear Happly. destruct IH as [x Hx].
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
  - intros x Hcheck.
    unfold domains_from_var_atomics_all in Hdom_map.
    destruct smap.is_empty eqn:Hempty.
    + destruct smap.is_empty eqn:Hempty2 in Hdom_map.
      * unfold build_atoms_map in Hempty2.
        inversion Hdom_map; subst; clear Hdom_map.
        rewrite smap.empty_spec.
        assert (from_var_atoms x atoms = nil).
        {
          (* Maybe fold this out as a lemma for map_from_prod_list *)
          unfold from_var_atoms.
          apply filter_pair_on_key_no_x.
          rewrite smap.is_empty_spec in Hempty2.
          specialize map_from_prod_list_spec with (f := check_in_vs vs) (l := atoms) as Hprod_spec.
          unfold map_from_prod_list_P in Hprod_spec.
          specialize (Hempty2 x).
          specialize (Hprod_spec x).
          rewrite Hempty2 in Hprod_spec.
          destruct Hprod_spec as [Hfalse | Hnin].
          - rewrite Hcheck in Hfalse. discriminate Hfalse.
          - apply Hnin.
        }
        unfold applied_dom.
        rewrite H. unfold apply_atomics.
        simpl. symmetry. rewrite apply_holes_equiv.
        simpl. reflexivity.
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
        unfold dom_equiv; intros y.
        repeat rewrite dom_effect_atomics.
        setoid_rewrite in_map_prod_list at 2.
        2: { apply Hin. }
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
        -- clear -Hatoms Hcheck.
          specialize map_from_prod_list_spec with (f := check_in_vs vs) (l := atoms) as Hspec.
          specialize (Hspec x).
          unfold build_atoms_map in Hatoms. 
          rewrite Hatoms in Hspec.
          destruct Hspec as [Hfalse | Hin].
          { now rewrite Hcheck in Hfalse. }
          apply filter_pair_on_key_no_x in Hin.
          unfold applied_dom, from_var_atoms.
          rewrite Hin.
          unfold apply_atomics. simpl.
          symmetry.
          rewrite apply_holes_equiv.
          reflexivity.
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

