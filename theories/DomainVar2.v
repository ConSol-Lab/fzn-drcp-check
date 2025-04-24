Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import String.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Arith.PeanoNat.
Require Import Bool.
Require Import Lia.
Require Checker.Atomic.
Require Import Checker.Variable.
Require Import Checker.Domain.
Require Coq.Structures.OrdersEx.
Require Checker.Utility.
Import Utility.ListEx.
Import Utility.Maps.
Import Utility.Tactics.
Require MMaps.Interface.
Require MMaps.RBT.
Require Import Sorting.Permutation.

Definition AtomicsMap := smap.t (list Atomic).

Definition DomainMap := smap.t Domain.

Definition check_in_vs (vs : option sstr.t) (x : string) :=
  match vs with
  | None => true
  | Some vs => sstr.mem x vs
  end.

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

Definition domains_from_var_atomics (atoms : list (string * Atomic)) (vs : option sstr.t) :=
  fold_left_error (add_apply vs) atoms smap.empty.

Definition from_var_atoms (x : string) (atoms : list (string * Atomic)) : list Atomic :=
  filter_pair_on_key x atoms.

Import Utility.ListInd.

Definition default_atom := mk_atm_le 0.

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
      dom_equiv (apply_atomics (from_var_atoms x atoms) (Some initial_dom)) 
        (Some 
          match smap.find x dom_map with 
          | Some dom => dom
          | None => initial_dom
          end
        )
    | None => exists x,
      dom_equiv (apply_atomics (from_var_atoms x atoms) (Some initial_dom)) None
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
        simpl.
        rewrite apply_atomics_app_swap.
        rewrite apply_atomics_app.
        rewrite Hx.
        unfold apply_atomics.
        simpl.
        reflexivity.
    }
Qed.

Definition build_atoms_map (atoms : list (string * Atomic)) (vs : option sstr.t) :=
  map_from_prod_list (check_in_vs vs) atoms.

Definition map_domains_apply_f (atoms : list Atomic) :=
  apply_atomics atoms (Some initial_dom).

Definition domains_from_var_atomics_all (atoms : list (string * Atomic)) (vs : option sstr.t) :=
  let atoms_map := build_atoms_map atoms vs in
  let dom_map := smap_valid initial_dom map_domains_apply_f atoms_map in
  if smap.is_empty dom_map
    then 
      if smap.is_empty atoms_map
        then Some smap.empty
        else None
    else Some dom_map.

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
        rewrite <- Happly. clear - Hin.
        unfold map_domains_apply_f.
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
          unfold from_var_atoms.
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
      unfold dom_equiv; intros y.
      repeat rewrite dom_effect_atomics.
      setoid_rewrite in_map_prod_list at 2.
      2: { apply Hin. }
      reflexivity.
    + discriminate Hdom_map.
Qed.