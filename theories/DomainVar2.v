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

Definition initial_dom := mkDom None None sint.empty.

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
  flat_map_option (fun a => if (fst a =? x)%string then Some (snd a) else None) atoms.

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
  (* unfold domains_from_var_atomics.
  rewrite fold_left_error_as_fold_left.
  rewrite <- fold_left_rev_right.
  generalize dependent atoms. *) 
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
        unfold from_var_atoms.
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
(*     
    specialize (dom_permute_equiv (from_var_atoms x (rev atoms)) (from_var_atoms x atoms) initial_dom) as Hrev.
    assert (Permutation (from_var_atoms x (rev atoms)) (from_var_atoms x atoms)).
    {
      clear.
      unfold from_var_atoms.
      remember (fun a : string * Atomic =>
        if (fst a =? x)%string
        then Some (snd a)
        else None) as f.
      repeat rewrite flat_map_option_as_filter_map with (d := default_atom).
      apply Permutation_map.
      apply permutation_filter. 
      - decide equality.
        + apply atom_eq_dec.
        + apply String.string_dec.
      - symmetry. apply Permutation_rev.
    }
    apply Hrev in H; clear Hrev.
    unfold domain_equiv in *.
    rewrite <- H. apply Hmap. *)
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
    2: {
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
    intros x Hcheck.
    simpl.
    rewrite apply_atomics_app.
    unfold fold_left_error_f in Happly.
    destruct dom_map as [dom_map|].
    + unfold add_apply in Happly.
      specialize (IH x Hcheck).
      destruct (check_in_vs vs x') eqn:Hcheck'.
      * clear Hcheck Hcheck'. 
        destruct (apply_atomics (a :: nil)) as [doma|] eqn:Happlya.
        2: { discriminate Happly. }
        inversion Happly; subst dom_map'; clear Happly.
        destruct (x' =? x)%string eqn:Hxx'.
        ++ rewrite String.eqb_eq in Hxx'; subst x'. 
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
        ++ clear Happlya. 
          rewrite String.eqb_neq in Hxx'.
          rewrite smap.add_spec2; try assumption.
        (* destruct (smap.find x' dom_map) as [domx'|] eqn:Hfind.
        -- destruct (apply_atomics (a :: nil) (Some domx')) as [doma|] eqn:Happlya.
          2: { discriminate Happly. }
          inversion Happly; subst dom_map'; clear Happly.
          destruct (x' =? x)%string eqn:Hxx'.
          ++ rewrite String.eqb_eq in Hxx'; subst x'. 
            rewrite <- smap.find_spec in Hmap.
            rewrite smap.add_spec1 in Hmap.
            inversion Hmap; subst doma; clear Hmap.
            rewrite smap.find_spec in Hfind.
            apply IH in Hfind; clear IH.
            rewrite <- apply_atomics_app.
            unfold dom_equiv in *. intros y.
            rewrite <- Happlya.
            specialize (Hfind y).
            repeat rewrite dom_effect_atomics.
            rewrite <- Hfind.
            rewrite dom_effect_atomics.
            simpl. clear. split; intros H;
            destruct_ands; repeat split; try easy.
            ** intros a' Hin.
              apply H2. right. exact Hin.
            ** intros a' Ha.
              destruct Ha as [Haa'|Hfalse]; try contradiction.
              subst a'. apply H2.
              left. reflexivity.
            ** intros a' Hin.
              destruct Hin as [Haa' | Hin].
              { subst a'. apply H2. left. reflexivity. }
              { apply H12. exact Hin. }
          ++ rewrite String.eqb_neq in Hxx'.
            rewrite <- smap.find_spec in Hmap.
            rewrite smap.add_spec2 in Hmap; try assumption.
            rewrite smap.find_spec in Hmap.
            apply IH in Hmap; clear IH.
            rewrite <- apply_atomics_app. simpl.
            apply Hmap.
        -- admit. *)
      * inversion Happly; subst dom_map'; clear Happly.
        remember (match smap.find x dom_map with
          | Some dom => dom
          | None => initial_dom
          end); clear Heqd.
        destruct (x' =? x)%string eqn:Hxx'.
        { rewrite String.eqb_eq in Hxx'; subst x'; rewrite Hcheck' in Hcheck. discriminate Hcheck. }
        rewrite <- apply_atomics_app. simpl.
        apply IH.
    + discriminate Happly.
Qed.

    + simpl. destruct (check_in_vs vs x') eqn:Hcheck'.
      * clear Hcheck Hcheck'. 
        destruct (smap.find x' dom_map) eqn:Hfind.
        -- destruct (apply_atomics_dom (a :: nil) d) as [d'|] eqn:Happly; try reflexivity.
          intros Hmap.
          destruct (x' =? x)%string eqn:Hxx'.
          ++ rewrite String.eqb_eq in Hxx'; subst x'.
            rewrite <- smap.find_spec in Hmap.
            rewrite smap.add_spec1 in Hmap;
            inversion Hmap; subst d'; clear Hmap.
            rewrite smap.find_spec in Hfind.
            apply IH in Hfind; clear IH.
            unfold domain_equiv in *.





      * intros H. apply IH in H.
        destruct (x' =? x)%string eqn:Hxx'.
        -- rewrite String.eqb_eq in Hxx'.
          subst x'. rewrite Hcheck' in Hcheck. discriminate Hcheck.
        -- simpl. apply H. 
    + simpl. reflexivity.

  induction atoms.
  - intros dom_map x dom.
    simpl.
    unfold domains_from_var_atomics.
    rewrite fold_left_error_as_fold_left. simpl.
    intros H; inversion H; subst dom_map.
    intros Hmap.
    rewrite <- smap.find_spec in Hmap.
    rewrite smap.empty_spec in Hmap.
    discriminate Hmap.
  - unfold domains_from_var_atomics.
    rewrite fold_left_error_as_fold_left.
    rewrite <- fold_left_rev_right.
    intros dom_map x dom.
