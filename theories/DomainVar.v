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
Require Import Checker.Zext.

(** This file adds variables to domains and the idea that atomic constraints can apply only to particular variables. It also provides functions to convert a list of atomic constraints into a map of domains, for which we use MMaps (defined in the Maps module in the Utility file). *)

(** We use a simple pair instead of a Record since it is just two things. *)
Definition BoundAtomic := (string * Atomic)%type.
Definition Domains := smap.t Domain.

Definition included_doms (doms : Domains) : list (string * Domain) := smap.bindings doms.

Definition dom_from_domains (m : Domains) (x : string) : Domain :=
  option_default initial_dom (smap.find x m).

Declare Scope Domain_scope.
Local Open Scope Domain_scope.
Infix "d->" := dom_from_domains (at level 65) : Domain_scope.

Lemma dom_from_domains_if_in :
  forall doms x dom,
    In (x, dom) (included_doms doms) -> doms d-> x = dom.
Proof.
  intros doms x dom.
  rewrite smap_in_spec. rewrite <- smap.find_spec.
  unfold dom_from_domains.
  intros H.
  rewrite H. simpl. reflexivity.
Qed.

Lemma doms_maps_or_not_included (doms : Domains) (x : string) :
  {smap.MapsTo x (doms d-> x) doms} + {doms d-> x = initial_dom /\ forall dom, ~ In (x, dom) (included_doms doms)}.
Proof.
  unfold dom_from_domains. destruct smap.find eqn:Hfind.
  - left. simpl. now rewrite <- smap.find_spec.
  - right. split; try reflexivity.
    intros dom.
    apply find_none_bindings.
    exact Hfind.
Qed.

Definition from_var_atoms (x : string) (atoms : list BoundAtomic) : list Atomic :=
  filter_pair_on_key x atoms.

Definition applied_dom (x : string) (atoms : list BoundAtomic) :=
  apply_atomics (from_var_atoms x atoms) initial_dom.

Definition valid_domains (doms : Domains) (atoms : list BoundAtomic) :=
  forall x,
    dom_equiv (doms d-> x) (applied_dom x atoms).

Definition include_all (x : string) := true.

Lemma include_all_true (x : string) :
  include_all x = true.
Proof. reflexivity. Qed.

Definition tightened_doms (doms : Domains) :=
  forall x,
    dom_tightened (doms d-> x).

Definition build_atoms_map (atoms : list BoundAtomic) :=
  map_from_prod_list include_all atoms.

Definition dom_from_initial (atoms : list Atomic) :=
  apply_atomics atoms initial_dom.

Definition domains_from_atomics (atoms : list BoundAtomic) : Domains :=
  let atoms_map := build_atoms_map atoms in
    smap.map dom_from_initial atoms_map.

(* The reverse definitely does not hold. *)
Lemma dom_equiv_initial :
  forall atoms atoms',
  (forall a, In a atoms <-> In a atoms')
    ->
  dom_equiv (apply_atomics atoms initial_dom) (apply_atomics atoms' initial_dom).
Proof.
  intros atoms atoms'.
  intros Hatoms.
  unfold dom_equiv. intros y.
  setoid_rewrite dom_effect_atomics.
  setoid_rewrite Hatoms. reflexivity.
Qed.
 
Lemma domains_from_atomics_correct :
  forall atoms doms,
  doms = domains_from_atomics atoms
    ->
  valid_domains doms atoms.
Proof.
  intros atoms doms.
  intros Hdoms.
  intros x.
  unfold domains_from_atomics, build_atoms_map in Hdoms.
  (* What to do? We want to use the properties of map_from_prod_list and map, but they need to know whether x is in the map or not. *)
  destruct (doms_maps_or_not_included doms x) as [Hmaps | (Hinitial & Hnincluded)].
  - rewrite <- smap_in_spec in Hmaps.
    subst doms.
    rewrite smap.map_spec in Hmaps.
    rewrite in_map_iff in Hmaps.
    destruct Hmaps as ((x' & xatoms) & H' & Hin).
    inversion H'; subst x'; clear -Hin.
    unfold dom_from_initial, applied_dom.
    apply dom_equiv_initial.
    intros a.
    apply in_map_prod_list with (a := a) in Hin.
    rewrite Hin. reflexivity.
  - rewrite Hinitial.
    unfold applied_dom.
    enough (from_var_atoms x atoms = nil).
    { rewrite H. simpl. reflexivity. }
    apply filter_pair_on_key_no_x.
    (* What to do? We know the goal can only be derived from map_from_prod_list if x is not in it. So we destruct on that possibility. *)
    destruct (smap.find x (map_from_prod_list include_all atoms)) as [atoms' |] eqn:Hfindprod.
    + exfalso. specialize (Hnincluded (dom_from_initial atoms')).
      apply Hnincluded. subst doms.
      unfold included_doms.
      rewrite smap.map_spec.
      rewrite in_map_iff.
      exists (x, atoms').
      split; try reflexivity.
      rewrite smap_in_spec.
      rewrite <- smap.find_spec.
      exact Hfindprod.
    + clear -Hfindprod.
      specialize map_from_prod_list_spec as Hprod_spec.
      unfold map_from_prod_list_P in Hprod_spec.
      specialize (Hprod_spec _ include_all atoms x).
      rewrite Hfindprod in Hprod_spec.
      destruct Hprod_spec; try discriminate.
      exact H.
Qed.

Lemma domains_from_atomics_if_in :
  forall atoms x dom,
    In (x, dom) (smap.bindings (domains_from_atomics atoms))
      ->
    exists atom, In atom (from_var_atoms x atoms).
Proof.
  intros atoms x dom.
  unfold domains_from_atomics.
  rewrite smap.map_spec. rewrite in_map_iff.
  intros ((x' & xatoms) & H' & Hin).
  inversion H'; subst; clear H'.
  unfold build_atoms_map in Hin.
  specialize (in_map_prod_list _ _ _ _ _ Hin) as [Hnnil Hinfilter].
  destruct xatoms; try contradiction.
  exists a.
  rewrite <- Hinfilter.
  left. reflexivity.
Qed.

Definition check_domains_consistent (doms : Domains) : bool :=
  smap.for_all (fun x dom => dom_check_consistent dom) doms.

Definition valid_atoms (sol : string -> Z) (atoms : list BoundAtomic) :=
  forall x a,
    In (x, a) atoms
      ->
    atomic_holds (sol x) a.

Lemma initial_consistent :
  dom_consistent initial_dom.
Proof.
  exists 0. unfold is_in_dom, initial_dom.
  simpl; easy.
Qed.

Lemma dom_consistent_if_valid_atoms :
  forall sol atoms,
    valid_atoms sol atoms
      ->
    forall x,
      dom_consistent (applied_dom x atoms).
Proof.
  intros sol atoms. intros Hatoms.
  intros x.
  exists (sol x).
  unfold applied_dom. rewrite dom_effect_atomics.
  split; try easy.
  intros a Hin.
  apply Hatoms.
  rewrite <- filter_pair_on_key_spec.
  exact Hin.
Qed.

Lemma domains_consistent_if_valid_atoms :
  forall sol atoms doms,
    valid_atoms sol atoms
      ->
    valid_domains doms atoms
      ->
    forall x,
      dom_consistent (doms d-> x).
Proof.
  intros sol atoms doms.
  intros Hatoms Hdoms. intros x.
  rewrite (Hdoms x).
  apply dom_consistent_if_valid_atoms with (sol := sol).
  exact Hatoms.
Qed.

      
Lemma inconsistent_contradiction :
  forall sol atoms doms,
    valid_atoms sol atoms
      ->
    valid_domains doms atoms
      ->
    check_domains_consistent doms <> false.
Proof.
  intros sol atoms doms Hatoms Hdoms.
  unfold check_domains_consistent.
  rewrite smap.for_all_spec.
  intros Hfalse.
  apply forallb_false in Hfalse.
  destruct Hfalse as ((x & xdom) & Hindoms & Hcheck).
  apply dom_inconsistent_if_checked_false in Hcheck.
  apply Hcheck.
  apply dom_from_domains_if_in in Hindoms.
  rewrite <- Hindoms.
  apply domains_consistent_if_valid_atoms with (sol := sol) (atoms := atoms); assumption.
Qed.

Definition tighten_doms (doms : Domains) :=
  smap.map tighten_dom doms.

Definition tighten_doms_equiv :
  forall doms x,
    dom_equiv (tighten_doms doms d-> x) (doms d-> x).
Proof.
  intros doms x.
  destruct (doms_maps_or_not_included (tighten_doms doms) x) as [Hmaps | (Hinitial & Hnincluded)].
  - rewrite <- smap_in_spec in Hmaps.
    unfold tighten_doms in *.
    rewrite smap.map_spec in Hmaps.
    rewrite in_map_iff in Hmaps.
    destruct Hmaps as ((x' & dom_tight) & Htighten & Hin).
    inversion Htighten.
    subst x'. rewrite smap_in_spec in Hin.
    rewrite <- smap.find_spec in Hin.
    unfold dom_from_domains. rewrite Hin.
    simpl. rewrite <- tighten_equiv. reflexivity.
  - destruct (doms_maps_or_not_included doms x) as [Hmaps_doms | (Hinitial_doms & Hnincluded_doms)].
    + exfalso. 
      apply Hnincluded with (dom := (tighten_dom (doms d-> x))).
      unfold included_doms, tighten_doms.
      rewrite smap.map_spec.
      rewrite in_map_iff.
      exists (x, (doms d-> x)).
      split; try reflexivity.
      rewrite smap_in_spec.
      exact Hmaps_doms.
    + rewrite Hinitial_doms. rewrite Hinitial.
      reflexivity. 
Qed.

Definition doms_apply_tighten (doms : Domains) (atomic : BoundAtomic) : option Domains :=
  match atomic with
  | (x, atom) =>
    match apply_atomic_tighten (doms d-> x) atom with
    | None => None
    | Some dom => Some (smap.add x dom doms)
    end
  end.

Lemma doms_apply_tighten_step :
  forall doms atoms,
    valid_domains doms atoms
      ->
    forall x a,
      match doms_apply_tighten doms (x, a) with
      | None => ~ dom_consistent (applied_dom x ((x, a) :: atoms))
      | Some doms' => valid_domains doms' ((x, a) :: atoms)
      end.
Proof.
  intros doms atoms. intros Hdoms.
  intros x xatom.
  unfold doms_apply_tighten. specialize (apply_atomic_tighten_valid (doms d-> x) xatom) as Hspec.
  destruct apply_atomic_tighten as [dom|].
  - unfold valid_domains. intros x'.
    unfold applied_dom. simpl. unfold dom_from_domains.
    destruct (x =? x')%string eqn:Hxx'; simpl.
    + rewrite String.eqb_eq in Hxx'; subst x'.
      rewrite smap.add_spec1. simpl.
      rewrite Hspec; clear Hspec.
      (* could be improved with some more propers *)
      unfold dom_equiv. intros y. 
      rewrite <- apply_atomic_spec.
      rewrite dom_effect_atomics.
      rewrite <- apply_atomic_spec.
      rewrite (Hdoms x).
      unfold applied_dom. rewrite dom_effect_atomics.
      repeat split; try easy.
    + rewrite String.eqb_neq in Hxx'.
      rewrite smap.add_spec2; try easy.
      apply Hdoms.
  - intros Hconsistent.
    apply Hspec. destruct Hconsistent as (y & Hy).
    exists y. revert Hy.
    rewrite <- apply_atomic_spec.
    rewrite (Hdoms x).
    unfold applied_dom.
    setoid_rewrite dom_effect_atomics.
    simpl. destruct (x =? x)%string eqn:Hxx.
    2: { rewrite String.eqb_neq in Hxx. contradiction. }
    simpl. intros (_ & Hholds).
    split; [split|]; try easy.
    + intros a Hin.
      apply Hholds. right. exact Hin.
    + apply Hholds. left. reflexivity.
Qed.
  
Definition sol_in_doms (sol : string -> Z) (doms : Domains) :=
  forall x,
    is_in_dom (sol x) (doms d-> x).

Lemma valid_domains_sol_in_doms_iff_valid_atoms :
  forall atoms doms sol,
    valid_domains doms atoms
      ->
    valid_atoms sol atoms
      <->
    sol_in_doms sol doms.
Proof.
  intros atoms doms sol.
  intros Hdoms.
  split.
  - intros Hatoms. intros x.
    rewrite (Hdoms x).
    unfold applied_dom.
    rewrite dom_effect_atomics.
    split; try easy.
    intros a Hin.
    apply Hatoms.
    rewrite <- filter_pair_on_key_spec.
    apply Hin.
  - intros Hindoms.
    intros x a Hin.
    specialize (Hdoms x).
    specialize (Hindoms x).
    rewrite Hdoms in Hindoms.
    unfold applied_dom in Hindoms.
    rewrite dom_effect_atomics in Hindoms.
    apply Hindoms.
    rewrite filter_pair_on_key_spec.
    exact Hin.
Qed.