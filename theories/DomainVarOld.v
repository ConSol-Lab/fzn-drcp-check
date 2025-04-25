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
Require Import Checker.DomainVar.
Require Checker.Utility.
Import Utility.ListEx.
Import Utility.Sets.
Import Utility.Maps.
Import Utility.Tactics.

(* ################################# *)

(* This file originally served as interface between the old checker and new checker. *)

(* ################################ *)

Definition VarAtomic := Atomic.Atomic.

Definition zn_interval := (Z * N)%type.

Definition var_cmp_to_cmp (var_cmp : Atomic.AtomicComparator) : AtomicComparator :=
  match var_cmp with
  | Atomic.less_equal => less_equal
  | Atomic.greater_equal => greater_equal
  | Atomic.equal => equal
  | Atomic.not_equal => not_equal
  end.

Definition var_atm_to_atm (atm : VarAtomic) : BoundAtomic :=
  (var_name (Atomic.var atm), {| atm_cmp := (var_cmp_to_cmp (Atomic.comparator atm)); atm_val := (Atomic.value atm) |}).

Definition var_to_atoms (v : Var) :=
  match v with
  | interval v =>
    (v.(name), mk_atm_ge v.(lower_bound)) ::
    (v.(name), mk_atm_le v.(upper_bound)) ::
    nil
  end.

Definition var_atomics_to_atoms (v_a : VarAtomic) : list BoundAtomic :=
  var_atm_to_atm v_a :: var_to_atoms (Atomic.var v_a).

Definition var_atomics_to_atomics (atomics : list VarAtomic) : list BoundAtomic :=
  flat_map var_atomics_to_atoms atomics.

Definition sol_to_assignment (vs : list Var) (sol : Assignment) : string -> Z :=
  fun x =>
    match find (fun v =>
      match v with
      | interval v =>
        (v.(name) =? x)%string
      end
    ) vs with
    | None => Z0
    | Some v => sol.(find_value) v
    end
  .


Definition var_atomic_equiv (v_a : Atomic.Atomic) (a : Atomic) :=
  var_cmp_to_cmp (Atomic.comparator v_a) = a.(atm_cmp)
    /\
  (Atomic.value v_a) = a.(atm_val).

(* Lemma var_atomics_only_initial :
  forall var_atomics initial,
    forall x atomics,
      In (x, atomics) (smap.bindings (var_atomics_to_atomics var_atomics initial))
        ->
      (* Would be nice if we could use smap.In, but that one unfolds a bit strangely making it harder to work with *)
      exists initial_atoms, smap.MapsTo x initial_atoms initial.
Proof.
  induction var_atomics as [| v var_atomics IH].
  - intros initial x atomics.
    intros Hin. 
    apply In_to_InA_Duo_eq in Hin.
    rewrite smap.bindings_spec1 in Hin.
    simpl in Hin.
    exists atomics.
    exact Hin.
  - intros initial x atomics.
    simpl. intros Hin.
    unfold to_atomics_new_map in Hin.
    remember (var_name (Atomic.var v)) as name.
    destruct (smap.find name initial) as [atomics' |] eqn:Hfind.
    + rewrite smap.find_spec in Hfind.
      destruct (String.string_dec name x) as [Hxname|Hxname].
      * subst x.
        exists atomics'.
        apply Hfind.
      * apply IH in Hin.
        destruct Hin as [x_atoms Hx].
        rewrite <- smap.find_spec in Hx.
        rewrite smap.add_spec2 in Hx.
        -- rewrite smap.find_spec in Hx.
          exists x_atoms.
          exact Hx.
        -- exact Hxname.
    + apply IH in Hin. exact Hin.
Qed.
 *)
(* Definition find_default (x : string) (m : AtomicsMap) :=
  match smap.find x m with
  | Some atoms => atoms
  | None => nil
  end.
 *)
(* Lemma var_atomics_correct :
  forall var_atomics initial,
    forall x atomics,
      In (x, atomics) (smap.bindings (var_atomics_to_atomics var_atomics initial))
        ->
      forall a,
        In a atomics
          ->
        In a (find_default x initial)
          \/
        exists v_a,
          In v_a var_atomics
            /\
          var_atomic_equiv v_a a
            /\
          var_name (Atomic.var v_a) = x.
Proof.
  induction var_atomics as [| v var_atomics IH].
  - intros init x atomics. simpl.
    intros Hin. apply In_to_InA_Duo_eq in Hin.
    rewrite smap.bindings_spec1 in Hin.
    intros a Hinatom.
    left.
    rewrite <- smap.find_spec in *.
    unfold find_default. rewrite Hin.
    exact Hinatom.
  - intros initial x atomics Hin.
    intros a Hinatom.
    simpl in Hin.
    pose proof Hin as Hinit.
    apply var_atomics_only_initial in Hinit.
    destruct Hinit as (x_init & Hinit).
    apply IH with (a := a) in Hin.
    + destruct Hin as [Hprevadd | Hv].
      * unfold find_default in Hprevadd.
        destruct (x =? (var_name (Atomic.var v)))%string eqn:Hvx.
        {
          clear -Hvx Hprevadd Hinit. 
          rewrite String.eqb_eq in Hvx.
          unfold to_atomics_new_map in Hprevadd, Hinit.
          rewrite <- Hvx in *.
          unfold find_default.
          destruct (smap.find x initial) eqn:Hfind_init.
          2: { rewrite Hfind_init in Hprevadd. destruct Hprevadd. }
          rewrite smap.add_spec1 in Hprevadd.
          simpl in Hprevadd.
          destruct Hprevadd.
          - right. exists v.
            split; [|split] .
            + left. reflexivity.
            + unfold var_atomic_equiv.
              unfold var_atm_to_atm in H.
              inversion H. simpl.
              split; reflexivity.
            + symmetry. exact Hvx.
          - left. exact H.  
        }
        {
          clear -Hvx Hprevadd Hinit.
          unfold to_atomics_new_map in Hprevadd, Hinit.
          remember (var_name (Atomic.var v)) as v_name.
          rewrite String.eqb_neq in Hvx.
          unfold find_default.
          destruct (smap.find v_name initial).
          - rewrite <- smap.find_spec in Hinit.
            rewrite smap.add_spec2 in Hprevadd, Hinit;
            try (symmetry; assumption).
            rewrite Hinit in *.
            left. exact Hprevadd.
          - rewrite <- smap.find_spec in Hinit. rewrite Hinit in *.
            left. exact Hprevadd.
        }
      * clear -Hv.
        right.
        destruct Hv as (v' & Hin & Hequiv & Hname).
        exists v'.
        split; [|split].
        -- right. exact Hin.
        -- exact Hequiv.
        -- exact Hname.
    + exact Hinatom.
Qed.
 *)
Definition domain_holds (x : string) (dom : Domain) (sol : Assignment) :=
  forall v,
    var_name v = x
      ->
    is_in_dom (sol.(find_value) v) (Some dom).
 
Definition var_atomics_to_domains (l : list VarAtomic) (vs : option sstr.t) :=
  let atomics := var_atomics_to_atomics l in
  match domains_from_var_atomics_all atomics vs with
  | None => nil
  | Some doms => smap.bindings doms
  end.

Definition atoms_hold_for_var (atoms : list Atomic) (sol : Assignment) (v : Var) :=
  forall a,
    In a atoms ->
    atomic_holds (sol.(find_value) v) a.

Lemma var_atomics_to_atomics_hold :
  forall sol var_atomics,
 (forall a : Atomic.Atomic,
  In a var_atomics ->
  Atomic.test_atomic_assignment a sol = true)
    ->
  forall x v,
    var_name v = x
      ->
    atoms_hold_for_var (from_var_atoms x (var_atomics_to_atomics var_atomics)) sol v.
Proof.
  intros sol var_atomics Hhold.
  intros x v Hname.
  unfold atoms_hold_for_var. intros a Hin.
  unfold from_var_atoms in Hin.
  rewrite filter_pair_on_key_spec in Hin.
  unfold var_atomics_to_atomics in Hin.
  rewrite in_flat_map in Hin.
  destruct Hin as (v_a & Hinva & Hintoatoms).
  apply Hhold in Hinva; clear Hhold.
  unfold var_atomics_to_atoms in Hintoatoms.
  unfold var_atm_to_atm, var_to_atoms in Hintoatoms.
  destruct (Atomic.var v_a) as [a_var] eqn:Hvar.
  unfold var_cmp_to_cmp, mk_atm_ge, mk_atm_le in Hintoatoms.
  simpl in Hintoatoms; unfold atomic_holds.
  destruct Hintoatoms as [Hconv | [Hlb | [Hub | Hfalse]]].
  - inversion Hconv. subst x.
    assert (var_name (interval a_var) = name a_var) as Hvname.
    { simpl. reflexivity. }
    rewrite <- Hvname in H0.
    apply sol.(find_value_eq_name) in H0.
    repeat rewrite <- H0 in *.
    unfold Atomic.test_atomic_assignment in Hinva.
    unfold Atomic.test_atomic in Hinva.
    destruct (Atomic.comparator v_a); simpl;
    rewrite Hvar in *; lia.
  - inversion Hlb; subst; simpl in *.
    assert (var_name (interval a_var) = name a_var) as Hvname.
    { simpl. reflexivity. }
    rewrite <- Hvname in H0.
    apply sol.(find_value_eq_name) in H0.
    repeat rewrite <- H0 in *.
    specialize sol.(consistency_proof) with (v := interval a_var) as Hcons.
    unfold is_in in Hcons; apply Is_true_eq_true in Hcons.
    lia.
  - inversion Hub; subst; simpl in *.
    assert (var_name (interval a_var) = name a_var) as Hvname.
    { simpl. reflexivity. }
    rewrite <- Hvname in H0.
    apply sol.(find_value_eq_name) in H0.
    repeat rewrite <- H0 in *.
    specialize sol.(consistency_proof) with (v := interval a_var) as Hcons.
    unfold is_in in Hcons; apply Is_true_eq_true in Hcons.
    lia.
  - contradiction.
Qed.

(* Lemma vars_to_atoms_correct :
forall vs sol x atoms_from_var, smap.MapsTo x atoms_from_var (vars_to_atoms vs) ->
    exists v, In v vs /\ var_name v = x /\ atoms_hold_for_var atoms_from_var sol v.
Proof.
  intros vs sol x atoms_from_var.
  intros Hmap.
  apply build_map_maps_to in Hmap.
  destruct Hmap as (v & Hin & Hname & Hto_atoms).
  exists v.
  split; [|split].
  - exact Hin.
  - exact Hname.
  - unfold atoms_hold_for_var.
    unfold var_to_atoms in Hto_atoms.
    destruct v.
    rewrite <- Hto_atoms.
    intros a Hain.
    unfold atomic_holds.
    specialize sol.(consistency_proof) with (v := interval var) as Hsol.
    unfold is_in in Hsol.
    apply Is_true_eq_true in Hsol.
    destruct Hain as [Hlb | [Hub | Hnil]].
    + unfold mk_atm_ge in Hlb. rewrite <- Hlb. simpl.
      lia.
    + unfold mk_atm_le in Hub. rewrite <- Hub. simpl.
      lia.
    + destruct Hnil.
Qed.
 *)
Lemma to_domains_sound :
  forall sol var_atomics vs x dom,
  (forall a, In a var_atomics ->
    Atomic.test_atomic_assignment a sol = true)
    ->
  In (x, dom)
    (var_atomics_to_domains
      var_atomics
      (Some vs))
    ->
  sstr.In x vs
    /\
  forall v,
    var_name v = x
      ->
    is_in_dom (sol.(find_value) v) (Some dom).
Proof.
  intros sol var_atomics vs x dom.
  intros Hvar_atoms_hold.
  intros Hin.
  unfold var_atomics_to_domains in Hin.
  destruct domains_from_var_atomics_all as [doms|] eqn:Hdoms.
  - remember (var_atomics_to_atomics var_atomics) as atoms.
    specialize domains_from_var_atomics_all_correct with (vs := (Some vs)) (atoms := atoms) as Hdoms_spec.
    unfold domains_from_vars_P in Hdoms_spec.
    rewrite Hdoms in Hdoms_spec; clear Hdoms.
    specialize (Hdoms_spec x).
    rewrite In_to_InA_Duo_eq in Hin;
    rewrite smap.bindings_spec1 in Hin;
    rewrite <- smap.find_spec in Hin.
    rewrite Hin in Hdoms_spec.
    destruct Hdoms_spec as [Hcheck Hequiv].
    unfold check_in_vs in Hcheck.
    split.
    + rewrite <- sstr.mem_spec. apply Hcheck.
    + intros v Hname.
      apply var_atomics_to_atomics_hold with (v := v) (x := x) in Hvar_atoms_hold; try apply Hname.
      rewrite <- Heqatoms in *; clear Heqatoms.
      specialize (Hequiv (find_value sol v)).
      rewrite Hequiv.
      unfold applied_dom.
      rewrite dom_effect_atomics.
      split.
      * apply all_in_inital_dom.
      * apply Hvar_atoms_hold.
  - destruct Hin.
Qed.
(* 
  unfold atomics_to_domains in Hin.
  remember (smap.bindings
    (var_atomics_to_atomics
    var_atomics
    (vars_to_atoms vs))) as bindings.
  assert (map_valid to_domain_f bindings nil <> nil).
  { intros Hnil. rewrite Hnil in Hin. destruct Hin. }
  rewrite map_valid_as_map with (d := default_dom) in Hin.
  - rewrite app_nil_r in Hin. rewrite <- in_rev in Hin.
    rewrite in_map_iff in Hin.
    destruct Hin as ((x & atoms) & Hto_dom & Hin).
    subst bindings.
    apply map_valid_all_some with (a := (x, atoms)) in H; try assumption.
    unfold option_map_default in Hto_dom.
    destruct (to_domain_f (x, atoms)) eqn:Hdom; try contradiction; clear H; subst d.
    unfold to_domain_f in Hdom.
    destruct (apply_atomics atoms None None sint.empty) as [[[lb ub] holes]|] eqn:Happly; try discriminate Hdom.
    rename Hdom into Hdom_some; inversion Hdom_some as [Hdom]; clear Hdom_some.
    specialize (var_atomics_correct var_atomics (vars_to_atoms vs) x atoms Hin) as Hvar_atomics.
    apply var_atomics_only_initial in Hin.
    destruct Hin as (var_atoms & Hvar_atoms).
    assert (var_atoms = find_default x (vars_to_atoms vs)) as Hvar_atoms_find.
    { unfold find_default. rewrite <- smap.find_spec in Hvar_atoms. rewrite Hvar_atoms. reflexivity. }
    rewrite <- Hvar_atoms_find in Hvar_atomics; clear Hvar_atoms_find.
    apply vars_to_atoms_correct with (sol := sol) in Hvar_atoms.
    destruct Hvar_atoms as (v & Hinvs & Hname & Hvar_atoms).
    exists v.
    split; [|split].
    + exact Hinvs.
    + simpl. exact Hname.
    + unfold domain_holds.
      intros v'. simpl.
      intros Hvname'.
      assert (sol.(find_value) v' = sol.(find_value) v) as Hvv'.
      { apply sol.(find_value_eq_name). rewrite Hvname'. rewrite Hname. reflexivity. }
      rewrite Hvv'.
      apply apply_atomics_some with (atoms := atoms).
      * exact Happly.
      * subst x. clear -Hvar_atoms_hold Hvar_atomics Hvar_atoms.
        intros a Hin.
        apply Hvar_atomics in Hin; clear Hvar_atomics.
        destruct Hin as [Hin_var_atoms | Hex_atom].
        { unfold atoms_hold_for_var in Hvar_atoms. apply Hvar_atoms. exact Hin_var_atoms. }
        destruct Hex_atom as (v_a & Hin & Hequiv & Hname).
        apply Hvar_atoms_hold in Hin; clear Hvar_atoms_hold.
        unfold Atomic.test_atomic_assignment in Hin.
        unfold var_atomic_equiv in Hequiv.
        destruct Hequiv as (Hcmp & Hval).
        assert (find_value sol (Atomic.var v_a) = find_value sol v).
        { apply sol.(find_value_eq_name). exact Hname. }
        unfold var_cmp_to_cmp in Hcmp.
        unfold atomic_holds.
        unfold Atomic.test_atomic in Hin.
        destruct (Atomic.comparator v_a); rewrite <- Hcmp; lia.
  - intros Hnil. rewrite Hnil in Hin. destruct Hin.
Qed. *)
