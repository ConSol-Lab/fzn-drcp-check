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

(* This file serves as an interface between the old variables and atomics and the new ones so that the cumulative checker can work. *)

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

(* Note that this means that we add the variable atoms more than once, so not as efficient, but for this version it should be fine. *)
Definition var_atomics_to_atomics (atomics : list VarAtomic) : list BoundAtomic :=
  flat_map var_atomics_to_atoms atomics.


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