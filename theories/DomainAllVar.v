Require Import Coq.Logic.FinFun.
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
Require Import Checker.DomainAll.
Require Import Coq.Structures.Orders.
Require Coq.Structures.OrdersEx.
Require Coq.Structures.Equalities.

(* Module String_List_as_OT := OrdersEx.PairOrderedType OrdersEx.Z_as_OT OrdersEx.String_as_OT. *)


Definition VarAtomic := Atomic.Atomic.

Definition zn_interval := (Z * N)%type.

Definition a := OrdersEx.String_as_OT.eqb_eq.

Module StringKey_as_OT (A : Equalities.Typ) <: Orders.OrderedType.
  Module Base := OrdersEx.String_as_OT.

  Definition t := (string * A.t)%type.

  Definition eq (x y : t) := Base.eq (fst x) (fst y).

  Definition lt (x y : t) := Base.lt (fst x) (fst y).

  Lemma eq_equiv : RelationClasses.Equivalence eq.
  Proof. 
    unfold eq.
    constructor.
    - intros [s a]. simpl. reflexivity.
    - intros [s a] [s' a']. simpl. intros H.
      rewrite H. reflexivity.
    - intros [s a] [s' a'] [s'' a'']. simpl.
      intros H' H''.
      rewrite <- H''. exact H'.
  Qed.
  
  Definition eqb (x y : t) := Base.eqb (fst x) (fst y).
  Lemma eqb_eq : forall x y, eqb x y = true <-> eq x y.
  Proof. 
    intros [s a] [s' a']. unfold eqb; unfold eq.
    simpl. apply Base.eqb_eq.
  Qed.

  Include HasEqBool2Dec.

  #[global]
  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
    intros [sx ax] [sx' ax'] Hx [sy ay] [sy' ay'] Hy.
    unfold lt; unfold eq in *.
    simpl in *.
    apply Base.lt_compat; assumption.
  Qed.

  #[global]
  Instance lt_strorder : RelationClasses.StrictOrder lt.
  Proof.
    unfold lt. specialize Base.lt_strorder as H.
    destruct H as [Hirr Htrans].
    split.
    - intros [s a] H; simpl in H.
      apply Hirr in H. exact H.
    - intros [s a] [s' a'] [s'' a'']. simpl.
      apply Htrans.
  Qed.

  Definition compare (a b : t)
    := Base.compare (fst a) (fst b).

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
    intros [s a] [s' a'].
    unfold CompSpec.
    unfold compare; unfold eq; unfold lt. simpl.
    apply Base.compare_spec.
  Qed.

End StringKey_as_OT.

Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetGenTree.

Module Type HasNonEmpty (Import T:Equalities.Typ).
  Parameter d : t.
End HasNonEmpty.

Module Type NonEmpty := Equalities.Typ <+ HasNonEmpty.

Module MMapAVLMake (A : NonEmpty).
  Module Elements := StringKey_as_OT A.
  Include MSetAVL.Make Elements.

  Fixpoint find_rec (t : Raw.t) (x : Elements.t) :=
    match t with
    | Raw.Leaf => None
    | Raw.Node _ l k r =>
      match Elements.compare x k with
        | Lt => find_rec l x
        | Eq => Some (snd k)
        | Gt => find_rec r x
      end
    end.

  Definition find (s : t) (x : string) :=
    find_rec (this s) (x, A.d).

  (* Assumes a value already exists! *)
  Fixpoint replace_rec (t : Raw.t) (new : Elements.t) :=
    match t with
    | Raw.Leaf => Raw.Leaf
    | Raw.Node h l original r =>
      match Elements.compare new original with
        | Lt => replace_rec l new
        | Eq => Raw.Node h l new r
        | Gt => replace_rec r new
      end
    end.

  Definition replace_raw (new : Elements.t) (s : Raw.t) :=
    replace_rec s new.

  (* Definition replace (s : t) (key : string) (value : A.t) := *)
  (* Local Hint Immediate Raw.MX.eq_sym : core. *)
  (* Local Hint Unfold In Raw.lt_tree Raw.gt_tree Raw.Ok : core. *)
  (* Local Hint Constructors Raw.InT Raw.bst : core. *)
  (* Local Hint Resolve Raw.MX.eq_refl Raw.MX.eq_trans Raw.MX.lt_trans Raw.ok : core. *)
  (* Local Hint Resolve Raw.lt_leaf Raw.gt_leaf Raw.lt_tree_node Raw.gt_tree_node : core. *)
  (* Local Hint Resolve Raw.lt_tree_not_in Raw.lt_tree_trans Raw.gt_tree_not_in Raw.gt_tree_trans : core. *)
  (* Local Hint Resolve Raw.elements_spec2 : core. *)

  Lemma replace_ok : forall s x, Raw.Ok s -> Raw.Ok (replace_raw x s).
  Proof.
    unfold replace_raw; unfold replace_rec.
    Raw.induct s x; auto; unfold Raw.Ok.
    apply Raw.BSNode; auto.
    specialize Raw.lt_tree_compat as Hcompat.
    - apply Raw.lt_tree_compat in H0.
      specialize (H0 l l eq_refl).
      rewrite H0. exact H7.
    - apply Raw.gt_tree_compat in H0.
      specialize (H0 r r eq_refl).
      rewrite H0. exact H8.
  Qed.

  Definition replace (key : string) (value : A.t) (s : t) :=
    {| this := replace_raw (key, value) (this s) ; is_ok := replace_ok (this s) (key, value) (is_ok s) |}.

End MMapAVLMake.

Module ListAtomicTyp <: NonEmpty.
  Definition t : Type := list Atomic.
  Definition d : t := nil.
End ListAtomicTyp.


Module VarAtomicsMap := MMapAVLMake ListAtomicTyp.

Definition var_cmp_to_cmp (var_cmp : Atomic.AtomicComparator) : AtomicComparator :=
  match var_cmp with
  | Atomic.less_equal => less_equal
  | Atomic.greater_equal => greater_equal
  | Atomic.equal => equal
  | Atomic.not_equal => not_equal
  end.

Definition var_atm_to_atm (atm : VarAtomic) : Atomic :=
  {| atm_cmp := (var_cmp_to_cmp (Atomic.comparator atm)); atm_val := (Atomic.value atm) |}.

Fixpoint var_atomics_to_atomics (atomics : list VarAtomic) (m : VarAtomicsMap.t) :=
  match atomics with
  | nil => m
  | a :: atomics' =>
    let name := (var_name (Atomic.var a)) in
    let converted := var_atm_to_atm a in
    let updated_m := match VarAtomicsMap.find m name with
    | Some l => VarAtomicsMap.replace name (converted :: l) m
    | None => VarAtomicsMap.add (name, converted :: nil) m
    end in
    var_atomics_to_atomics atomics' updated_m
  end.