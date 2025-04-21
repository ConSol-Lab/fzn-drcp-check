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

Record Domain := mkDom {
  d_lb : option Z;
  d_ub : option Z;
  holes : sint.t
}.

Definition DomainMap := smap.t Domain.

Definition check_in_vs (vs : option sstr.t) (x : string) :=
  match vs with
  | None => true
  | Some vs => sstr.mem x vs
  end.

Fixpoint fold_left_error {Acc X} (f : Acc -> X -> option Acc) (xl : list X) (acc : Acc) : option Acc :=
  match xl with
  | nil => Some acc
  | x :: xl' => 
    match f acc x with
    | None => None
    | Some acc => fold_left_error f xl' acc
    end
  end.

Definition fold_left_error_f {Acc X } (f : Acc -> X -> option Acc) (acc : option Acc) (x : X) :=
  match acc with
  | None => None
  | Some acc => f acc x
  end.

Lemma fold_left_error_as_fold_left :
  forall (Acc X : Type) (f : Acc -> X -> option Acc) xl acc,
    fold_left_error f xl acc = fold_left (fold_left_error_f f) xl (Some acc).
Proof.
  intros Acc X f. induction xl as [| x xl IH].
  - intros acc. simpl. reflexivity.
  - intros acc. simpl.
    destruct (f acc x) eqn:Hfx.
    + apply IH.
    + rewrite <- fold_left_rev_right. unfold fold_left_error_f. 
      clear. induction xl as [| x xl IH].
      * reflexivity.
      * simpl. rewrite fold_right_app. simpl.
        exact IH.
Qed.

Definition add_apply (vs : option sstr.t) (domains : DomainMap) (atom : (string * Atomic)) : option DomainMap :=
  match atom with
  | (x, atom) =>
    if check_in_vs vs x then
      let (bounds, holes) := 
        match smap.find x domains with
        | Some dom => (dom.(d_lb), dom.(d_ub), dom.(holes))
        | None => (None, None, sint.empty)
        end in
      let (lb, ub) := bounds in
      match apply_atomics (atom :: nil) lb ub holes with
      | None => None
      | Some (lb, ub, holes) => 
        let new_dom := mkDom lb ub holes in
        Some (smap.add x new_dom domains)
      end
    else Some domains
  end.

Definition domains_from_var_atomics (atoms : list (string * Atomic)) (vs : option sstr.t) :=
  fold_left_error (add_apply vs) atoms smap.empty.

Definition initial_dom := mkDom None None sint.empty.

Definition apply_atomics_dom (atoms : list Atomic) (dom : Domain) :=
  match apply_atomics atoms dom.(d_lb) dom.(d_ub) dom.(holes) with
  | None => None
  | Some (lb, ub, holes) => Some (mkDom lb ub holes)
  end.

Inductive Atomic_proof : list Atomic -> Domain -> Prop :=
  | atomic_proof_nil : Atomic_proof nil (mkDom None None sint.empty)
  | atomic_proof_app (atoms : list Atomic) (prev : list Atomic) (old_dom : Domain) (new_dom : Domain)
    (H1: Atomic_proof prev old_dom) (H2: apply_atomics_dom atoms old_dom = Some new_dom)
    : Atomic_proof (atoms ++ prev) new_dom.

Definition from_var_atoms (x : string) (atoms : list (string * Atomic)) : list Atomic :=
  flat_map_option (fun a => if (fst a =? x)%string then Some (snd a) else None) atoms.

Definition is_in_dom (y : Z) (dom : Domain) :=
    (match dom.(d_ub) with
    | Some ub => y <= ub
    | None => True
    end)
      /\
    (match dom.(d_lb) with
    | Some lb => lb <= y
    | None => True
    end)
      /\
    (~ sint.In y dom.(holes)).

Definition dom_equiv (dom1 : Domain) (dom2 : Domain) :=
  forall n, is_in_dom n dom1 <-> is_in_dom n dom2.




Lemma apply_atomics_dom_app :
  forall dom atoms,
  apply_atomics_dom (atoms ++ atoms') dom = 

Lemma apply_atomics_dom_perm :
  forall dom atoms1 atoms2 dom1 dom2,
    Permutation atoms1 atoms2
      ->
    apply_atomics_dom atoms1 dom = Some dom1
      ->
    apply_atomics_dom atoms2 dom = Some dom2
      ->
    dom_equiv dom1 dom2.
Proof.
  intros dom.
  induction atoms1 as [| a atoms1 IH].
  - intros atoms2 dom1 dom2.
    intros H.
    apply Permutation_nil in H.
    subst atoms2.
    intros H1 H2.
    rewrite H1 in H2. inversion H2.
    unfold dom_equiv. intros n.
    reflexivity.
  - intros atoms2 dom1 dom2.
    intros Hperm.
    inversion Hperm.
    + subst x; subst l; subst atoms2.
      unfold apply_atomics_dom.
      unfold apply_atomics.
      simpl.
      destruct (apply_atomic a (d_lb dom)
        (d_ub dom) (holes dom)) as [[[lb' ub'] holes']|] eqn:Ha.
      2: { intros H; discriminate H. }
      destruct (apply_atomics_rec atoms1 lb' ub' holes') eqn:Ha1.
      2: { intros H; discriminate H. }
Admitted.

      

Import Utility.ListInd.

Lemma domains_from_var_atomics_correct :
  forall vs x dom atoms dom_map,
    domains_from_var_atomics atoms vs = Some dom_map
      ->
    smap.MapsTo x dom dom_map
      ->
    match apply_atomics_dom (from_var_atoms x atoms) initial_dom with
    | None => False
    | Some dom' => dom_equiv dom dom'
    end.
Proof.
  intros vs x dom atoms.
  (* unfold domains_from_var_atomics.
  rewrite fold_left_error_as_fold_left.
  rewrite <- fold_left_rev_right.
  generalize dependent atoms. *)
  set (P := fun (atoms : list (string * Atomic)) (dom_map : option DomainMap) =>
    match dom_map with
    | Some dom_map =>
      smap.MapsTo x dom dom_map
        ->
      match apply_atomics_dom (from_var_atoms x atoms) initial_dom with
      | Some dom' => dom_equiv dom dom'
      | None => False
      end
    | None => True
    end
  ).
  enough (P (rev atoms) (domains_from_var_atomics atoms vs)).
  {
    unfold P in H; clear P. intros dom_map Hdom_map.
    rewrite Hdom_map in H. intros Hmap.
    apply H in Hmap; clear H.
    destruct (apply_atomics_dom (from_var_atoms x (rev atoms)) initial_dom) as [dom_rev|] eqn:Happly; try contradiction.


  }
  unfold domains_from_var_atomics.
  rewrite fold_left_error_as_fold_left.
  rewrite <- fold_left_rev_right.
  apply fold_ind.


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
