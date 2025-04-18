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

Definition AtomicsMap := smap.t (list Atomic).

Record Domain := {
  d_lb : option Z;
  d_ub : option Z;
  holes : sint.t
}.

Definition DomainMap := smap.t (list Domain).

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

Fixpoint fold_right_error {Acc X} (f : X -> Acc -> option Acc) (acc : Acc) (xl : list X) : option Acc :=
  match xl with
  | nil => Some acc
  | x :: xl' =>
    match fold_right_error f acc xl' with
    | None => None
    | Some rest => f x rest
    end
  end.

Lemma fold_right_app_error : forall (A B:Type)(f:A->B->option B) l l' i,
    fold_right_error f i (l++l')
      =
    match fold_right_error f i l' with
    | None => None 
    | Some fl' => fold_right_error f fl' l
    end.
  Proof.
    intros A B f l; induction l.
    - intros l' i. simpl. remember (fold_right_error f i l') as fl'. destruct fl'; reflexivity.
    - intros l' i. simpl.
      rewrite IHl.
      remember (fold_right_error f i l') as fl'.
      destruct fl'; reflexivity.
  Qed.

Lemma fold_left_rev_right_right : forall (Acc X : Type)(f : X -> Acc -> option Acc) xl acc,
    fold_right_error f acc (rev xl) = fold_left_error (fun acc x => f x acc) xl acc.
Proof.
  intros Acc X f.
  induction xl as [| x xl].
  - intros acc. simpl. reflexivity.
  - intros acc. simpl. 
    rewrite fold_right_app_error. simpl. 
    destruct (f x acc) eqn:Hfx; easy.
Qed.

Definition add_apply (vs : option sstr.t) (atom : (string * Atomic)) (acc : DomainMap) :=
  match atom with
  | (x, atom) =>
    if check_in_vs then
      let (bounds, holes) := 
        match smap.find x domains with
        | Some dom => (dom.(d_lb), dom.(d_ub), dom.(holes))
        | None => (None, None, sint.empty)
        end in
      let (lb, ub) := bounds in
      match apply_atomics (a :: nil) lb ub holes with
      | None => None
      | Some (lb, ub, holes) => 
        let new_dom := mkDom x lb ub holes in
        Some (smap.add x new_dom domains)
      end


Definition domains_from_var_atomics (atoms : list (string * Atomic)) (vs : option sstr.t) :=
  fold_left ()


