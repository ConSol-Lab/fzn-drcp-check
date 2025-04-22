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
  d_holes : sint.t
}.

Definition DomainMap := smap.t Domain.

Definition check_in_vs (vs : option sstr.t) (x : string) :=
  match vs with
  | None => true
  | Some vs => sstr.mem x vs
  end.

Definition initial_dom := mkDom None None sint.empty.

Definition apply_atomics_dom (atoms : list Atomic) (dom : Domain) :=
  match apply_atomics atoms dom.(d_lb) dom.(d_ub) dom.(d_holes) with
  | None => None
  | Some (lb, ub, holes) => Some (mkDom lb ub holes)
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
      match apply_atomics_dom (atom :: nil) dom with
      | None => None
      | Some new_dom => 
        Some (smap.add x new_dom domains)
      end
    else Some domains
  end.

Definition domains_from_var_atomics (atoms : list (string * Atomic)) (vs : option sstr.t) :=
  fold_left_error (add_apply vs) atoms smap.empty.


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
    (~ sint.In y dom.(d_holes)).

Definition dm_as_prod (d : option Domain) :=
  match d with
  | None => None
  | Some dom => Some (dom.(d_lb), dom.(d_ub), dom.(d_holes))
  end.

Definition domain_equiv (d1 d2 : option Domain) :=
  dom_equiv (dm_as_prod d1) (dm_as_prod d2).

Import Utility.ListInd.

Definition default_atom := mk_atm_le 0.

Lemma dom_permute_equiv :
  forall atoms atoms' dom,
    Permutation atoms atoms'
      ->
    domain_equiv (apply_atomics_dom atoms dom) (apply_atomics_dom atoms' dom).
Proof.
  intros atoms atoms' dom.
  intros Hpermute.
  unfold domain_equiv.
  unfold apply_atomics_dom.
  unfold dm_as_prod.
  destruct dom as [lb_in ub_in holes_in]. simpl.
  destruct (apply_atomics atoms lb_in ub_in holes_in) as [[[lb ub] holes]|] eqn:Hres;
  destruct (apply_atomics atoms' lb_in ub_in holes_in) as [[[lb' ub'] holes']|] eqn:Hres'; simpl;
  try reflexivity; try rewrite <- Hres; try rewrite <- Hres'; clear Hres Hres'; apply permute_apply_equiv;
  assumption.
Qed.

Ltac destruct_apply_atomics_rec_tuple :=
  repeat match goal with
  | |- context[apply_atomics_rec ?atoms ?lb ?ub ?holes] =>
      let result := fresh "result" in
      remember (apply_atomics_rec atoms lb ub holes) as result;
      destruct result as [ [[?lb_res ?ub_res] ?holes_res] | ]
  end.
  
Lemma apply_atomics_dom_cons_equiv :
  forall atoms atoms' dom,
    domain_equiv (apply_atomics_dom (atoms ++ atoms') dom) (
      match apply_atomics_dom atoms' dom with 
      | Some dom' => apply_atomics_dom atoms dom'
      | None => None
      end
    ).
Proof.
  intros atoms atoms' dom.
  unfold domain_equiv.
  unfold apply_atomics_dom.
  unfold apply_atomics.
  simpl.
  unfold dom_equiv.
  intros y.
  destruct (apply_atomics_rec
(atoms ++ atoms') (d_lb dom)
(d_ub dom) (d_holes dom)) as [[[lb ub] holes]|] eqn:Hres;
  try destruct (apply_holes lb ub
(holes_in_bounds holes lb ub)) as [[[lbh ubh] holesh]|] eqn:Hresh.
  

Lemma domains_from_var_atomics_correct :
  forall vs x atoms dom_map,
    check_in_vs vs x = true
      ->
    domains_from_var_atomics atoms vs = Some dom_map
      ->
    forall dom,
    smap.MapsTo x dom dom_map
      ->
    domain_equiv (apply_atomics_dom (from_var_atoms x atoms) initial_dom) (Some dom).
Proof.
  intros vs x atoms dom_map Hcheck.
  generalize dependent dom_map.
  (* unfold domains_from_var_atomics.
  rewrite fold_left_error_as_fold_left.
  rewrite <- fold_left_rev_right.
  generalize dependent atoms. *)
  set (P := fun (atoms : list (string * Atomic)) (dom_map : option DomainMap) =>
    forall dom,
    match dom_map with
    | Some dom_map =>
      smap.MapsTo x dom dom_map
        ->
      domain_equiv (apply_atomics_dom (from_var_atoms x atoms) initial_dom) (Some dom)
    | None => True
    end
  ).
  enough (P (rev atoms) (domains_from_var_atomics atoms vs)).
  {
    unfold P in H; clear P. intros dom_map Hdom_map.
    rewrite Hdom_map in H. intros dom Hmap.
    apply H in Hmap; clear H.
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
    rewrite <- H. apply Hmap.
  }
  unfold domains_from_var_atomics.
  rewrite fold_left_error_as_fold_left.
  rewrite <- fold_left_rev_right.
  apply fold_ind.
  - unfold P; clear P.
    intros Hmap.
    admit.
  - intros [x' a] dom_map s.
    unfold P; clear P.
    intros IH dom.
    destruct dom_map as [dom_map|].
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
