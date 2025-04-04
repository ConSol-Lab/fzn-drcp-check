Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Checker.Atomic.
Require Import Checker.Variable.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.

Require Coq.MSets.MSetAVL.
Require Coq.MSets.MSetProperties.
Require Coq.Structures.OrdersEx.

(* ################################### *)
(* ####### MSet instantiations ####### *)

Module sstr := MSetAVL.Make OrdersEx.String_as_OT.
Module sint := MSetAVL.Make OrdersEx.Z_as_OT.
Module Z_String_as_OT := OrdersEx.PairOrderedType OrdersEx.Z_as_OT OrdersEx.String_as_OT.
Module sintstr := MSetAVL.Make Z_String_as_OT.
Module sstr_prps := MSetProperties.Properties sstr.
Module sint_prps := MSetProperties.Properties sint.
Module sintstr_prps := MSetProperties.Properties sintstr.

(* the integer is the lower bound, upper bond is lb + the N *)

Definition zn_interval := (Z * N)%type.

Definition interval_to_bounds (i : zn_interval) : (Z * Z)%type :=
  let (lb, size) := i in
    (lb, lb + (Z.of_N size)).

Definition bounds_to_interval (lb : Z) (ub : Z) : option zn_interval :=
  if ub <? lb
    then None
    else Some (lb, Z.to_N (ub - lb)).

Definition update_interval_w_atomic (i : zn_interval) (a : AtomicComparator) (x : Z) : option zn_interval :=
  match interval_to_bounds i with
  | (lb, ub) =>
    match a with 
    | less_equal => 
      if x <? ub
        then bounds_to_interval lb x
        else Some i
    | greater_equal => 
      if x >? lb
        then bounds_to_interval x ub
        else Some i
    | not_equal =>
      if x =? lb
        then bounds_to_interval (lb + 1) ub
        else if x =? ub
          then bounds_to_interval lb (ub - 1)
          else Some i
    | equal =>
      if x <? lb
        then None
        else if x >? ub
          then None
          else Some (x, 0%N)
    end
  end.

Definition variables_to_intervals (vars : list Var) : list (string * zn_interval) :=
  map (fun v =>
    match v with
    | interval v =>
      (v.(name), (v.(lower_bound), N.of_nat v.(size)))
    end
  ) vars.

Definition atom_matches_name_and_apply (a : Atomic) (name : string) (i : zn_interval) :=
  if (var_name a.(var) =? name)%string
  then (true, update_interval_w_atomic i a.(comparator) a.(value))
  else (false, None).



Fixpoint apply_atomics {U} (interval : string * zn_interval * U) (atoms : list Atomic) (applied : list Atomic) : option (list Atomic * string * zn_interval * U) :=
  match interval with
  | (i_var_name, i, u) =>
    match atoms with
    | nil => Some (applied, i_var_name, i, u)
    | a :: atoms' =>
      match atom_matches_name_and_apply a i_var_name i with
      | (true, Some i_new) => apply_atomics (i_var_name, i_new, u) atoms' (a :: applied)
      | (true, None) => None
      | (false, _) => apply_atomics interval atoms' applied
      end
    end
  end
.

Inductive Atomic_proof (x : string) (i_init : zn_interval) : list Atomic -> zn_interval -> Prop :=
  | atomic_proof_nil : Atomic_proof x i_init nil i_init
  | atomic_proof_a (a : Atomic) (al' : list Atomic) (old_i : zn_interval) (new_i : zn_interval)
    (H1: Atomic_proof x i_init al' old_i) (H2: atom_matches_name_and_apply a x old_i = (true, Some new_i))
    : Atomic_proof x i_init (a :: al') new_i
  .

(* Here we use a trick we also used for res_sum, we return also everything we've seen, this allows us to make the induction proof much easier! *)
Lemma apply_atomics_has_proof_rec (U : Type) :
  forall x (u : U) i_init,
    forall atoms i_before applied_before out,
    Atomic_proof x i_init applied_before i_before
      ->
    apply_atomics (x, i_before, u) atoms applied_before = Some out
      ->
    match out with
    | (applied, x', (lb_result, size_result), u') => 
      x' = x /\ u' = u /\
    (forall atom, In atom applied -> In atom atoms \/ In atom applied_before)
      /\
    Atomic_proof x i_init applied (lb_result, size_result) 
    end.
Proof.
  intros x u i_init.
  induction atoms.
  - intros i_before applied_before out Hbefore Happly.
    destruct out as [[[applied x'] [lb_init size_init]] u'].
    simpl in Happly.
    inversion Happly. subst applied; subst x'; subst i_before; subst u'; clear Happly.
    repeat split.
    + intros atom Hin. right. exact Hin.
    + exact Hbefore.
  - intros i_before applied_before out Hbefore Happly.
    destruct out as [[[applied x'] i_out] u'].
    simpl in Happly.
    destruct (atom_matches_name_and_apply a x i_before) as [name_match i_applied_a] eqn:Hmatch.
    destruct name_match eqn:Hname.
    + destruct i_applied_a as [i_applied_a | ].
      2: discriminate Happly.
      assert (Atomic_proof x i_init (a :: applied_before) i_applied_a) as Happlied.
      {
       clear IHatoms. apply atomic_proof_a with (old_i := i_before).
       - exact Hbefore.
       - exact Hmatch.
      } 
      remember (applied, x', i_out, u') as out.
      specialize (IHatoms i_applied_a (a :: applied_before) out Happlied Happly); clear Happly; clear Happlied.
      rewrite Heqout in *.
      destruct i_out as [lb_result size_result].
      destruct IHatoms as [Hxx' [Huu' [IHatoms IHproof]]].
      subst x'; subst u'.
      repeat split.
      * intros atom' Hin.
        destruct (IHatoms atom' Hin) as [Hinatoms |Hinbefore]; clear IHatoms.
        -- left. simpl. right. exact Hinatoms.
        -- destruct Hinbefore as [Haatom' | Hinbefore].
          ++ subst atom'. left. simpl. left. reflexivity.
          ++ right. exact Hinbefore.
      * exact IHproof.
    + remember (applied, x', i_out, u') as out.
      specialize (IHatoms i_before applied_before out  Hbefore Happly).
      rewrite Heqout in *.
      destruct i_out as [lb_result size_result].
      destruct IHatoms as [Hxx' [Huu' IHatoms]].
      subst x'; subst u'.
      repeat split.
      * intros atom_in_applied Hin.
        apply IHatoms in Hin.
        destruct Hin as [Hinatoms | Hinbefore].
        -- left. simpl. right. exact Hinatoms.
        -- right. exact Hinbefore.
      * apply IHatoms.
Qed.

Lemma apply_atomics_has_proof (U : Type) :
  forall x (u : U) i_init atoms out,
    apply_atomics (x, i_init, u) atoms nil = Some out
      ->
    match out with
    | (applied, x', (lb_result, size_result), u') => 
      x' = x /\ u' = u /\
    (forall atom, In atom applied -> In atom atoms)
      /\
    Atomic_proof x i_init applied (lb_result, size_result) 
    end.
Proof.
  intros x u i_init atoms out Hsome.
  specialize (apply_atomics_has_proof_rec U x u i_init atoms i_init nil out) as H.
  destruct out as [[[applied x'] [lb_out size_out]] u'].
  assert (Atomic_proof x i_init nil i_init) as Hproof_init by (apply atomic_proof_nil).
  apply H in Hproof_init; try assumption; clear H.
  destruct Hproof_init as [Hxx' [Huu' [IHatoms IHproof]]].
  repeat split; try assumption.
  intros atom' Hin.
  specialize (IHatoms atom' Hin).
  destruct IHatoms; easy.
Qed.

Lemma atomic_proof_rec_correct :
  forall x lb_init size_init sol atoms_all,
  (forall atomic, In atomic atoms_all ->
  Is_true (test_atomic_assignment atomic sol))
    ->
  forall atoms i,
  (forall a, In a atoms -> In a atoms_all)
    ->
  Atomic_proof x (lb_init, size_init) atoms i
    ->
  match i with
  | (lb, i_size) =>
    forall v,
    v.(name) = x
      ->
    v.(lower_bound) = lb_init
      ->
    N.of_nat v.(size) = size_init
      ->
    lb <= sol.(find_value) (interval v) <= lb + Z.of_N i_size
  end.
Proof.
  intros x lb_init size_init sol atoms_all Hatoms. 
  induction atoms.
  - intros i Hatomin Hatom.
    destruct i as [lb size].
    intros v Hname Hinit Hsize_init.
    subst x; subst lb_init; subst size_init.
    inversion Hatom. subst lb; subst size.
    specialize (sol.(consistency_proof) (interval v)) as Hcons.
    apply Is_true_eq_true in Hcons.
    unfold is_in in Hcons. apply andb_true_iff in Hcons.
    repeat rewrite Z.leb_le in Hcons.
    unfold upper_bound in Hcons.
    rewrite nat_N_Z. exact Hcons.
  - intros i Hatomin Hatom.
    destruct i as [lb size].
    inversion Hatom.
    subst a0; subst al'; subst new_i.
    clear Hatom.
    specialize (IHatoms old_i).
    destruct old_i as [old_lb old_size].
    assert (forall a : Atomic, In a atoms -> In a atoms_all) as Hinold.
    {
     intros a' Hina'.
     apply Hatomin.
     simpl. right. exact Hina'.  
    }
    intros v Hname Hlb_init Hsize_init.
    subst x; subst lb_init; subst size_init.
    apply IHatoms with (v := v) in Hinold; try easy; clear IHatoms; clear H3.
    specialize (Hatoms a).
    assert (In a atoms_all) as Haholds.
    {
      apply Hatomin. simpl. left. reflexivity.
    }
    apply Hatoms in Haholds; clear Hatoms; clear Hatomin.
    apply Is_true_eq_true in Haholds.
    unfold atom_matches_name_and_apply in H4.
    destruct (var_name (var a) =? name v)%string eqn:Hvareq; inversion H4; clear H4.
    rewrite String.eqb_eq in Hvareq.
    specialize sol.(find_value_eq_name) as Hname_eq1.
    assert (var_name (var a) = var_name (interval v)) as Hname_eq.
    { apply Hvareq. }
    apply Hname_eq1 in Hname_eq; clear Hname_eq1; clear Hvareq.
    unfold test_atomic_assignment in Haholds.
    rewrite Hname_eq in Haholds; clear Hname_eq.
    unfold test_atomic in Haholds.
    unfold update_interval_w_atomic in H0.
    destruct (interval_to_bounds (old_lb, old_size)) as [old_lb' ub] eqn:Hbound.
    unfold interval_to_bounds in Hbound. inversion Hbound. subst old_lb'; clear Hbound.
    destruct (comparator a).
    + destruct (value a <? ub).
      * unfold bounds_to_interval in H0. destruct (value a <? old_lb); inversion H0.
        lia.
      * inversion H0. subst old_lb; subst old_size.
        exact Hinold.
    + destruct (value a >? old_lb).
      * unfold bounds_to_interval in H0. destruct (ub <? value a); inversion H0.
        lia.
      * inversion H0. subst old_lb; subst old_size.
        lia.
    + destruct (value a =? old_lb) eqn:Hvallb.
      * unfold bounds_to_interval in H0. destruct (ub <? old_lb + 1); inversion H0.
        rewrite Z.eqb_eq in Hvallb. rewrite Hvallb in Haholds.
        lia.
      * destruct (value a =? ub) eqn:Hvalub. 
        -- unfold bounds_to_interval in H0.
          destruct (ub - 1 <? old_lb); inversion H0.
          lia.
        -- inversion H0. subst lb; subst size. lia.
    + destruct (value a <? old_lb); try discriminate H0.
      destruct (value a >? ub); inversion H0.
      subst size; subst lb; subst ub.
      lia.
Qed.
      
Lemma atomic_proof_correct :
  forall atoms sol,
  (forall atomic, In atomic atoms ->
  Is_true (test_atomic_assignment atomic sol))
    ->
  forall x lb_init size_init lb i_size,
  Atomic_proof x (lb_init, size_init) atoms (lb, i_size)
    ->
    forall v,
    v.(name) = x
      ->
    v.(lower_bound) = lb_init
      ->
    N.of_nat v.(size) = size_init
      ->
    lb <= sol.(find_value) (interval v) <= lb + Z.of_N i_size.
Proof.
  intros atoms sol Hholds x lb_init size_init lb i_size.
  remember (lb, i_size) as i.
  specialize (atomic_proof_rec_correct x lb_init size_init sol atoms Hholds atoms i) as Hcorrect.
  destruct i as [lb' i_size'].
  inversion Heqi. subst lb'; subst i_size'.
  apply Hcorrect.
  intros a H. assumption.
Qed.

Fixpoint apply_atomics_to_variables {U} (is : list (string * zn_interval * U)) (atoms : list Atomic) :=
  match is with
  | nil => Some nil
  | i :: is' => 
    match apply_atomics i atoms nil with
    | None => None
    | Some (_, x, i, u) => 
      match apply_atomics_to_variables is' atoms with
      | None => None
      | Some rest => Some ((x, i, u) :: rest)
      end
    end
  end.

Definition bound_name {U} (bound : string * zn_interval * U) :=
  match bound with
  | (x, _, _) => x
  end.

Definition unique_bounds {U} (bounds : list (string * zn_interval * U)) :=
  NoDup bounds
    /\
  forall a1 a2,
    In a1 bounds -> In a2 bounds
    -> bound_name a1 = bound_name a2
    -> a1 = a2. 

Lemma a_u_dec (U : Type) (u_dec : forall x y : U, {x = y}+{x <> y}) :
  forall x y : string * zn_interval * U, {x = y}+{x <> y}.
Proof.
  repeat decide equality.
Qed.

Lemma unique_bounds_cons (U : Type) :
  forall (a : string * zn_interval * U) bounds,
    unique_bounds (a :: bounds)
      ->
    forall a',
      In a' bounds
        ->
      bound_name a <> bound_name a'.
Proof.
  intros a bounds.
  intros Hunique.
  intros a'. intros Hin.
  unfold not. intros Hname.
  apply Hunique in Hname.
  - subst a'.
    unfold unique_bounds in Hunique.
    destruct Hunique as [Hnodup _].
    rewrite NoDup_cons_iff in Hnodup.
    destruct Hnodup as [Hnotinbounds _].
    contradiction.
  - left. reflexivity.
  - right. exact Hin.
Qed.

Lemma unique_bounds_less (U : Type) :
  forall (a : string * zn_interval * U) bounds,
    unique_bounds (a :: bounds)
      ->
    unique_bounds bounds.
Proof.
  intros a bounds.
  intros Hunique.
  unfold unique_bounds in Hunique.
  unfold unique_bounds.
  destruct Hunique as [Hnodup Hunique].
  split.
  - rewrite NoDup_cons_iff in Hnodup. apply Hnodup.
  - intros a1 a2 Hin1 Hin2 Hname.
    apply Hunique.
    + right. exact Hin1.
    + right. exact Hin2.
    + exact Hname.
Qed.

Lemma apply_atomics_correct (U : Type) :
  forall (is : list (string * zn_interval * U)) atoms bounds,
  apply_atomics_to_variables is atoms = Some bounds 
    ->
  (forall a, In a bounds ->
    match a with
    | (x, (lb, a_size), u) =>
      exists lb_init size_init, In (x, (lb_init, size_init), u) is
        /\
      exists atoms_applied, 
      (forall atom, In atom atoms_applied -> In atom atoms) /\
      Atomic_proof x (lb_init, size_init) atoms_applied (lb, a_size)
    end
  ).
Proof.
  induction is as [| i is].
  - intros atoms bounds Hsome.
    unfold apply_atomics_to_variables in Hsome.
    inversion Hsome.
    intros a Hinnil.
    destruct Hinnil.
  - intros atoms bounds Hsome.
    intros a Hin.
    simpl in Hsome.
    destruct a as [[x [lb a_size]] u] eqn:Ha.
    destruct i as [[i_x i_i] u_i].
    specialize (apply_atomics_has_proof U i_x u_i i_i atoms) as Hproof'.
    destruct (apply_atomics (i_x, i_i, u_i) atoms nil) as [i_out |] eqn:Happly.
    2: discriminate Hsome.
    specialize (Hproof' i_out).
    assert (Some i_out = Some i_out) as Hproof by reflexivity.
    apply Hproof' in Hproof; clear Hproof'.
    destruct i_out as [[[i_applied i_x'] [i_lb i_size]] u_i'].
    destruct Hproof as [H1 [H2 [Hiatoms Hproof]]].
    subst i_x'; subst u_i'.
    destruct (apply_atomics_to_variables is atoms) as [rest | ] eqn:Hrest.
    2: discriminate Hsome.
    inversion Hsome; clear Hsome. subst bounds.
    destruct Hin as [Hix | Hin].
    + inversion Hix. subst x; subst lb; subst a_size; subst u; clear Hix.
      destruct i_i as [i_lb_init i_size_init].
      exists i_lb_init. exists i_size_init.
      split.
      * simpl. left. reflexivity.
      * exists i_applied. split.
        -- exact Hiatoms.
        -- exact Hproof.
    + rewrite <- Ha in Hin.
      specialize (IHis atoms rest Hrest a Hin).
      rewrite Ha in IHis; subst a.
      destruct IHis as [lb_init [size_init [Hinis [atoms_applied [Hatoms_applied_in Hatoms_applied_proof]]]]].
      exists lb_init; exists size_init.
      split.
      * simpl. right. exact Hinis.
      * exists atoms_applied. split.
        -- exact Hatoms_applied_in.
        -- exact Hatoms_applied_proof.
Qed.


Lemma apply_atomics_unique :
  forall (U : Type) (u_dec : forall x y : U, {x = y}+{x <> y}) (is : list (string * zn_interval * U)) atoms bounds,
  unique_bounds is
    ->
  apply_atomics_to_variables is atoms = Some bounds 
    ->
  unique_bounds bounds.
Proof.
  intros U.
  induction is. 
  - intros atoms bounds Hnil.
    intros Happly.
    unfold apply_atomics_to_variables in Happly. inversion Happly.
    apply Hnil.
  - intros atoms bounds.
    intros Hunique.
    intros Happly.
    simpl in Happly.
    destruct (apply_atomics_to_variables is atoms) as [is_result |] eqn:Happlyis.
    + assert (forall a_x a_i a_u, 
        In (a_x, a_i, a_u) is_result -> exists a_i_pre, In (a_x, a_i_pre, a_u) is) as Hpre.
      {
        intros a_x a_i a_u Hin.
        destruct a_i as [a_lb a_size].
        specialize (apply_atomics_correct U is atoms is_result Happlyis (a_x, (a_lb, a_size), a_u) Hin) as Hatomics.
        destruct Hatomics as [lb_i [size_i [Hin_is _]]].
        exists (lb_i, size_i). exact Hin_is.
      }
      destruct (apply_atomics a atoms nil) as [[[[a_applied x] a_i] a_u] |] eqn:Haapply.
      * inversion Happly.
        subst bounds; clear Happly.
        apply unique_bounds_less in Hunique as H.
        apply IHis with (atoms := atoms) (bounds := is_result) in H.
        2: { exact Happlyis. }
        clear IHis.
        unfold unique_bounds.
        split.
        {
     
          apply NoDup_cons_iff.
          split.
          - specialize (unique_bounds_cons U a is Hunique) as Hnames.
            destruct a as [[x' a_i_pre] a_u'].
            apply apply_atomics_has_proof in Haapply as Haout.
            destruct a_i.
            destruct Haout as [Hxx' [Huu' _]].
            subst x'; subst a_u'.
            unfold not. intros Hin_is.
            remember (z, n) as a_i.
            apply Hpre in Hin_is as Hpre_a; clear Hpre.
            destruct Hpre_a as [a_i_pre' Hpre_a].
            apply Hnames in Hpre_a.
            simpl in Hpre_a.
            contradiction. 
          - apply H.
        }
        {
          intros a1 a2.
          intros Hin1 Hin2 Hname.
          remember (x, a_i, a_u) as a_out.
          destruct (a_u_dec U u_dec a1 a_out) as [Ha1a | Ha1na];
          destruct (a_u_dec U u_dec a2 a_out) as [Ha2a | Ha2na].
          - subst a1; subst a2. reflexivity.
          - subst a1.
            destruct Hin2 as [Ha2out | Hin2]; try easy.
            clear Hin1. exfalso.
            specialize (unique_bounds_cons U a is Hunique) as Hnames.
            + destruct a2 as [[a2_x a2_i] a2_u].
              apply Hpre in Hin2 as Hin2pre.
              destruct Hin2pre as [a2_i_pre Hin2pre].
              apply Hnames in Hin2pre.
              simpl in Hname, Hin2pre.
              assert (bound_name a = bound_name a_out) as Hnamesa.
              {
                destruct a as [[x' a_i_pre] a_u'].
                apply apply_atomics_has_proof in Haapply as Haout.
                destruct a_i.
                destruct Haout as [Hx]; subst x'; rewrite Heqa_out.
                simpl. reflexivity.
              }
              rewrite Hname in Hnamesa.
              contradiction.
          - subst a2.
            destruct Hin1 as [Ha1out | Hin1]; try easy.
            clear Hin2. exfalso.
            specialize (unique_bounds_cons U a is Hunique) as Hnames.
            + destruct a1 as [[a1_x a1_i] a1_u].
              apply Hpre in Hin1 as Hin1pre.
              destruct Hin1pre as [a1_i_pre Hin1pre].
              apply Hnames in Hin1pre.
              simpl in Hname, Hin1pre.
              assert (bound_name a = bound_name a_out) as Hnamesa.
              {
                destruct a as [[x' a_i_pre] a_u'].
                apply apply_atomics_has_proof in Haapply as Haout.
                destruct a_i.
                destruct Haout as [Hx]; subst x'; rewrite Heqa_out.
                simpl. reflexivity.
              }
              rewrite <- Hname in Hnamesa.
              contradiction.
          - destruct Hin1 as [Ha1out | Hin1].
            { symmetry in Ha1out. contradiction. }
            destruct Hin2 as [Ha2out | Hin2].
            { symmetry in Ha2out. contradiction. }
            apply H.
            + exact Hin1.
            + exact Hin2.
            + exact Hname.
        }
      * discriminate Happly.
    + destruct (apply_atomics a atoms nil) as [[[[a_applied x] a_i] a_u] |] eqn:Haapply.
      * discriminate Happly.
      * discriminate Happly.
Qed.

(* 


Definition hole_domain := (option Z * option Z * sint.t)%type.

Definition consistent_hole_domain (d : hole_domain) :=
  match d with
  | (lb, ub, holes) =>
    match lb with
    | Some lb => forall n, sint.In n holes -> n > lb
      /\
      match ub with
      | Some ub => lb <= ub
      | None => True
      end
    | None => True
    end
      /\
    match ub with
    | Some ub => forall n, sint.In n holes -> n < ub
    | None => True
    end
  end.

Definition val_in_hole_domain (y : Z) (d : hole_domain) :=
  match d with
  | (lb, ub, holes) =>
    ~ sint.In y holes 
      /\
    match lb with
    | Some lb => y >= lb
    | None => True
    end
      /\
    match ub with
    | Some ub => y <= ub
    | None => True
    end
  end.

Definition fixed_to_list := sint.t.

Definition lt_ub (x : Z) (ub : option Z) :=
  match ub with
  | Some ub => x <? ub
  | None => true
  end.

Definition gt_lb (x : Z) (lb : option Z) :=
  match lb with
  | Some lb => x >? lb
  | None => true
  end.

Definition update_hole_domain_w_atomic (d : hole_domain * fixed_to_list) (a : AtomicComparator) (x : Z) : (hole_domain * fixed_to_list) :=
  match d with
  | ((lb, ub, holes), fixed) =>
    match a with 
    | less_equal => 
      if lt_ub x ub
        then ((lb, Some x, holes), fixed)
        else d
    | greater_equal => 
      if gt_lb x lb
        then ((Some x, ub, holes), fixed)
        else d
    | not_equal =>
      ((lb, ub, sint.add x holes), fixed)
    | equal => ((lb, ub, holes), sint.add x fixed)
    end
  end.

Definition atom_match_name_update_hole_dom (a : Atomic) (name : string) (d : hole_domain * fixed_to_list) : option (hole_domain * fixed_to_list) :=
  if (var_name a.(var) =? name)%string
  then Some (update_hole_domain_w_atomic d a.(comparator) a.(value))
  else None.

Fixpoint apply_atomics_dom (x : string) (d : hole_domain * fixed_to_list) (atoms : list Atomic) (applied : list Atomic) : (list Atomic * (hole_domain * fixed_to_list)) :=
  match atoms with
  | nil => (applied, d)
  | a :: atoms' =>
    match atom_match_name_update_hole_dom a x d with
    | Some d_new => apply_atomics_dom x d_new atoms' (a :: applied)
    | None => apply_atomics_dom x d atoms' applied
    end
  end
.

Definition atom_is (x : string) (val : Z) (a : Atomic) (cmp : AtomicComparator) :=
  (var_name a.(var)) = x
    /\
  a.(comparator) = cmp
    /\
  a.(value) = val.

Definition has_atoms (x : string) (atoms : list Atomic) (d : hole_domain * fixed_to_list) :=
match d with
| ((lb, ub, holes), fixed) =>
  match lb with
  | Some lb => exists (a : Atomic),
    (In a atoms)
      /\
    atom_is x lb a greater_equal
  | None => True
  end
    /\
  match ub with
  | Some ub => exists (a : Atomic),
    (In a atoms)
      /\
    atom_is x ub a less_equal
  | None => True
  end
    /\
  (forall n, sint.In n holes ->
    exists (a : Atomic),
    (In a atoms)
      /\
    atom_is x n a not_equal)
    /\
  (forall n, sint.In n fixed ->
    exists (a : Atomic),
    (In a atoms)
      /\
    atom_is x n a equal)
end.

Lemma apply_dom_correct :
  forall x atoms d applied_before applied d_out,
    has_atoms x applied_before d ->
    apply_atomics_dom x d atoms applied_before = (applied, d_out) ->
    has_atoms x (atoms ++ applied_before) d_out.
Proof.
  intros x. induction atoms.
  - intros d applied_before applied d_out.
    intros Hbefore.
    intros Hres. simpl in Hres.
    inversion Hres.
    subst applied_before; subst d_out; clear Hres.
    destruct d as [d fixed].
    destruct d as [[lb ub] holes]. simpl.
    unfold has_atoms in Hbefore.
    destruct Hbefore as [Hlb [Hub [Hholes Hfixed]]].
    repeat split.
    + destruct lb; try reflexivity.
      exact Hlb.
    + destruct ub; try reflexivity.
    exact Hub.
    + exact Hholes.
    + exact Hfixed.
  - intros d applied_before applied d_out.
    intros Hbefore Hres.
    simpl in Hres.
    destruct (atom_match_name_update_hole_dom a x d) eqn:Hupdatesome.
    {
      unfold atom_match_name_update_hole_dom in Hupdatesome.
      destruct (var_name (var a) =? x)%string.
      2: discriminate Hupdatesome.
      inversion Hupdatesome as [Hupdate]; clear Hupdatesome.
      unfold update_hole_domain_w_atomic in Hupdate.
      destruct d as [[[lbb ubb] holesb] fixedb].
      destruct (comparator a) eqn:Hcomp.
      - destruct (lt_ub (value a) ubb).
        + subst p.
          unfold has_atoms.
          destruct d_out as [[[lb ub] holes] fixed].
          repeat split.
          * destruct lb; try reflexivity.
            specialize (IHatoms (lbb, ubb, holesb, fixedb) applied_before )


      unfold has_atoms.
     
     repeat split.
     - destruct lb; try reflexivity.

    } *)
