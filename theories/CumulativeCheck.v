
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Arith.PeanoNat.
Require Import Bool.
Require Import String.
Require Import Checker.Nogood.
Require Import Checker.Cumulative.
Require Checker.CumulativeUtil.
Import CumulativeUtil.ResourceSum.
Require Import Checker.Utility.
Import ListEx.
Require Import Lia.
Require Import Checker.Atomic.
Require Import Checker.Variable.
Require Checker.Utility.
Require Import Checker.Domain.

Open Scope N_scope.

Theorem res_sum_semantics :
  forall c l,
    match res_sum c l with
    | (_, sum_result, true) =>
      xn_sum l = sum_result  
        /\     
        xn_sum l <= c
    | (summed, sum_result, false) =>
    xn_sum summed = sum_result
        /\
        xn_sum summed > c
        /\
      sub_list xn_eq_dec summed l
        /\
        xn_sum l > c
    end.
Proof.
  intros c l.
  specialize (res_sum_correct c l) as H.
  destruct (res_sum c l) as [[summed sum_result] b].
  destruct b.
  - destruct H as [Hsum_result [Hin [Hle Husage]]].
    split.
    + exact Husage.
    + rewrite Husage. exact Hle.
  - destruct H as [Hsum_result [Hin Hgt]].
    assert (sub_list xn_eq_dec summed l) as Hsub.
    {
      unfold sub_list.
      intros a Hinsummed.
      apply Hin. exact Hinsummed.
    }
    repeat split.
    + rewrite Hsum_result. reflexivity.
    + rewrite Hsum_result. exact Hgt.
    + exact Hsub. 
    + specialize (xn_sum_sub_list summed l Hsub) as Husagelt.
      repeat rewrite usage_sum_add in *.
      rewrite <- Hsum_result in Hgt.
      lia.
Qed.

Open Scope Z_scope.


Lemma h_true_with_false :
  forall b (H : b = true),
    b = false -> False.
Proof.
  intros b H Hfalse. rewrite Hfalse in H.
  discriminate H.
Qed.

Open Scope N_scope.
Lemma exceeds_at_t_dec_false :
  forall (c : CumulativeConstraint) (a : Assignment),
  (exists t, 
    (c.(horizon_start) <= t <= c.(horizon_end))%Z
      /\
    usage_sum (activities_at_t (activity_list c a) t) > c.(capacity))
    ->
  cumulative_decide c a = false.
Proof.
  intros c a Hex.
  destruct Hex as [t [Hhorizon Husage]].
  destruct (cumulative_decide c a) eqn:Hdecide; try reflexivity.
  exfalso. unfold cumulative_decide in Hdecide.
  rewrite forallb_forall in Hdecide.
  specialize (Hdecide t).
  specialize c.(horizon_consistent) as Hrange.
  apply (ZRange.build_range_correct (horizon_start c) (horizon_end c)) in Hrange.
  unfold ZRange.is_range in Hrange.
  destruct Hrange as [_ [Ht _]].
  rewrite Ht in Hhorizon.
  apply Hdecide in Hhorizon as Husagelt.
  clear Hhorizon; clear Hdecide.
  rewrite N.leb_le in Husagelt.
  contradiction.
Qed.

Open Scope Z_scope.
Definition var_has_bounds (a : Assignment) (v : Var) (lb : Z) (ub : Z) :=
  lb <= (a.(find_value) v) <= ub.

(* Here, you might think the implication goes both ways, but I was shown this cannot be, so reconsider! *)
Lemma active_at :
  forall t (activities : list Activity),
    forall a lb ub, In a activities ->
      lb <= a.(start) <= ub ->
      ub <= t < (lb + (Z.of_N a.(p_time)))
      ->
      In a (activities_at_t activities t).
Proof.
  intros t activities a lb ub.
  intros Hl Hbounds Ht.
  unfold activities_at_t.
  rewrite filter_In.
  split.
  - exact Hl.
  - unfold is_active_at.
    rewrite andb_true_iff.
    repeat rewrite Z.leb_le.
    lia.
Qed.

Definition mandatory_active (lb : Z) (ub : Z) (t : Z) (p_time : N) :=
  (ub <=? t) && (t <? (lb + (Z.of_N p_time))).


Definition constraint_to_intervals (c : CumulativeConstraint) : list (string * zn_interval * (N * N)) :=
  map (fun elt =>
    match elt with
    | (v, p, u) =>
      match v with
      | interval v =>
        (v.(name), (v.(lower_bound), N.of_nat v.(size)), (p, u))
      end
    end
  ) c.(vs).

Definition inferred_cumulative_bounds (c : CumulativeConstraint) (inference : list Atomic) :=
  apply_atomics_to_variables (constraint_to_intervals c) (map atomic_not inference).

Definition inference_negated (inference : list Atomic) (sol : Assignment) :=
  forall atomic, In atomic (map atomic_not inference) ->
    Is_true (test_atomic_assignment atomic sol).

Definition activity_bounds_is_active (t : Z) (activity : string * zn_interval * (N * N)) : list (string * N) :=
  match activity with
  | (x, i, (p_time, usage)) =>
    match interval_to_bounds i with
    | (lb, ub) =>
      if mandatory_active lb ub t p_time
        then (x, usage) :: nil
        else nil
    end
  end.


Definition activities_bounds_active_at (t : Z) (activities : list (string * zn_interval * (N * N))) :=
  nodup xn_eq_dec (flat_map (activity_bounds_is_active t) activities).

Fixpoint find_overloaded_t_with_mandatory (capacity : N) (ts : list Z) (activities : list (string * zn_interval * (N * N))) := 
  match ts with
  | nil => None
  | t :: ts' =>
    match res_sum capacity (activities_bounds_active_at t activities) with
    | (summed, result, false) => Some (t, summed, result)
    | _ => find_overloaded_t_with_mandatory capacity ts' activities
    end
  end
.

(* Definition i_mandatory_active_at (t : Z) (i : (string * zn_interval * (N * N))) := 
  match i with
  | (_, (lb, size), (p_time, _)) =>
     mandatory_active lb (lb + Z.of_N size) t p_time = true
  end. *)

Definition interval_to_usage (i : (string * zn_interval * (N * N))) : N :=
  match i with
  | (_, _, (_, usage)) => usage
  end.

Open Scope N_scope.

Lemma overload_props :
  forall capacity ts activities,
    match find_overloaded_t_with_mandatory capacity ts activities with
    | None => True
    | Some (t, _, _) => xn_sum (activities_bounds_active_at t activities) > capacity /\ In t ts
    end.
Proof.
  intros c ts activities.
  destruct (find_overloaded_t_with_mandatory c ts activities) as [[[t summed] result] |] eqn:Hres.
  - unfold find_overloaded_t_with_mandatory in Hres.
    induction ts as [| ts_t ts].
    + discriminate Hres.
    + specialize (res_sum_semantics c (activities_bounds_active_at ts_t activities)) as Hres_sum.
      destruct (res_sum c (activities_bounds_active_at ts_t activities)) as [[rs_summed rs_result] rs_b].
      destruct rs_b.
      * apply IHts in Hres; clear IHts.
        destruct Hres as [Hgt Hin].
        split.
        -- exact Hgt.
        -- simpl. right. exact Hin.
      * clear IHts. inversion Hres. subst ts_t; subst rs_summed; subst rs_result. destruct Hres_sum as [_ [_ [Hsub Hgt]]].
        split.
        -- exact Hgt.
        -- simpl. left. reflexivity.
  - reflexivity.
Qed. 

Definition resource_profile_t (capacity : N) (activities : list (string * zn_interval * (N * N))) (t : Z) : (Z * N) :=
  match res_sum capacity (activities_bounds_active_at t activities) with
  (_, usage, _) => (t, usage)
  end
.

Definition resource_profile (capacity : N) (activities : list (string * zn_interval * (N * N))) (times : list Z) := 
  map (resource_profile_t capacity activities) times
.

Lemma resource_profile_correct :
  forall capacity activities times usage t,
    In (t, usage) (resource_profile capacity activities times) ->
      In t times /\
      xn_sum (activities_bounds_active_at t activities) >= usage.
Proof.
  intros c activities times usage t.
  intros Hin.
  unfold resource_profile in Hin.
  rewrite in_map_iff in Hin.
  destruct Hin as [t' [Hprofile Hintimes]].
  unfold resource_profile_t in Hprofile.
  specialize (res_sum_semantics c (activities_bounds_active_at t' activities)) as Hres_sum.
  destruct (res_sum c
  (activities_bounds_active_at t'
  activities)) as [[summed sum_result] b].
  inversion Hprofile. subst t'; subst sum_result; clear Hprofile.
  remember (activities_bounds_active_at t activities) as active; clear Heqactive.
  split.
  - exact Hintimes.
  - clear Hintimes. destruct b.
    + destruct Hres_sum as [Hisusage]. lia.
    + destruct Hres_sum as [Husage [_ [Hsub _]]].
      rewrite <- Husage.
      specialize (xn_sum_sub_list summed active Hsub) as Hsub_sum.
      lia.
Qed.

Open Scope Z_scope.
Definition task_in_constraint (a : string * zn_interval * (N * N)) (c : CumulativeConstraint) (sol : Assignment) :=
  match a with
  | (x, (a_lb, a_size), (p_time, usage)) =>
    exists start_time,
      a_lb <= start_time <= (a_lb + Z.of_N a_size)
        /\
      In (mkAct x start_time p_time usage) (activity_list c sol)
  end.
      

Definition valid_bounds (bounds : list (string * zn_interval * (N * N))) (c : CumulativeConstraint) (sol : Assignment) :=
  forall a, In a bounds -> task_in_constraint a c sol.


Lemma resource_profile_correct_bounds :
  forall (c : CumulativeConstraint) inference sol bounds,
    inference_negated inference sol
    -> inferred_cumulative_bounds c inference = Some bounds
    -> valid_bounds bounds c sol.
Proof.
  intros c inference sol bounds.
  intros Hneg Hbounds.
  unfold inferred_cumulative_bounds in Hbounds.
  unfold valid_bounds.
  intros a.
  intros Hinbounds. specialize (apply_atomics_correct (N * N) ((constraint_to_intervals c)) (map atomic_not inference) bounds Hbounds a Hinbounds) as Happly.
    destruct a as [[x [lb a_size]] [p u]] eqn:Ha.
    destruct Happly as [lb_init [size_init [Hinis [atoms_applied [Hatomsin Hatomproof]]]]].
    unfold task_in_constraint.
    unfold constraint_to_intervals in Hinis.
    rewrite in_map_iff in Hinis.
    destruct Hinis as [[[v v_process] v_usage] [Hv Hvinc]].
    destruct v.
    inversion Hv. subst x; subst lb_init; subst size_init; subst v_process; subst v_usage; clear Hv.
    exists (sol.(find_value) (interval var)).
    split.
    - apply atomic_proof_correct with (lb_init := (lower_bound var)) (size_init := (N.of_nat (size var))) (atoms := atoms_applied) (x := name var); try easy.
      intros atom Hinapplied.
      apply Hneg.
      apply Hatomsin.
      exact Hinapplied.
    - unfold activity_list. unfold activity_list_inner. rewrite in_map_iff.
      exists (interval var, p, u).
      split.
      + unfold activity_list_inner_f. reflexivity.
      + exact Hvinc.
Qed.
(*     
    exists (interval var). simpl. reflexivity.
    - intros v' Hname_eq.
      specialize (c.(unique_vars) (interval var) v' p u Hvinc) as Hunique.
      rewrite Hname_eq in Hunique. simpl in Hunique.
      assert (name var = name var) as Hvv' by reflexivity.
      apply Hunique in Hvv'; subst v'.
      split.
      + exact Hvinc.
      + apply atomic_proof_correct with (lb_init := (lower_bound var)) (size_init := (N.of_nat (size var))) (atoms := atoms_applied) (x := name var); try easy.
        intros atom Hinapplied.
        apply Hneg.
        apply Hatomsin.
        exact Hinapplied.
Qed. *)

Definition c_var_with_x (x : string) (elt : (Var * N * N)) :=
  match elt with
  | (v, _, _) =>
    (x =? var_name v)%string
  end.

Definition x_start_time (x : string) (c : CumulativeConstraint) (sol : Assignment) : Z :=
  match (find (c_var_with_x x) c.(vs)) with
  | None => Z0
  | Some (v, _, _) => sol.(find_value) v
  end.

(* Lemma task_in_constraint_start_time_eq :
forall a c sol,
  match a with
  | (x, _, (p, u)) =>
    task_in_constraint a c sol ->
    forall (v : Var),
      var_name v = x
      -> x_start_time x c sol = sol.(find_value) v
  end.
Proof.
  intros a c sol.
  destruct a as [[x [lb a_size]] [p u]] eqn:Ha.
  intros Htask.
  intros v Hname.
  specialize sol.(find_value_eq_name) as Heq_value.
  unfold x_start_time.
  destruct (find (c_var_with_x x) (vs c)) as [[[v' v_p'] v_u'] |] eqn:Hfind.
  - apply find_some in Hfind.
    apply Heq_value.
    destruct Hfind as [_ Hvar_eq].
    unfold c_var_with_x in Hvar_eq.
    rewrite String.eqb_eq in Hvar_eq.
    rewrite Hname. rewrite <- Hvar_eq. reflexivity.
  - exfalso. apply find_none with (x := (v, p, u)) in Hfind.
    + unfold c_var_with_x in Hfind.
      rewrite String.eqb_neq in Hfind. rewrite Hname in Hfind.
      contradiction.
    + unfold task_in_constraint in Htask.
      destruct Htask as [[v' Hnamev'] Htask].
      apply Htask. exact Hname.
Qed.  *)
        
Lemma task_in_constraint_active_period :
  forall a c sol,
    match a with
    | (x, (lb, size), (p_time, _)) =>
      task_in_constraint a c sol ->
        exists s,
          lb <= s <= lb + Z.of_N size
            /\
          forall t, 
            s <= t < s + Z.of_N p_time
            -> is_active_at s p_time t = true
    end.
Proof.
  intros a c sol.
  destruct a as [[x [lb a_size]] [p u]] eqn:Ha.
  intros Htask.
  unfold task_in_constraint in Htask.
  destruct Htask as [s [Hbound Hactivity]].
  exists s.
  split.
  - exact Hbound.
  - intros t. intros Ht.
    unfold is_active_at.
    lia.
Qed.

Open Scope nat_scope.

(* Fixpoint has_n_true (n : nat) (reset : nat) (current : nat) (l : list bool) : bool :=
  match l with
  | nil => n <=? current
  | b :: l' =>
    if b
      then has_n_true n reset (S current) l'
      else has_n_true n reset reset l'
  end
.

Fixpoint max_n_true (reset : nat) (current : nat) (l : list bool) : nat :=
  match l with
  | nil => current
  | b :: l' =>
    if b
      then max_n_true reset (S current) l'
      else max current (max_n_true reset reset l') 
  end
.

Lemma max_n_true_lt_has_n_true :
  forall n reset l current,
    reset <= n
      ->
    has_n_true n reset current l = false
      ->
    max_n_true reset current l <= n \/ .
Proof.
  intros n reset l current.
  intros Hreset.
  generalize dependent current; generalize dependent l.
  induction l.
  - intros current Hhasn.
    simpl in *.
    rewrite <- not_true_iff_false in Hhasn.
    rewrite Nat.leb_le in Hhasn.
    lia.
  - simpl. destruct a.
    + intros current Hhasn.
      apply IHl. exact Hhasn.
    + intros current Hhasn.
      assert (max_n_true reset reset l <= n).
      { apply IHl. exact Hhasn. }
      assert (current <= n).
      {
        
      } *)

(* Note: we don't care if it traverses the whole list when it finds a valid one, since that is only in the error path. In general it will have to traverse the whole list to ensure there is a conflict since we expect to validate many more inferences than we reject *)
Fixpoint has_n_true (n : nat) (current : nat) (l : list bool) : bool :=
  match l with
  | true :: l' => has_n_true n (S current) l'
  | false :: l' => (n <=? current) || (has_n_true n 0 l')
  | nil => n <=? current
  end
.

Lemma fold_ind {X} :
  forall (Acc:Type)(P : list X -> Acc -> Type)(f : X -> Acc -> Acc)(i : Acc)(s:list X),
  P nil i ->
  (forall x a s',
    P s' a -> P (x :: s') (f x a)) ->
  P s (fold_right f i s).
Proof.
  intros Acc P f i s Hnil Hstep.
  induction s as [| x s IH].
  - simpl. exact Hnil.
  - simpl. specialize (Hstep x (fold_right f i s)).
    apply Hstep.
    exact IH.
Qed.

Open Scope N_scope.
Definition max_n_foldf (b : bool) (acc : (N * N)) : (N * N) :=
  match acc with 
  | (current, max) =>
    match b with
    | true => (current + 1, max)
    | false => (0, if (max <? current) then current else max)
    end
  end.



Definition max_n_fold (l : list bool) :=
  fold_right max_n_foldf (0, 0) l.



(* Lemma fold_ind_left {X} :
  forall (Acc:Type)(P : list X -> Acc -> Type)(f : Acc -> X -> Acc)(i : Acc)(s:list X),
  P nil i ->
  (forall x a s',
    P s' a -> P (x :: s') (f a x)) ->
  P s (fold_left f s i).
Proof.
  intros Acc P f i s Hnil Hstep.
  induction s as [| x s IH].
  - simpl. exact Hnil.
  - simpl. specialize (Hstep x (fold_left f s i)).
    apply Hstep.
    exact IH.
Qed. *)

Open Scope nat_scope.
Fixpoint run_size (l : list bool) : nat :=
  match l with
  | nil => O
  | false :: l' => O
  | true :: l' => S (run_size l')
  end.

(* Fixpoint run_size_rest (l : list bool) : (nat * list bool) :=
  match l with
  | nil => (O, nil)
  | false :: l' => O
  | true :: l' => S (run_size l')
  end. *)

Definition run_at (n : nat) (l : list bool) : nat :=
  run_size (skipn n l). 

Fixpoint max_n_true (current : nat) (l : list bool) : nat :=
  match l with
  | nil => current
  | b :: l' =>
    if b
      then max_n_true (S current) l'
      else max current (max_n_true 0 l') 
  end
.

Lemma l_ind {X} :
   forall P : list X -> Type,
   P nil ->
   (forall l', P l' -> forall x,  P (x :: l')) ->
   forall l, P l.
Proof.
  intros P Hnil Hstep.
  induction l.
  - apply Hnil.
  - apply Hstep. exact IHl.
Qed.

Lemma has_0_true :
  forall l start,
    has_n_true 0 start l = true.
Proof.
  induction l.
  - intros. simpl. reflexivity.
  - intros start. simpl.
    destruct a.
    + apply IHl.
    + reflexivity.
Qed.

(* Fixpoint has_n_true (n : nat) (current : nat) (l : list bool) : bool :=
  match l with
  | nil => n <=? current
  | b :: l' =>
    if b
      then has_n_true n (S current) l'
      else has_n_true n 0 l'
  end
. *)

(* Lemma max_n_true_lt_has_n_true :
  forall l n current,
    has_n_true n current l = false
      ->
    run_size l <=  *)

Lemma max_n_true_lt_has_n_true :
  forall l n current,
    has_n_true n current l = false
      ->
    max_n_true current l <= n.
Proof.
  induction l.
  - intros n current Hhasn.
    simpl in *.
    rewrite <- not_true_iff_false in Hhasn. rewrite Nat.leb_le in Hhasn.
    lia.
  - simpl. destruct a.
    + intros n current Hhasn.
      apply IHl.
      exact Hhasn.
      (* intros n Hhasn.
      specialize (IHl (pred n)). *)
      (* assert (has_n_true (pred n) 0 l = false).
      {
        (* Does not hold in general! *)
      } *)
      (* specialize (IHl n (S current)).
      apply IHl in Hhasn.
      destruct 
      apply IHl. exact Hhasn. *)
    + intros n current Hhasn.
      rewrite orb_false_iff in Hhasn.
      destruct Hhasn as [Hncurrent Hhasn].
      rewrite <- not_true_iff_false in Hncurrent.
      rewrite Nat.leb_le in Hncurrent.
      assert (max_n_true 0 l <= n).
      { apply IHl. exact Hhasn. }
      lia.
Qed.

Admitted. 
      (* intros n current Hhasn.
      assert (max_n_true 0 l <= n).
      { apply IHl. exact Hhasn. }
      assert (current <= n).
      {
        
      } *) 


Lemma max_run_lt_start :
  forall l s1 s2,
  s1 <= s2
    ->
  max_n_true s1 l <= max_n_true s2 l.
Proof.
  induction l.
  - intros s1 s2 H. simpl. exact H.
  - intros s1 s2 H. simpl. destruct a.
    + apply IHl. lia.
    + clear IHl. lia.
Qed.

(* Lemma max_run_is_max :
  forall l current,
  max_n_true current l >= max (run_size l + current) (max_n_true current (tl l)).
Proof.
  induction l.
  - intros current.
    simpl. lia.
  - intros current. simpl.
    destruct a.
    + specialize (IHl (S current)).
      admit.
    + simpl.
      
      symmetry.
      destruct ((S (run_size l) + current) <=? (max_n_true current l)) eqn:Hlt.
      * assert .  *)
  (* intros l current.
  enough (max_n_true current l <= max_n_true (S current) (tl l)).
  - lia.
  - generalize dependent current.
    induction l.
    + intros current. simpl. lia.
    + intros current. simpl.
      destruct a.
      * reflexivity.
      * enough (max_n_true 0 l <= max_n_true 1 l)
  induction l.
  - intros current. simpl. lia.
  - intros current. *)



Fixpoint max_runs (l : list bool) : nat :=
  match l with
  | nil => O
  | _ :: l' => max (run_size l) (max_runs l')
  end
.

Lemma run_size_le_pre :
  forall l start,
    run_size l <= max_n_true start l.
Proof.

Lemma nth_false_run_lt :
  forall l n,
    (exists k,
      k <= n /\ nth k l false = false)
      <->
    run_size l <= n.
Proof.
  induction l.
  - intros n. split.
    + intros. simpl. lia.
    + intros Hnil. simpl in Hnil.
      exists 0.
      split.
      * exact Hnil.
      * simpl. reflexivity.
  - intros n. 
    split.
    + simpl. intros Hk.
      destruct Hk as [k [Hkn Hkfalse]].
      destruct a.
      * destruct k; try discriminate Hkfalse.
        specialize (IHl (pred n)).
        assert (exists k, k <= pred n /\ nth k l false = false).
        {
         exists k.
         split.
         - lia.
         - exact Hkfalse. 
        }
        rewrite IHl in H.
        lia.
      * lia.
    + simpl. destruct a.
      * intros Hrun.
        assert (run_size l <= pred n) by lia.
        rewrite <- IHl in H.
        destruct H as [k [Hkn Hkfalse]].
        exists (S k).
        split.
        -- lia.
        -- exact Hkfalse.
      * intros H; clear H.
        exists 0.
        split.
        -- lia.
        -- reflexivity.
Qed.
      
Lemma run_size_le :
  forall l start,
    run_size l + start <= max_n_true start l.
Proof.
  induction l.
  - intros start. simpl. reflexivity.
  - simpl. destruct a.
    + intros start.
      specialize (IHl start).

      (* destruct (max_n_true start l <? start) eqn:Hlstart.
      { rewrite Nat.ltb_lt in Hlstart. exfalso. lia. }
      rewrite <- not_true_iff_false in Hlstart.
      rewrite Nat.ltb_lt in Hlstart.
      assert (run_size l <= (max_n_true start l) - start) by lia.
      rewrite <- nth_false_run_lt in H.
      destruct H as [k [Hkmaxn Hkfalse]]. *)


      (* destruct (max_n_true start l <=? (pred start)) eqn:Hlstart.
      * rewrite Nat.leb_le in Hlstart. exfalso.
        
        remember (run_size l) as n; remember (max_n_true start l) as m;
        clear Heqn; clear Heqm.
        assert (n + start <= start). *)

      admit.
    + intros start. lia.
Admitted.

Open Scope N_scope.
Definition pprop (l : list bool) (acc : (N * N)) :=
  match acc with
  | (current, max) =>
    N.of_nat (max_runs l) <= max

  end.

(* Lemma max_runs_max_lin :
  forall l,
    (N.of_nat (max_runs l) <= snd (max_n_fold l))%N.
Proof.
  intros l.
  assert (pprop l (max_n_fold l)).
  {
    unfold max_n_fold.
    apply fold_ind; unfold pprop in *.
    - simpl. reflexivity.
    - clear l; intros x a l.
      destruct a as [current max].
      intros Hmax.
      destruct (max_n_foldf x (current, max)) as [current' max'] eqn:Hfold.
      simpl in *.
      destruct x eqn:Hx.
      + inversion Hfold.
        subst current'; subst max'; clear Hfold.
        admit.
      + destruct (max <? current) eqn:Hmaxcurr.
        * inversion Hfold.
          subst max'; subst current'; clear Hfold.
          rewrite N.ltb_lt in Hmaxcurr.
          lia.
        * inversion Hfold.
        subst max'; subst current'; clear Hfold.
        rewrite <- not_true_iff_false in Hmaxcurr.
        rewrite N.ltb_lt in Hmaxcurr.
        lia.
  }
  intros l. *)
  

Open Scope nat_scope.
Lemma max_runs_max_lin :
  forall l start,
    max_runs l <= max_n_true start l.
Proof.
  induction l.
  - intros start.
    simpl. lia.
  - intros start.
    simpl.
    destruct a.
    + destruct (max_runs l <=? S (run_size l)) eqn:Hmax.
      * assert (max (S (run_size l))
      (max_runs l) = S (run_size l)).
        {
          apply max_l. rewrite <- Nat.leb_le. exact Hmax.
        }
        rewrite H; clear H; clear Hmax; clear IHl.
        specialize (run_size_le l (S start)) as Hrun.
        lia.
      * assert (max (S (run_size l))
      (max_runs l) = (max_runs l)).
        {
          apply max_r.
          rewrite <- not_true_iff_false in Hmax.
          rewrite Nat.leb_le in Hmax.
          lia.
        }
        rewrite H; clear H; clear Hmax.
        apply IHl.
    + assert (max_runs l <= max_n_true 0 l) by (apply IHl).
      lia.
Qed.
        


Definition has_run (l: list bool) (size : nat) :=
  exists n,
    nth n l false = true
      /\
    forall k,
      n <= k <= n + size
        ->
      nth k l false = true.




Lemma has_n_true_false :
  forall n l start,
    start <= n
      ->
    has_n_true n start l = false
      ->
    max_n_true start l < n.
Proof.
  intros n l.
  induction l.
  - intros start Hstartle Hntrue. 
    unfold has_n_true in Hntrue. unfold max_n_true.
    rewrite <- not_true_iff_false in Hntrue.
    rewrite Nat.leb_le in Hntrue.
    lia.
  - intros start Hstartle Hntrue.
    simpl in *.
    destruct (start =? n) eqn:Hnstart.
    + rewrite Nat.eqb_eq in Hnstart.
      subst start; clear Hstartle.
      destruct a.
      * 
    + rewrite Nat.eqb_neq in Hnstart.
      destruct a.
      * apply IHl.
        -- lia.
        -- exact Hntrue.
      * enough (max_n_true 0 l < n).
        -- lia.
        -- apply IHl.
          ++ lia.
          ++ exact Hntrue.
Qed.

    + admit.
    + induction l.
      * simpl in *.

    destruct (stmax_n_foldart =? n) eqn:Hnstart.

    + apply IHl.
      * 
    apply IHl.
    + exact Hntrue.
    + induction l.
      * simpl in *.
        apply IHl in Hntrue.
    

Inductive N_True : list bool -> nat -> nat -> Prop :=
  | N_True_0 (l : list bool) : N_True l 0 0
  | N_True_cons_true (current max : nat) (l' : list bool) (H : N_True l' current max) : N_True (true :: l') (S current) (if (current =? max) then S max else max)
  | N_True_cons_false (current max : nat) (l' : list bool) (H : N_True l' current max) : N_True (false :: l') 0 max.
  
  
Lemma has_n_true_N_True :
  forall l max current,
    current <= max
      ->
    has_n_true max l current = true
      ->
    N_True l current max.
Proof.
  intros l max current Hmaxlecurr Hntrue.
  induction current; induction max; induction l.
  - apply N_True_0.
  - apply N_True_0.
  - unfold has_n_true in Hntrue.
    destruct (S max <=? 0) eqn:Hmax0.
    + exfalso; clear IHmax. rewrite Nat.leb_le in Hmax0.
      lia.
    + discriminate Hntrue.
  - unfold has_n_true in Hntrue.
    destruct (S max <=? 0) eqn:Hmax0.
    + exfalso; clear IHmax; clear IHl. rewrite Nat.leb_le in Hmax0.
      lia.
    + clear Hmax0; clear Hmaxlecurr.
      destruct a.
      * destruct l.
        -- assert (max = 0).
          { destruct (S max <=? 1) eqn:Hmax; try discriminate Hntrue.
            rewrite Nat.leb_le in Hmax. clear IHmax; clear IHl; lia. }
          subst max; clear Hntrue.
          assert (0 <= 0) as H0 by reflexivity.
          apply IHmax in H0.
          ++ inversion H0.

          



Open Scope Z_scope.
(* Lemma hole2 :
  forall range range_l range_e (f : Z -> bool) length start,
    range_l <= start
      ->
    range_e <= start + Z.of_nat length
      ->
    ZRange.is_range range_l range_e range 
      ->
    (forall x, 
      start <= x <= start + Z.of_nat length
        <->
      f x = true
    )
      ->
    has_hole_of_size (map f range) 0 length = true.
Proof.
  induction range.
  - intros range_l range_e f length start.
    intros Hrange_l Hrange_e Hrange Hftrue.
    simpl.
    unfold ZRange.is_range in Hrange.
    destruct Hrange as [Hle [Hn _]].
    assert (range_l <= range_l <= range_e) as Htonil.
    { lia. }
    rewrite Hn in Htonil. destruct Htonil.
  - intros range_l range_e f length start.
    intros Hrange_l Hrange_e Hrange Hftrue.
    induction length.
    + simpl. reflexivity.
    + simpl.
      unfold ZRange.is_range in Hrange.
      destruct Hrange as [Hle [Hrangein Hsucc]].
      assert (In a (a :: range)) as Hainarange.
      { left. reflexivity. }
      rewrite <- Hrangein in Hainarange.
      destruct ((start <=? a) && (a <=? start + Z.of_nat (S length))) eqn:Ha.
      * rewrite andb_true_iff in Ha; repeat rewrite Z.leb_le in Ha.
        rewrite Hftrue in Ha. rewrite Ha.


    (* specialize (IHrange range_l range_e f length start Hrange_l Hrange_e). *)
    destruct (range_l =? range_e) eqn:Hlr.
    {
     rewrite Z.eqb_eq in Hlr; subst range_e.
     unfold ZRange.is_range in Hrange.
     simpl.
     destruct Hrange as [_ [Hn Hsucc]].
     specialize (IHrange range_l range_l f length start Hrange_l Hrange_e).

    }
    simpl.
    assert (ZRange.is_range range_l (range_e - 1) range).
    {
      clear IHrange.
      unfold ZRange.is_range in Hrange.
      destruct Hrange as [Hrangele [Hnin Hsucc]].
      unfold ZRange.is_range.
      split; try assumption.
      split.
      - intros n.
        split.
        + intros Hnbetween.
          rewrite Hnin in Hnbetween.
    } *)



Definition active_list (start_time : Z) (p_time : N) (times : list Z) : list bool :=
  map (is_active_at start_time p_time) times.
  

(* Lemma hole :
  forall (p : nat) s lb size times range_l range_e,
    range_l <= lb
    ->
    range_e >= lb + Z.of_N size
    ->
    (
      lb <= s <= lb + Z.of_N size
        /\
      forall t, 
        s <= t < s + Z.of_nat p
          -> 
        is_active_at s (N.of_nat p) t = true
    )
      ->
    ZRange.is_range range_l range_e times
      ->
    has_hole_of_size (active_list s (N.of_nat p) times) p = true.
Proof.
  induction p as [| p IH].
  - intros s lb size times range_l range_e.
    intros Hrange_l Hrange_e Hactive Hrange.
    unfold N.of_nat in *; unfold Z.of_nat in *.
    unfold has_hole_of_size.
    destruct (active_list s 0 times); reflexivity.
  - intros s lb size times range_l range_e. 
    intros Hrange_l Hrange_e Hactive Hrange.

  induction (N.to_nat p_time) as [|] eqn:Hp_time.
  - assert (p_time = 0%N).
    { clear Hactive; clear Hrange; lia. }
    subst p_time; clear Hp_time.
    unfold has_hole_of_size.
    destruct (active_list s 0 times); reflexivity.
  - assert (p_time = (N.of_nat n) + 1)%N.
    { clear Hrange; clear IHn; clear Hactive; lia. }
    subst p_time. *)



    
    

  (* specialize (task_in_constraint_start_time_eq a c sol) as Hstart_eq_all.
  assert (task_in_constraint
  (x, (lb, a_size), (p, u)) c sol) as Hstart_eq by assumption.
  unfold task_in_constraint in Htask.
  destruct Htask as [[v Hv] Htask].
  apply Hstart_eq_all with (v := v) in Hstart_eq; try assumption; clear Hstart_eq_all.
  apply Htask in Hv; clear Htask.
  destruct Hv as [Hvin Hbound].
  exists (find_value sol v).
  split.
  - exact Hbound.
  - intros t Ht.
    unfold is_active_at.
    rewrite andb_true_iff.
    rewrite Z.leb_le.
    rewrite Z.ltb_lt.
    rewrite Hstart_eq.
    exact Ht.
Qed. *)
  



Open Scope N_scope.
Definition can_be_active_at_t (capacity : N) (profile_usage : N) (activity : string * zn_interval * (N * N)) (time : Z) : bool :=
  match activity with
  | (_, _, (_, usage)) =>
    match activity_bounds_is_active time activity with
    | nil => true
    | _ => profile_usage + usage <? capacity
    end
  end
.


 

Open Scope Z_scope.
Definition make_active_list_f (capacity : N) (activity : string * zn_interval * (N * N)) (profile_entry : (Z * N)) : list bool :=
  match activity with
  | (_, (lb, size), _) =>
    match profile_entry with
    | (t, profile_usage) =>
      if (t >=? lb) && (t <=? (lb + Z.of_N size))
        then (can_be_active_at_t capacity profile_usage activity t) :: nil
        else nil
    end
  end
.

Definition make_active_list (capacity : N) (profile : list (Z * N)) (activity : string * zn_interval * (N * N)) : list bool :=
  flat_map (make_active_list_f capacity activity) profile.

Definition cannot_schedule_activity_w_profile (capacity : N) (profile : list (Z * N)) (activity : string * zn_interval * (N * N)) : bool :=
  match activity with
  | (_, _, (duration, _)) =>
    negb (has_n_true (N.to_nat duration) (make_active_list capacity profile activity) 0)
  end.

Definition var_empty_domain (v : Var) (sol : Assignment) :=
  exists n m,
    n < m
      /\
    m <= sol.(find_value) v <= n.

Definition ex_var_empty_domain (sol : Assignment) :=
  exists (v : Var),
    var_empty_domain v sol.

Definition cumulative_checker (inference : list Atomic) (constraint : CumulativeConstraint) : bool :=
  let times := (ZRange.build_range constraint.(horizon_start) constraint.(horizon_end)) in
  match inferred_cumulative_bounds constraint inference with
  | None => false
  | Some bounds => 
    match find_overloaded_t_with_mandatory (constraint.(capacity)) times bounds with
    | None => 
      let r_profile := resource_profile (constraint.(capacity)) bounds times in
      existsb (cannot_schedule_activity_w_profile (constraint.(capacity)) r_profile) bounds 
    | Some _ => true
    end
  end
.

Lemma neg_atomic : forall sol inference, satisfies_nogood inference sol = false -> inference_negated inference sol.
Proof.
  intros sol inference Hsat.
  unfold inference_negated. intros atomic.
  apply unsat_nogood.
  exact Hsat.
Qed.

Open Scope Z_scope.
(* Lemma checker_true_finds_overloaded_t :
  forall fact sol constr,
  inference_negated fact sol ->
  cumulative_checker fact constr = true
  ->
  exists t,
    horizon_start constr <= t <= horizon_end constr /\
    (usage_sum
    (activities_at_t (activity_list constr sol) t) >
    capacity constr)%N.
Proof.
  intros fact sol constr.
  intros Hinf Hchecked.
  unfold cumulative_checker in Hchecked.
  destruct (inferred_cumulative_bounds constr fact) as [bounds |] eqn:Hbounds.
  - specialize (overload_props constr.(capacity) (ZRange.build_range constr.(horizon_start) constr.(horizon_end)) bounds) as Hoverload.
    destruct (find_overloaded_t_with_mandatory (capacity constr)
    (ZRange.build_range (horizon_start constr)
    (horizon_end constr)) bounds) as [[[t usages_t] _] |].
    {
     exists t.
     destruct Hoverload as [Hsum Hinhorz].
     split.
     - rewrite ZRange.build_range_correct.
      + exact Hinhorz.
      + exact constr.(horizon_consistent).
    - clear Hinhorz; clear Hchecked; clear usages_t.
      unfold usage_sum.
      apply xn_sum_sub_list_gtn with (l1 := (activities_bounds_active_at t bounds)).
      + clear Hsum.
        apply sub_list_if_in_nodup.
        * intros a Hin.
          rewrite in_map_iff.
          assert (In a (activities_bounds_active_at t bounds)) as Hin2 by assumption.
          unfold activities_bounds_active_at in Hin.
          rewrite nodup_In in Hin.
          rewrite in_flat_map in Hin.
          destruct Hin as [a' [Hinbounds Hinres]].
          destruct a' as [[x [lb size]] [p u]] eqn:Ha'.
          unfold activity_bounds_is_active in Hinres.
          destruct (interval_to_bounds (lb, size)) as [lb' ub] eqn:Hibounds. unfold interval_to_bounds in Hibounds; inversion Hibounds; subst lb'; symmetry in H1; clear Hibounds.
          destruct (mandatory_active lb ub t p) eqn:Hmand.
          2: destruct Hinres.
          simpl in Hinres. destruct Hinres; try contradiction. subst a.
          unfold inferred_cumulative_bounds in Hbounds.
          rewrite <- Ha' in Hinbounds.
          specialize (apply_atomics_correct (N * N) ((constraint_to_intervals constr)) (map atomic_not fact) bounds Hbounds a' Hinbounds) as Happly.
          rewrite Ha' in Happly; clear Hinbounds; clear Ha'; clear a'.
          destruct Happly as [lb_init [size_init [Hinis [atoms_applied [Hatomsin Hatomproof]]]]].
          unfold constraint_to_intervals in Hinis.
          rewrite in_map_iff in Hinis.
          destruct Hinis as [[[v p'] u'] [His Hinc]].
          destruct v; inversion His.
          subst p'; subst u'.
          exists (mkAct x (sol.(find_value) (interval var)) p u). split.
          { simpl. subst x. reflexivity. }
          apply active_at with (lb := lb) (ub := ub).
          -- unfold activity_list. unfold activity_list_inner. rewrite in_map_iff.
            exists (interval var, p, u).
            split.
            ++ unfold activity_list_inner_f. subst x.
            reflexivity.
            ++ exact Hinc.
          -- simpl. subst ub.
            apply atomic_proof_correct with (x := x) (atoms := atoms_applied) (lb_init := lb_init) (size_init := size_init); try assumption.
            intros atom Hinapplied.
            apply Hinf.
            apply Hatomsin.
            exact Hinapplied.
          -- simpl. unfold mandatory_active in Hmand.
            apply andb_true_iff in Hmand.
            rewrite Z.leb_le in Hmand.
            rewrite Z.ltb_lt in Hmand.
            exact Hmand. 
        * unfold activities_bounds_active_at. 
          (* TODO: try and get rid of this, but it only really matters for performance *)
          apply NoDup_nodup.
      + exact Hsum.
    }
    { discriminate Hchecked. }
  - discriminate Hchecked.
Qed. *)



(* Definition empty_domain (x : string) (sol : Assignment) :=
  exists n m,
    n < m ->
      forall v,
        var_name v = x ->
          (sol.(find_value) v) >= n

. *)



Lemma empty_domain_is_false :
  forall sol,
    ex_var_empty_domain sol -> False.
Proof.
  intros sol. unfold not. intros Hempty.
  unfold ex_var_empty_domain in Hempty; unfold var_empty_domain in Hempty.
  destruct Hempty as [v [n [m Hempty]]].
  lia.
Qed.

Lemma checker_not_cumulative :
  forall fact sol constr,
  Is_true (cumulative_decide constr sol)
  -> Is_true (cumulative_checker fact constr)
  -> inference_negated fact sol
  -> False.
Proof.
  intros fact sol constr.
  intros Hconstr Hchecked Hneg.
  apply Is_true_eq_true in Hchecked.
  unfold cumulative_checker in Hchecked.
  destruct (inferred_cumulative_bounds constr fact) as [bounds |] eqn:Hbounds.
  2: discriminate Hchecked.
  specialize (overload_props constr.(capacity) (ZRange.build_range constr.(horizon_start) constr.(horizon_end)) bounds) as Hoverload.
  destruct (find_overloaded_t_with_mandatory (capacity constr)
  (ZRange.build_range (horizon_start constr)
  (horizon_end constr)) bounds) as [[[t usages_t] _] |].
  {
    enough (cumulative_decide constr sol = false).
    {
    rewrite H in Hconstr. apply Hconstr.
    }
    apply exceeds_at_t_dec_false.
    exists t.
    destruct Hoverload as [Hsum Hinhorz].
    split.
    - specialize (ZRange.build_range_correct (horizon_start constr) (horizon_end constr) (horizon_consistent constr)) as Hrange.
      unfold ZRange.is_range in Hrange.
      destruct Hrange as [_ [Hrange _]].
      rewrite Hrange.
      exact Hinhorz.
    - clear Hinhorz; clear Hchecked; clear usages_t.
      unfold usage_sum.
      apply xn_sum_sub_list_gtn with (l1 := (activities_bounds_active_at t bounds)).
      + clear Hsum.
        apply sub_list_if_in_nodup.
        * intros a Hin.
          rewrite in_map_iff.
          assert (In a (activities_bounds_active_at t bounds)) as Hin2 by assumption.
          unfold activities_bounds_active_at in Hin.
          rewrite nodup_In in Hin.
          rewrite in_flat_map in Hin.
          destruct Hin as [a' [Hinbounds Hinres]].
          destruct a' as [[x [lb size]] [p u]] eqn:Ha'.
          unfold activity_bounds_is_active in Hinres.
          destruct (interval_to_bounds (lb, size)) as [lb' ub] eqn:Hibounds. unfold interval_to_bounds in Hibounds; inversion Hibounds; subst lb'; symmetry in H1; clear Hibounds.
          destruct (mandatory_active lb ub t p) eqn:Hmand.
          2: destruct Hinres.
          simpl in Hinres. destruct Hinres; try contradiction. subst a.
          unfold inferred_cumulative_bounds in Hbounds.
          rewrite <- Ha' in Hinbounds.
          specialize (apply_atomics_correct (N * N) ((constraint_to_intervals constr)) (map atomic_not fact) bounds Hbounds a' Hinbounds) as Happly.
          rewrite Ha' in Happly; clear Hinbounds; clear Ha'; clear a'.
          destruct Happly as [lb_init [size_init [Hinis [atoms_applied [Hatomsin Hatomproof]]]]].
          unfold constraint_to_intervals in Hinis.
          rewrite in_map_iff in Hinis.
          destruct Hinis as [[[v p'] u'] [His Hinc]].
          destruct v; inversion His.
          subst p'; subst u'.
          exists (mkAct x (sol.(find_value) (interval var)) p u). split.
          { simpl. subst x. reflexivity. }
          apply active_at with (lb := lb) (ub := ub).
          -- unfold activity_list. unfold activity_list_inner. rewrite in_map_iff.
            exists (interval var, p, u).
            split.
            ++ unfold activity_list_inner_f. subst x.
            reflexivity.
            ++ exact Hinc.
          -- simpl. subst ub.
            apply atomic_proof_correct with (x := x) (atoms := atoms_applied) (lb_init := lb_init) (size_init := size_init); try assumption.
            intros atom Hinapplied.
            apply Hneg.
            apply Hatomsin.
            exact Hinapplied.
          -- simpl. unfold mandatory_active in Hmand.
            apply andb_true_iff in Hmand.
            rewrite Z.leb_le in Hmand.
            rewrite Z.ltb_lt in Hmand.
            exact Hmand. 
        * unfold activities_bounds_active_at. 
          (* TODO: try and get rid of this, but it only really matters for performance *)
          apply NoDup_nodup.
      + exact Hsum.
    }
    { 
      clear Hoverload.
      apply existsb_exists in Hchecked.
      destruct Hchecked as [a [Hbound Hcannot_sched]].
      specialize (apply_atomics_correct (N * N) ((constraint_to_intervals constr)) (map atomic_not fact) bounds Hbounds a Hbound) as Happly.
      destruct a as [[x [lb size]] [p u]] eqn:Ha.
      destruct Happly as [lb_init [size_init [Hinis [atoms_applied [Hatomsin Hatomproof]]]]].
      unfold cannot_schedule_activity_w_profile in Hcannot_sched.
      rewrite negb_true_iff in Hcannot_sched.

      rewrite <- Ha in *.
      

    }
  

  (* apply sufficient_false.
  apply Is_true_eq_true in Hchecked.
  apply checker_true_finds_overloaded_t with (fact := fact); assumption. *)
Admitted.

Lemma is_true_false_not :
  forall b, Is_true b -> b = false -> False.
Proof.
  intros. unfold Is_true in H.
  rewrite H0 in H. exact H.
Qed.

Lemma is_true_not_false :
  forall b, (b = false -> False) -> Is_true b.
Proof.
  intros. destruct b.
  - reflexivity.
  - simpl. apply H. reflexivity.
Qed.

Lemma cumulative_checker_valid :
  forall fact sol constr,
  Is_true (cumulative_decide constr sol) ->
  Is_true (cumulative_checker fact constr) ->
  Is_true (satisfies_nogood fact sol).
Proof.
  intros fact sol constr.
  intros Hcumul Hchecked.
  apply is_true_not_false.
  intros Hsat.
  apply neg_atomic in Hsat.
  apply checker_not_cumulative with (fact := fact) (sol := sol) (constr := constr); assumption.
Qed.


