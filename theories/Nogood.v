Require Import Bool.
Require Import Checker.Variable.
Require Import Checker.Atomic.
Require Import ZArith.
Require Import List.
Require Import Logic.FunctionalExtensionality.
Open Scope Z_scope.

Definition Clause := list Atomic.

Fixpoint satisfies_nogood (x : Clause) (sol : Assignment) :=
  match x with
  | nil => false
  | a :: xs =>
  let val := (find_value sol) (var a) in
      if test_atomic a val
      then true
      else satisfies_nogood xs sol
  end.


Theorem unsat_nogood : (forall (atomic : Atomic) (i : list Atomic) (s : Assignment),
  satisfies_nogood i s = false ->
  In atomic (map atomic_not i) ->
  Is_true (test_atomic_assignment atomic s)).
Proof.
  intros atomic i.
  generalize dependent atomic.
induction i ; simpl ; intros ; try contradiction.
  destruct (test_atomic a (find_value s (var a))) eqn:Ha_test.
  discriminate.
  destruct H0 as [Hfound|Htail].
  - unfold test_atomic_assignment.
    rewrite <- Hfound, <- atomic_not_variable_eq, atomic_not_involution, Ha_test.
    reflexivity.
  - apply IHi.
    + apply H.
    + apply Htail.
Qed.


Definition satisfies_all_nogoods (xs : list Clause) (sol : Assignment) :=
  forallb (fun x => satisfies_nogood x sol) xs.

Definition is_valid_nogood
  (inference : Clause) (clause_seq : list Clause) : Prop := 
  forall (sol : Assignment),
  Is_true (satisfies_all_nogoods clause_seq sol) ->
  Is_true (satisfies_nogood inference sol).

Definition contradiction (literals : list Atomic) : bool :=
  let contra_checker :=
    fun given => existsb (fun other => contradiction_binary given other) literals
  in
  existsb contra_checker literals.

Lemma no_solutions_if_contradict :
  forall (assumptions : list Atomic) (sol : Assignment),
  contradiction assumptions = true -> 
  (forall (a : Atomic), In a assumptions -> Is_true (test_atomic_assignment a sol)) -> False.
Proof.
  unfold contradiction.
  intros.
  apply existsb_exists in H.
  destruct H as [x [Hxin H]].
  apply existsb_exists in H.
  destruct H as [y [Hyin contra]].
  apply Is_true_eq_left in contra.
  apply contradiction_at_most_one with (x := find_value sol (var x))
    in contra as contra_at_most_one.
  unfold contradiction_binary in contra.
  destruct (eqb (var x) (var y)) eqn:Evar ; try contradiction.
  apply Is_true_eq_left, eqb_eq in Evar.
  destruct contra_at_most_one.
  - specialize (H0 x Hxin) as Hsat.
    unfold test_atomic_assignment in Hsat.
    contradiction.
  - specialize (H0 y Hyin) as Hsat.
    rewrite Evar in H.
    unfold test_atomic_assignment in Hsat.
    contradiction.
Qed.


Definition simplify (clause : Clause) (assumptions : list Atomic) : Clause :=
  filter (fun lit => negb (contradiction (lit :: assumptions))) clause.


Theorem simplify_equiv : forall (clause : Clause) (assumptions : list Atomic) (sol : Assignment),
  Is_true (satisfies_nogood clause sol) ->
  (forall (a : Atomic), In a assumptions -> Is_true (test_atomic_assignment a sol)) ->
  Is_true (satisfies_nogood (simplify clause assumptions) sol).
Proof.
  intros clause assumptions sol Hnogood Hsat.
  generalize dependent clause.
  intros.
  induction clause as [|clause_head clause_left] ; try contradiction.
  simpl.
  destruct (contradiction (clause_head :: assumptions)) eqn:Econtra_clause_assumption ; simpl.
  - apply IHclause_left.
    unfold satisfies_nogood in Hnogood.
    destruct (test_atomic clause_head (find_value sol (var clause_head))) eqn:Eclause_head_test ; simpl .
    + exfalso.
      apply no_solutions_if_contradict with (assumptions := clause_head :: assumptions) (sol := sol).
      * apply Econtra_clause_assumption.
      * simpl.
        intros.
        destruct H.
        -- rewrite <- H.
           unfold test_atomic_assignment.
           rewrite Eclause_head_test.
           reflexivity.
        -- apply Hsat, H.
    + fold satisfies_nogood in Hnogood.
      apply Hnogood.
  - destruct (test_atomic clause_head (find_value sol (var clause_head))) eqn:Eclause_head_test ; simpl ; try exact I.
    apply IHclause_left.
    unfold satisfies_nogood in Hnogood.
    rewrite Eclause_head_test in Hnogood.
    fold satisfies_nogood in Hnogood.
    apply Hnogood.
Qed.



Definition find_unit (clause : Clause) (assumptions : list Atomic) : option Atomic :=
  match simplify clause assumptions with
  | unit :: nil => Some unit
  | _ => None
  end.

Fixpoint rup 
  (clause_seq : list Clause)
  (true_literals : list Atomic) : bool :=
  if contradiction true_literals then true
  else
  match clause_seq with
  | nil => false
  | clause :: remaining =>
      match find_unit clause true_literals with
      | Some x => rup remaining (x :: true_literals)
      | None => false
      end
  end.

Lemma satisfy_unit_clause :
  forall (assumptions : list Atomic) (clause : Clause) (sol : Assignment) (unit : Atomic),
  Is_true (satisfies_nogood clause sol) ->
  find_unit clause assumptions = Some unit -> 
  (forall (a : Atomic), In a assumptions -> Is_true (test_atomic_assignment a sol)) ->
  Is_true (test_atomic_assignment unit sol).
Proof.
  unfold find_unit.
  intros.
  destruct (simplify clause assumptions) as [|head [|tail]] eqn:simplified ;
  inversion H0.
  rewrite H3 in simplified.
  assert (Hunit: Is_true (satisfies_nogood (unit :: nil) sol)). { 
    rewrite <- simplified.
    apply simplify_equiv, H1.
    apply H.
  }
  simpl in Hunit.
  unfold test_atomic_assignment.
  remember (test_atomic unit (find_value sol (var unit))) as t.
  destruct t.
  - apply Hunit.
  - contradiction.
Qed.


Lemma no_solutions_if_rup :
  forall (clause_seq : list Clause) (assumptions : list Atomic) (sol : Assignment),
  Is_true (rup clause_seq assumptions) ->
  Is_true (satisfies_all_nogoods clause_seq sol) ->
  (forall (a : Atomic), In a assumptions -> Is_true (test_atomic_assignment a sol)) -> False.
Proof.
  intros.
  generalize dependent assumptions.
  generalize dependent sol.
  induction clause_seq as [|clause] ; simpl ; intros ;
  destruct (contradiction assumptions) eqn:contra ; try contradiction .
  - apply no_solutions_if_contradict with (assumptions := assumptions) (sol := sol).
    + apply contra.
    + apply H1.
  - apply no_solutions_if_contradict with (assumptions := assumptions) (sol := sol).
    + apply contra.
    + apply H1.
  - destruct (find_unit clause assumptions) as [unit|] eqn:is_unit;
    simpl ; try contradiction.
    apply IHclause_seq with (sol := sol) (assumptions := unit :: assumptions).
    + apply andb_prop_elim in H0.
      destruct H0 as [_ H0].
      apply H0.
    + apply H.
    + simpl.
      intros.
      destruct H2.
      * rewrite <- H2.
        apply satisfy_unit_clause with (assumptions := assumptions) (clause := clause).
        -- apply andb_prop_elim in H0.
           destruct H0 as [H0 _].
           apply H0.
        -- apply is_unit.
        -- apply H1.
      * apply H1, H2.
Qed.

Theorem valid_rup_on_negation :
  forall (clause_seq : list Clause) (nogood : Clause),
  Is_true (rup clause_seq (map atomic_not nogood)) ->
  is_valid_nogood nogood clause_seq.
Proof.
  unfold is_valid_nogood.
  intros.
  destruct (satisfies_nogood nogood sol) eqn:Esat ;
  simpl ;
  try apply I.
  apply no_solutions_if_rup with (clause_seq := clause_seq) (assumptions := map atomic_not nogood) (sol := sol).
  - apply H.
  - apply H0.
  - intros.
    apply unsat_nogood with (i := nogood).
    + apply Esat.
    + apply H1.
Qed.
