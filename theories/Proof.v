Require Import Checker.Atomic.
Require Import Checker.Linear.
Require Import Checker.Nogood.
Require Import Checker.Variable.
Require Import Bool.
Require Import List.

Inductive InferenceRule :=
  | linear (constraint : LinearConstraint)
  | rup_inf (database : list Clause).

Record Step := 
  {
    premises : list Atomic ;
    consequent : Atomic ;
    inference_rule : InferenceRule ;
  }.

Definition clausal_form (step : Step) : Clause :=
  (consequent step) :: (map atomic_not (premises step)).

Definition satisfies_impl (x : Step) (sol : Assignment) :=
  orb
  (test_atomic_assignment (consequent x) sol)
  (existsb (fun p : Atomic => negb (test_atomic_assignment p sol)) (premises x)).

Theorem clausal_form_equiv : forall (step : Step) (sol : Assignment),
  Is_true (satisfies_impl step sol) <-> Is_true (satisfies_nogood (clausal_form step) sol).
Proof.
  intros.
  split.
  - intros Himpl.
    destruct (test_atomic_assignment (consequent step) sol) eqn:Eatomic ;
    unfold clausal_form ;
    unfold test_atomic_assignment in Eatomic ;
    simpl ;
    rewrite Eatomic ;
    try reflexivity.
    unfold satisfies_impl in Himpl.
    unfold test_atomic_assignment in Himpl.
    rewrite Eatomic in Himpl.
    simpl in Himpl.
    apply Is_true_eq_true, existsb_exists in Himpl.
    generalize dependent sol.
    induction (premises step) as [|clause_neg_head clause_neg IHclause] ; simpl ; intros.
    + destruct Himpl as [_ [contra _]].
      apply contra.
    + destruct Himpl as [x [[Heq | Hin] Hneg]].
      * rewrite Heq, atomic_not_involution, <- atomic_not_variable_eq, Hneg.
        reflexivity.
      * destruct (test_atomic (atomic_not clause_neg_head) (find_value sol (var (atomic_not clause_neg_head)))) eqn:Eif ;
        try reflexivity.
        apply IHclause.
        -- exists x.
           split.
           ++ apply Hin.
           ++ apply Hneg.
        -- apply Eatomic.
  - intros Hnogood.
    unfold satisfies_impl.
    destruct (test_atomic_assignment (consequent step) sol) eqn:Eatomic ;
    unfold clausal_form in Hnogood ;
    simpl in Hnogood ;
    unfold test_atomic_assignment in Eatomic ;
    rewrite Eatomic in Hnogood ;
    try reflexivity ;
    simpl.
    apply Is_true_eq_left, existsb_exists.
    generalize dependent sol.
    induction (premises step) as [|clause_neg_head clause_neg IHclause] ;
    simpl ; intros ;
    try contradiction.
    destruct (test_atomic (atomic_not clause_neg_head) (find_value sol (var (atomic_not clause_neg_head)))) eqn:Eif .
    + exists clause_neg_head.
      split.
      * left.
        reflexivity.
      * unfold test_atomic_assignment.
        rewrite <- atomic_not_involution, atomic_not_variable_eq.
        apply Eif.
    + assert (Hexists: exists x : Atomic, In x clause_neg /\ negb (test_atomic_assignment x sol) = true). {
        apply IHclause.
        - apply Hnogood.
        - apply Eatomic.
      }
      destruct Hexists as [x [Hin Hnot]].
      exists x.
      split.
      * right.
        apply Hin.
      * apply Hnot.
Qed.
    
Inductive Conclusion :=
  | unsat
  | optimal (bound : Atomic).

Definition satisfies_conclusion (c : Conclusion) (sol : Assignment) :=
  match c with
  | unsat => false
  | optimal bound => test_atomic_assignment bound sol
  end.

Record Proof := 
  {
    steps : list Step;
    conclusion : Conclusion;
  }.
