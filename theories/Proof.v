Require Import Checker.Atomic.
Require Import Checker.Linear.
Require Import Checker.Cumulative.
Require Import Checker.CumulativeCheck.
Require Import Checker.AllDifferentCheck.
Require Import Checker.Nogood.
Require Import Checker.Variable.
Require Import Checker.ConstraintProblem.
Require Import Bool.
Require Import List.
Import Coq.Lists.List.ListNotations.

Inductive InferenceRule :=
  | trivial
  | linear
  | cumulative
  | alldifferent
  .

Inductive Step := 
  | inference (fact : Clause) (hint : list nat) (rule : InferenceRule)
  | nogood (fact : Clause) (database : list Clause).

Inductive Conclusion :=
  | unsat.

Definition conclusion_holds_for (csp : ConstraintProblem) (conclusion : Conclusion) (sol : Assignment) :=
  match conclusion with
  | unsat => negb (satisfies_problem csp sol)
  end.

Definition conclusion_holds (csp : ConstraintProblem) (conclusion : Conclusion) :=
  forall (sol : Assignment), Is_true (conclusion_holds_for csp conclusion sol).

Record Proof := 
  {
    steps : list Step;
    conclusion : Conclusion;
  }.

Definition validate_inference (fact : Clause) (hint : list Constraint) (rule : InferenceRule) :=
  match rule with
  | trivial =>
      existsb
        (fun c => false)
        hint
  | linear =>
      match hint with
      | [linear_leq c] => linear_checker fact c
      | _ => false
      end
  | cumulative =>
      match hint with
      | [cumulative_c c] => cumulative_checker fact c
      | _ => false
      end
  | alldifferent =>
    match hint with
    | [alldifferent_c c] => alldifferent_checker fact c
    | _ => false
    end
  end.

Lemma validate_inference_soundness : forall (fact : Clause) (hint : list Constraint) (rule : InferenceRule) (sol : Assignment),
  (forall (c : Constraint), In c hint -> Is_true(satisfies_constraint c sol)) ->
  Is_true (validate_inference fact hint rule) -> 
  Is_true (satisfies_nogood fact sol).
Proof.
  intros fact hint rule sol Hsat Hvalid.
  unfold validate_inference in Hvalid.
  destruct rule; simpl in Hvalid.
  - intros.
    apply Is_true_eq_true, existsb_exists in Hvalid.
    destruct Hvalid as [x [Hin Hcontra]].
    discriminate Hcontra.
  - destruct hint as [|c [|c0 l]] eqn:Ehint ; try destruct c eqn:Ec ; try easy.
    simpl in Hsat.
    apply Is_true_eq_true, linear_inference_checker_correct in Hvalid.
    unfold is_valid_linear_inference in Hvalid.
    specialize (Hvalid sol).
    apply Hvalid.
    specialize (Hsat c).
    rewrite Ec in Hsat.
    simpl in Hsat.
    apply Hsat.
    left.
    reflexivity.
  - destruct hint as [|c [|c0 l]] eqn:Ehint ; try destruct c eqn:Ec ; try easy.
    (* apply cumulative_checker_valid with (constr := constraint); try assumption.
    specialize (Hsat (cumulative_c constraint)).
    apply Hsat.
    simpl. left. reflexivity. *)
  - destruct hint as [|c [|c0 l]] eqn:Ehint ; try destruct c eqn:Ec ; try easy.
    specialize (Hsat (alldifferent_c constraint)).
    apply Is_true_eq_left.
    apply alldifferent_checker_valid with (constr := constraint); apply Is_true_eq_true; try assumption.
    apply Hsat.
    simpl. left. reflexivity.
Qed.


Fixpoint validate_kb (csp : ConstraintProblem) (s : list Step) (c : Conclusion) (inferences : list Clause) (nogoods : list Clause) :=
  match s with
  | nil =>
      match c with
      | unsat =>
          let is_empty := fun x => match x with
                                   | nil => true
                                   | _ => false
                                   end in
          orb (existsb is_empty nogoods) (existsb is_empty inferences)
      end
  | step :: rest =>
      match step with
      | inference fact hint rule => 
          let extract_constraint : nat -> list Constraint := fun index => 
            match nth_error (constraints csp) index with
            | Some found_cons => [found_cons]
            | None => []
            end
          in
          let constraints := flat_map extract_constraint hint in
          if validate_inference fact constraints rule
          then validate_kb csp rest c (fact :: inferences) nogoods
          else false
      | nogood fact database =>
          if forallb (fun f =>
            let is_same_fact := fun g => Checker.Nogood.eqb f g in
            let has_nogood := existsb is_same_fact nogoods in
            let has_inference := existsb is_same_fact inferences in
            has_nogood || has_inference
          ) database && rup database (map atomic_not fact)
          then validate_kb csp rest c nil (fact :: nogoods)
          else false
      end
  end.

Definition validate (csp : ConstraintProblem) (p : Proof) :=
  validate_kb csp (steps p) (conclusion p) nil nil.


Lemma if_else_rewrite : forall (b : bool), (if b then false else false) = false. 
Proof.
  intros.
  destruct b ; reflexivity.
Qed.

Lemma if_else_false : forall (a b : bool), (if b then a else false) = a && b.
Proof.
  intros.
  destruct a, b ; reflexivity.
Qed.

Lemma soundness_with_kb : forall (csp : ConstraintProblem) (s : list Step) (c : Conclusion) (inferences : list Clause) (nogoods : list Clause),
  Is_true (validate_kb csp s c inferences nogoods) ->
  (forall (sol : Assignment),
    Is_true (satisfies_problem csp sol) ->
    forall (f : Clause), In f inferences \/ In f nogoods -> Is_true(satisfies_nogood f sol)) ->
  conclusion_holds csp c.
Proof.
  (* Induction by proof length *)
  intros csp s c inferences nogoods Hvalid Hsat.
  generalize dependent nogoods.
  generalize dependent inferences.
  induction s as [|head_step tail_steps IH] ; simpl.
  - (* Base case: empty proof *)
    intros.
    destruct c eqn:Ec.
    apply orb_prop_elim in Hvalid.
    (* Show that an empty clause is in the KB,
      which cannot be satisfied by definition *)
    destruct Hvalid as [Hvalid|Hvalid] ; 
    apply Is_true_eq_true, existsb_exists in Hvalid ;
    destruct Hvalid as [x [Hin Hnil]] ;
    destruct x ;
    try easy ;
    unfold conclusion_holds ;
    intros sol ;
    simpl ;
    destruct (satisfies_problem csp sol) eqn:Esat ;
    simpl ;
    try easy ;
    apply Is_true_eq_left in Esat ;
    specialize (Hsat sol Esat nil) as Hsat_empty ;
    simpl in Hsat_empty ;
    apply Hsat_empty.
    + right.
      apply Hin.
    + left.
      apply Hin.
  - (* Induction step: show that (n+1) steps are valid against any KB
    if the last n steps are valid against any KB. *)
    intros.
    destruct head_step eqn:Ehead.
    + (* If the next step is an inference, use the inference checker correctness
         and the induction hypothesis after adding the fact to the inferences list *)
      apply IH with (inferences := fact :: inferences) (nogoods := nogoods).
      * (* The proof tail is valid *)
        destruct (validate_kb csp tail_steps c (fact :: inferences) nogoods) ; try easy.
        simpl.
        rewrite if_else_rewrite in Hvalid.
        contradiction.
      * (* Any feasible solution satisfies the KB. *)
        intros sol Hsat_sol f.
        specialize (Hsat sol Hsat_sol f).
        intros Hin.
        destruct Hin as [Hin_inf | Hin_nogood].
        -- (* Show that the newly added inference is satisfied by
           any feasible solution since it is derived by a checker from the model constraints. *)
           simpl in Hin_inf.
           destruct Hin_inf as [Heq | Hin_inf].
           ++ rewrite if_else_false in Hvalid.
              apply andb_prop_elim in Hvalid.
              destruct Hvalid as [_ Hforall].
              remember (flat_map (fun index =>
              match nth_error (constraints csp) index with
              | Some found_cons => [found_cons]
              | None => []
              end
              ) hint) as hint_cons.
              apply validate_inference_soundness with (rule := rule) (hint := hint_cons) ;
              try rewrite <- Heq ;
              try easy.
              intros hint_c Hin_c.
              unfold satisfies_problem in Hsat_sol.
              apply Is_true_eq_true in Hsat_sol.
              rewrite forallb_forall in Hsat_sol.
              specialize (Hsat_sol hint_c).
              apply Is_true_eq_left, Hsat_sol.
              rewrite Heqhint_cons in Hin_c.
              apply in_flat_map in Hin_c.
              destruct Hin_c as [index [_ Hin_by_index]].
              destruct (nth_error (constraints csp) index) eqn:Elookup; try easy.
              simpl in Hin_by_index.
              destruct Hin_by_index ; try contradiction.
              apply nth_error_In in Elookup.
              rewrite H in Elookup.
              apply Elookup.
           ++ apply Hsat.
              left.
              apply Hin_inf.
        -- (* All nogoods are copied from the previous iteration *)
           apply Hsat.
           right.
           apply Hin_nogood.
    + (* If the next step is a nogood, do the same but use RUP correctness this time *)
      apply IH with (inferences := nil) (nogoods := fact :: nogoods).
      * (* The proof tail is valid *)
        destruct (validate_kb csp tail_steps c nil (fact :: nogoods)) ; try easy.
        simpl.
        rewrite if_else_rewrite in Hvalid.
        contradiction.
      * (* Any feasible solution satisfies the KB. *)
        simpl.
        intros sol Hsat_sol f.
        specialize (Hsat sol Hsat_sol f) as Hsat_f.
        intros Hin.
        destruct Hin as [Hcontra | [Heq | Hin_nogood]] ; try contradiction.
        -- (* Show that the newly added nogood is satisfied by any feasible solution
              since it is derived by RUP from the KB facts. *)
           destruct (rup database (map atomic_not fact)) eqn:Erup.
           ++ apply Is_true_eq_left, valid_rup_on_negation in Erup.
              unfold is_valid_nogood in Erup.
              rewrite Heq in Erup.
              apply Erup.
              unfold satisfies_all_nogoods.
              apply Is_true_eq_left, forallb_forall.
              intros db Hdb_in.
              apply Is_true_eq_true, Hsat ; try easy.
              rewrite if_else_false in Hvalid.
              apply andb_prop_elim in Hvalid.
              destruct Hvalid as [_ Hforall].
              rewrite andb_true_r in Hforall.
              apply Is_true_eq_true in Hforall.
              rewrite forallb_forall in Hforall.
              specialize (Hforall db Hdb_in).
              apply orb_prop in Hforall.
              destruct Hforall as [Hforall | Hforall] ;
              apply existsb_exists in Hforall ;
              destruct Hforall as [db_ex [Hxin Hxeqb]] ;
              apply Is_true_eq_left, Nogood.eqb_eq in Hxeqb ;
              rewrite <- Hxeqb in Hxin.
              ** right.
                 apply Hxin.
              ** left.
                 apply Hxin.
           ++ (* No need to handle inferences, as there will be none *)
              rewrite andb_false_r in Hvalid.
              contradiction.
        -- (* All the other nogoods are copied *)
           specialize (Hsat sol).
           apply Hsat ; try easy.
           right.
           apply Hin_nogood.
Qed.

Lemma soundness : forall (csp : ConstraintProblem) (p : Proof),
  Is_true (validate csp p) -> conclusion_holds csp (conclusion p).
Proof.
  unfold validate.
  intros csp p Hvalid.
  apply soundness_with_kb with (s := steps p) (c := conclusion p) (nogoods := nil) (inferences := nil).
  + apply Hvalid.
  + simpl.
    intros sol Hsat f Hcontra.
    exfalso.
    destruct Hcontra ; contradiction.
Qed.

Lemma completeness : forall (csp : ConstraintProblem) (c : Conclusion),
  conclusion_holds csp c -> exists (p : Proof), Is_true (validate csp p).
Proof.
Admitted.

Theorem correctness : forall (csp : ConstraintProblem) (c : Conclusion),
  conclusion_holds csp c <-> exists (p : Proof), Is_true (validate csp p).
Proof.
  split.
  - intros Hconcl.
    apply completeness with (c := c), Hconcl.
  - intros Hexist.
    destruct Hexist as [p Hval].
    specialize (soundness csp p Hval).
    unfold conclusion_holds.
    intros Hproof_concl.
    (* TODO This proof requires a more careful wording for optimality conclusions *)
    destruct (conclusion p) eqn:Eproof ;
    destruct c eqn:Ec.
    apply Hproof_concl.
Qed.
