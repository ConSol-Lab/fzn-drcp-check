Require Import ZArith.
Require Import Bool.
Require Import String.
Require Import List.
Require Checker.Utility.
Import Checker.Utility.Maps.

Module ProofFacts.
  Open Scope Z_scope.

  Inductive AtomicComparator :=
  | less_equal
  | greater_equal
  | equal
  | not_equal.

  Record Atomic := mkAtm {
                       atm_cmp : AtomicComparator;
                       atm_val : Z
                     }.

  (** This definition provides the semantics of an atomic constraint. Again, `y` is some value, but think of it as the value of some variable. *)
  Definition atomic_holds (y : Z) (a : Atomic) :=
    match a.(atm_cmp) with
    | less_equal => y <= a.(atm_val)
    | greater_equal => y >= a.(atm_val)
    | equal => y = a.(atm_val)
    | not_equal => y <> a.(atm_val)
    end.

  (** We use a simple pair instead of a Record since it is just two things. *)
  Definition BoundAtomic := (string * Atomic)%type.

  Definition bound_atomic_holds (assignment : string -> Z) (atom : BoundAtomic) :=
    match atom with
    | (x, atom) =>
        atomic_holds (assignment x) atom
    end.

  (** A fact is a set of premises and a consequent. If the consequent is None, it represents a nogood. *)
  Record ProofFact := mkFact {
                          i_premises : list BoundAtomic;
                          i_consequent : option BoundAtomic
                        }.

  Definition valid_atoms (sol : string -> Z) (atoms : list BoundAtomic) :=
    forall x a, In (x, a) atoms -> atomic_holds (sol x) a.

  (** If the premises hold for the assignment, then the consequent holds *)
  Definition fact_valid (assignment : string -> Z) (fact : ProofFact) :=
    valid_atoms assignment fact.(i_premises)
    ->
      match fact.(i_consequent) with
      | None => False
      | Some consequent => bound_atomic_holds assignment consequent
      end.
End ProofFacts.

Module ConstraintDefinitions.
  Open Scope Z_scope.

  Inductive Var :=
  | var_name (ident : string)
  | const (value : Z)
  .

  Definition Assignment := string -> Z.

  Definition evaluate (var : Var) (sol : Assignment) : Z :=
    match var with
    | var_name ident => sol ident
    | const value => value
    end.

  Record LinearConstraint :=
    {
      l_terms : list (Z * Var);
      l_bound : Z;
    }.

  Record Activity := mkActDef {
    activity_start : Var;
    activity_duration : N;
    activity_usage : N;
  }.

  Record CumulativeConstraint :=
    {
      capacity: N;
      activities: list Activity;
      valid_p_times : forall a, In a activities -> (a.(activity_duration) >= 1)%N;
      acts_nodup : NoDup (map activity_start activities)
    }.

  Inductive Constraint :=
  | linear_leq (constraint : LinearConstraint)
  | cumulative_c (constraint : CumulativeConstraint)
  | fact_c (constraint : ProofFacts.ProofFact)
  (* TODO | alldifferent_c (constraint : AllDifferent.AllDifferentConstraint) *)
  .

  Definition evaluate_term (sol : Assignment) (term : Z * Var) : Z :=
    match term with
    | (coef, var) => coef * (evaluate var sol)
    end.

  Definition evaluate_linear (sol : Assignment) (terms : list (Z * Var)) : Z :=
    fold_left (fun acc term => acc + evaluate_term sol term) terms Z.zero.

  Definition Linear (c : LinearConstraint) (a : string -> Z) : Prop :=
    evaluate_linear a (c.(l_terms)) <= c.(l_bound).

  Definition is_active_at (sol : Assignment) (timepoint : Z) (activity : Activity) : bool :=
    let start_time := evaluate activity.(activity_start) sol in
    let duration := Z.of_N activity.(activity_duration) in
    let end_time := Z.add start_time duration in
    Z.leb start_time timepoint && Z.ltb timepoint end_time.

  Definition usage_at_timepoint (sol : Assignment) (timepoint : Z) (activities : list Activity) : N :=
    let active_activities := filter (is_active_at sol timepoint) activities in
    let usages := List.map activity_usage activities in
    fold_left N.add usages N.zero.

  Definition Cumulative (constraint : CumulativeConstraint) (sol : Assignment) : Prop :=
    forall t,
      N.le (usage_at_timepoint sol t constraint.(activities)) constraint.(capacity).

  Open Scope Z_scope.
  Definition satisfies_constraint (c : Constraint) (sol : string -> Z) :=
    match c with
    | linear_leq c => Linear c sol
    | cumulative_c c => Cumulative c sol
    | fact_c c => ProofFacts.fact_valid sol c
    end.

  Definition ConstraintProblem := nmap.t Constraint.

  Definition satisfies_problem (csp : ConstraintProblem) (sol : string -> Z) :=
    forall index c, nmap.MapsTo index c csp -> satisfies_constraint c sol.
End ConstraintDefinitions.

Module Proofs.
  Inductive InferenceRule :=
  | fact_equiv
  | linear
  (* TODO This is not _cumulative_ inference rule; look up the canonical naming *)
  | cumulative
  (* | alldifferent *)
  .

  Inductive Step :=
  | inference (fact : ProofFacts.ProofFact) (hint : list N) (rule : InferenceRule)
  | nogood (fact : ProofFacts.ProofFact) (chain : list N).

  Record IndexedInference := {
      iinf_index : N ;
      iinf_fact : ProofFacts.ProofFact ;
      iinf_hint : list N ;
      iinf_rule : InferenceRule
    }.

  Record ProofStage := {
      s_inferences : list IndexedInference ;
      s_chain : list N ;
      s_conclusion : ProofFacts.ProofFact ;
      s_conclusion_index : N
    }.

  Record CPProof := {
      proof_stages : list ProofStage ;
      conclusion : ProofFacts.ProofFact
    }.

  Import Coq.Lists.List.ListNotations.

  Definition fact_holds
    (csp : ConstraintDefinitions.ConstraintProblem)
    (fact : ProofFacts.ProofFact) :=
    forall (sol : string -> Z),
      ConstraintDefinitions.satisfies_problem csp sol ->
      ProofFacts.fact_valid sol fact.

  Definition checker_sound (checker_impl : ConstraintDefinitions.ConstraintProblem -> CPProof -> bool) : Prop :=
    forall csp p, checker_impl csp p = true -> fact_holds csp (p.(conclusion)).
End Proofs.
