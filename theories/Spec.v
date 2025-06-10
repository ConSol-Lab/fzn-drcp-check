Require Import ZArith.
Require Import Bool.
Require Import String.
Require Import List.
(* Require Import Checker.Proof (validate, step_soundness). *)
(* Require Import Checker.ConstraintProblem (entailed_addition). *)
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

  Record LinearConstraint :=
    {
      l_terms : list (Z * string);
      l_bound : Z;
    }.

  Record ActivityDefine := mkActDef
                             {
                               def_x : string;
                               def_p : N;
                               def_u : N;
                             }.

  Record CumulativeConstraint :=
    {
      capacity: N;
      activities: list ActivityDefine;
      valid_p_times : forall a, In a activities -> (a.(def_p) >= 1)%N;
      acts_nodup : NoDup (map def_x activities)
    }.

  Inductive Constraint :=
  | linear_leq (constraint : LinearConstraint)
  | cumulative_c (constraint : CumulativeConstraint)
  | fact_c (constraint : ProofFacts.ProofFact)
  (* TODO | alldifferent_c (constraint : AllDifferent.AllDifferentConstraint) *)
  .

  Fixpoint evaluate_linear (x : list (Z * string)) (sol : string -> Z) : Z :=
    match x with
    | nil => 0
    | cons (coef, v) xs => coef * (sol v) + (evaluate_linear xs sol)
    end.

  Definition Linear (c : LinearConstraint) (a : string -> Z) : Prop :=
    evaluate_linear (c.(l_terms)) a <= c.(l_bound).

  Record Activity := mkAct {
                         a_name : string;
                         start : Z;
                         p_time : N;
                         usage : N;
                       }.

  Definition activity_from_a_def (a : string -> Z) (act : ActivityDefine) : Activity :=
    match act with
    | mkActDef x p u =>
        mkAct x (a x) p u
    end.

  Definition activity_list_inner (l : list ActivityDefine) (a : string -> Z) : list Activity :=
    map (activity_from_a_def a) l
  .

  Definition activity_list (c : CumulativeConstraint) (a : string -> Z) : list Activity :=
    activity_list_inner c.(activities) a
  .

  Definition is_active_at (start_time : Z) (p_time : N) (t : Z) : bool :=
    let end_time := (start_time + (Z.of_N p_time)) in
    (start_time <=? t) && (t <? end_time).

  Definition activities_at_t (l : list Activity) (t : Z) : list Activity :=
    filter (fun a => is_active_at a.(start) a.(p_time) t) l
  .

  Open Scope N_scope.
  Fixpoint n_sum_rec (l : list N) (current : N) : N :=
    match l with
    | nil => current
    | n :: l' => n_sum_rec l' (current + n)
    end.

  Definition n_sum (l : list N) : N :=
    n_sum_rec l N0.

  Definition xn_sum (l : list (string * N)) : N :=
    n_sum (map snd l).


  Definition act_to_xn (a : Activity) : (string * N) :=
    (a.(a_name), a.(usage)).

  Definition usage_sum (l : list Activity) : N :=
    xn_sum (map act_to_xn l).

  Definition Cumulative (constraint : CumulativeConstraint) (a : string -> Z) : Prop :=
    let activities := activity_list constraint a in
    forall t,
      usage_sum (activities_at_t activities t) <= constraint.(capacity).

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

  Definition CPProof := (list ProofStage)%type.

  Import Coq.Lists.List.ListNotations.
  Fixpoint conclusion (p : CPProof) :=
    match p with
    | [] => None
    | [stage] => Some (stage.(s_conclusion))
    | _ :: p' => conclusion p'
    end.

  Definition conclusion_holds
    (csp : ConstraintDefinitions.ConstraintProblem)
    (fact : ProofFacts.ProofFact) :=
    forall (sol : string -> Z),
      ConstraintDefinitions.satisfies_problem csp sol ->
      ProofFacts.fact_valid sol fact.

  (* Theorem soundness : forall *)
  (*     (csp : ConstraintDefinitions.ConstraintProblem) *)
  (*     (p : CPProof) *)
  (*     (fact : ProofFacts.ProofFact), *)
  (*     conclusion p = Some fact -> *)
  (*     Is_true (validate csp p) -> *)
  (*     conclusion_holds csp fact. *)
  (* Proof. *)
  (*   intros csp p fact Hconcl Hvalid. *)
  (*   generalize dependent csp. *)
  (*   (* Induction by proof length; base case p = nil is vacuously true. *) *)
  (*   induction p as [|stage] ; try discriminate. *)
  (*   intros csp Hvalid. *)
  (*   destruct p eqn:Ep. *)
  (*   (* The proof has a single stage; use stage checker soundness directly *)
  (*    after appropriately unpacking all variables *) *)
  (*   { *)
  (*     inversion Hconcl as [Hconcl']. *)
  (*     apply step_soundness with (p := nil). *)
  (*     exact Hvalid. *)
  (*   } *)
  (*   (* Use the induction hypothesis for the remainder of the proof and *)
  (*    the mutated CSP problem instance *) *)
  (*   assert (Hholds: conclusion_holds csp (stage.(s_conclusion))). { *)
  (*     apply step_soundness with (p := p0 :: l). *)
  (*     exact Hvalid. *)
  (*   } *)
  (*   unfold conclusion_holds. *)
  (*   apply entailed_addition with *)
  (*     (fact := stage.(s_conclusion)) *)
  (*     (index := stage.(s_conclusion_index)) ; *)
  (*     try exact Hholds. *)
  (*   remember (add (stage.(s_conclusion_index)) (stage.(s_conclusion)) csp) as csp'. *)
  (*   unfold conclusion_holds in IHp. *)
  (*   apply IHp with (csp := csp'). *)
  (*   + (* Proof conclusion stays the same, as it is not empty. *) *)
  (*     easy. *)
  (*   + (* Checker reports true on the upcoming proof prefix *)
  (*      after mutating the CSP *) *)
  (*     remember (p0 :: l) as q. *)
  (*     unfold validate in Hvalid. *)
  (*     rewrite <- Heqcsp' in Hvalid. *)
  (*     destruct (validate_proof_stage (hydrate csp stage)) ; try easy. *)
  (* Qed. *)

End Proofs.
