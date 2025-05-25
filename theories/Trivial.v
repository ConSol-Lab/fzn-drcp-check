Require Import Bool.
Require Import List.

Require Import Checker.ConstraintProblem.
Require Import Checker.Atomic.
Require Import Checker.Nogood.
Require Import Checker.Variable.

Definition construct_trivial_solution (c : Constraint) (fact : Clause) : option Assignment :=
  None.
  (* let naive_mapping := fun v => 
    match find (fun lit =>
      andb
        (eqb (var lit) v)
        (cmp_eqb (comparator lit) not_equal)
    ) fact with
    | Some lit => Some (value lit)
    | None => None
    end
  in
  let all_assigned := forallb 
    (fun v => match naive_mapping v with
              | None => false
              | Some _ => true
              end)
    (affected_variables c)
  in
  if all_assigned then 
    {|
      find_value := fun v =>
      match naive_mapping v with
      | None => lower_bound v
      | Some x => x
      end ;
      consistency_proof := admit
    |}
  else None. *)

