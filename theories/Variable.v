Require Import List.
Require Import String.
Require Import ZArith.

Definition non_zero_Z := { n : nat | n <> 0 }.

Record IntervalVariable := 
  {
    name : string;
    lower_bound : Z;
    size: non_zero_Z;
    upper_bound : Z := lower_bound + Z.of_nat (proj1_sig size)
  }.

Inductive Var :=
  | interval (var : IntervalVariable).

Compute upper_bound {| name := "a"; lower_bound := 1; size := exist _ 5 (Nat.neq_succ_0 4) |}.

