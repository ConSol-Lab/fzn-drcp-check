Require Import Checker.Atomic.

Inductive Step :=
  | inference (premises : list Atomic) (conclusion : Atomic).

Inductive Conclusion :=
  | unsat
  | optimal (bound : Atomic).

Record Proof := 
  {
    steps : list Step;
    conclusion : Conclusion;
  }.
