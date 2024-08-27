Require Import Checker.Atomic.

Inductive Step :=
  | inference (premises : list atomic) (conclusion : atomic).

Inductive Conclusion :=
  | unsat
  | optimal (bound : atomic).

Record Proof := 
  {
    steps : list Step;
    conclusion : Conclusion;
  }.
