Require Import Checker.Variable.
Require Import Checker.Atomic.

Record Inference :=
  {
    premises : list atomic;
    conclusion : list atomic;
  }.
