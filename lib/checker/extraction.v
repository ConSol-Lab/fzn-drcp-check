Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

From Coq Require Extraction.

From Checker Require Import ConstraintProblem.
From Checker Require Import Proof.

Extraction Language OCaml.
Set Extraction Output Directory ".".

Extraction "checker" 
  Checker.ConstraintProblem.ConstraintProblem 
  Checker.Proof.CPProof 
  validate.
