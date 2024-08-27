Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

From Coq Require Extraction.

From Checker Require Import ConstraintProblem.
From Checker Require Import Proof.
From Checker Require Import ProofChecker.

Extraction Language OCaml.
Set Extraction Output Directory ".".

Extraction "checker_extracted" Checker.ConstraintProblem.ConstraintProblem Checker.Proof.Proof proof_checker.
