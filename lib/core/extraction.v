From Checker Require Import Spec.
From Checker Require Import Checker.

Set Warnings Append "-extraction-opaque-accessed".

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.
Require Import ExtrOcamlZBigInt.

Extraction Language OCaml.
Extraction Blacklist List String Nat.

Set Extraction Output Directory ".".

Extraction "checker" 
  Spec.ConstraintDefinitions.ConstraintProblem
  Checker.InferenceRule
  Checker.validate.
