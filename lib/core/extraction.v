From Checker Require Import Spec.

Set Warnings Append "-extraction-opaque-accessed".

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.
Require Import ExtrOcamlZBigInt.

Extraction Language OCaml.
Extraction Blacklist List String Nat.

Set Extraction Output Directory ".".

Extraction "checker" 
  Spec.ConstraintDefinitions.ConstraintProblem
  Spec.Proofs.CPProof.
