Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

From Coq Require Extraction.

From Checker Require Import StringEqual.

Extraction Language OCaml.
Set Extraction Output Directory ".".

Extraction "myproject_extracted" strings_are_equal.
