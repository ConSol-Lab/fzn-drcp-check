From Checker Require Import Spec.
From Checker Require Import Checker.

From Checker Require Import Utility.
From FlatZinc Require Import Ast.
From FlatZinc Require Import Parser.

Set Warnings Append "-extraction-opaque-accessed".

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.
Require Import ExtrOcamlZBigInt.
Require Import ExtrOcamlNatBigInt.

Extraction Language OCaml.
Extraction Blacklist List String Nat.

Set Extraction Output Directory ".".

Extract Constant OrdersEx.String_as_OT.compare => "fun s1 s2 -> let cmp = String.compare s1 s2 in if cmp < 0 then Lt else if cmp = 0 then Eq else Gt".

Extract Constant BinNat.N.eqb => "Big_int_Z.eq_big_int".
Extract Constant BinNat.N.eq_dec => "Big_int_Z.eq_big_int".
Extract Constant List.map => "fun f l -> List.rev (List.rev_map f l)".
Extract Constant List.rev => "List.rev".
Extract Constant List.rev_append => "List.rev_append".

Extract Constant List.length => "fun l -> Big_int_Z.big_int_of_int (List.length l)".

Extraction Inline ProofStream.
Extraction Inline Checker.SequentialCheckerImpl.step Checker.SequentialCheckerImpl.finalize.

Extraction "checker"
  Spec.ConstraintDefinitions.ConstraintProblem
  Checker.DefaultRules
  Checker.StreamingChecker
  Checker.SequentialChecker
  Ast.mk_ast
  Parser.model
  Lower.to_constraint_problem
.
