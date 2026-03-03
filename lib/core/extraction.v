From Checker Require Import Spec.
From Checker Require Import Checker.
From Checker Require Import CheckerStreamed.
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

Extract Inductive Utility.LazyLists.llist => "Lazy.lazylist" [ "Lazy.LNil" "Lazy.Single" "Lazy.Cons" "Lazy.Thunk" ].

Separate Extraction
  Spec.ConstraintDefinitions.ConstraintProblem
  Checker.validate
  Checker.default_rules
  CheckerStreamed.validate
  CheckerStreamed.default_rules
  Ast.mk_ast
  Parser.model
  Lower.to_constraint_problem
.
