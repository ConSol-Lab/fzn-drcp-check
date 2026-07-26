From Coq Require Import ZArith NArith String List Bool Lia.
From Coq.Lists Require ListDec.
Import ListNotations.
Open Scope string_scope.

From Checker Require Utility.
From Checker Require Spec.

Module Ast.

Import Utility.Maps.
Import Spec.ConstraintDefinitions.

Inductive const_or_ident : Type :=
  | COIIdent    (name : string)
  | COIConstant (value : Z).

Inductive constr_arg : Type :=
  | CAIdent    (name : string)
  | CAConstant (value : Z)
  | CAArray    (xs : list const_or_ident).

Record constr : Type := mk_constr {
  constr_name : string;
  constr_args : list constr_arg
}.

Inductive decl_item : Type :=
  | DIParConst  (name : string) (value : Z)
  | DIParArray  (name : string) (values : list Z)
  | DIVarScalar (name : string) (domain : IntSet)
  | DIVarArray  (name : string) (elts : list const_or_ident).

Record ast : Type := mk_ast {
  ast_decls       : list decl_item;
  ast_constraints : list constr
}.

End Ast.

Module Lower.

Import Utility.Maps.
Import Spec.ConstraintDefinitions.
Import Ast.

Definition error := string.
Definition result (A : Type) : Type := sum A error.

Local Notation ok  := inl.
Local Notation err := inr.

Local Notation "'let*' x ':=' m 'in' k" :=
  (match m with
   | inl x => k
   | inr e => inr e
   end)
  (at level 200, x pattern, right associativity, only parsing).

Definition from_option {A} (o : option A) (msg : unit -> error) : result A :=
  match o with Some v => ok v | None => err (msg tt) end.

Definition from_dec {P : Prop} (d : {P} + {~P}) (msg : unit -> error) : result P :=
  match d with left p => ok p | right _ => err (msg tt) end.

Fixpoint map_sum_acc {A B : Type} (f : A -> result B)
  (acc : list B) (xs : list A) : result (list B) :=
  match xs with
  | [] => ok (List.rev acc)
  | x :: rest =>
      let* y := f x in map_sum_acc f (y :: acc) rest
  end.

Definition map_sum {A B : Type} (f : A -> result B) (xs : list A)
  : result (list B) := map_sum_acc f [] xs.

Record collected : Type := mk_collected {
  c_constants    : smap.t Z;
  c_const_arrays : smap.t (list Z);
  c_variables    : smap.t IntSet;   (* A map from string to an interval domain *)
  c_var_arrays   : smap.t (list const_or_ident)
}.

Definition empty_collected : collected :=
  mk_collected smap.empty smap.empty smap.empty smap.empty.

Definition add_decl (c : collected) (d : decl_item) : collected :=
  match d with
  | DIParConst name v =>
      mk_collected (smap.add name v (c_constants c))
        (c_const_arrays c) (c_variables c) (c_var_arrays c)
  | DIParArray name xs =>
      mk_collected (c_constants c)
        (smap.add name xs (c_const_arrays c))
        (c_variables c) (c_var_arrays c)
  | DIVarScalar name dom =>
      mk_collected (c_constants c) (c_const_arrays c)
        (smap.add name dom (c_variables c))
        (c_var_arrays c)
  | DIVarArray name elts =>
      mk_collected (c_constants c) (c_const_arrays c) (c_variables c)
        (smap.add name elts (c_var_arrays c))
  end.

Definition collect (ds : list decl_item) : collected :=
  List.fold_left add_decl ds empty_collected.

Definition lookup_constant (c : collected) (ident : string) : result Z :=
  from_option (smap.find ident (c_constants c))
              (fun _ => "Undefined constant '" ++ ident ++ "'.").

Definition arg_to_constant (c : collected) (arg : constr_arg) : result Z :=
  match arg with
  | CAConstant v  => ok v
  | CAArray _     => err "Expected constant, got array literal."
  | CAIdent ident => lookup_constant c ident
  end.

Definition to_constant (c : collected) (coi : const_or_ident) : result Z :=
  match coi with
  | COIConstant v  => ok v
  | COIIdent ident => lookup_constant c ident
  end.

Definition constant_array (c : collected) (arg : constr_arg) : result (list Z) :=
  match arg with
  | CAArray arr   => map_sum (to_constant c) arr
  | CAConstant _  => err "Expected constant array, got constant."
  | CAIdent ident =>
      from_option (smap.find ident (c_const_arrays c))
                  (fun _ => "Constant array '" ++ ident ++ "' does not exist.")
  end.

Definition to_variable (c : collected) (coi : const_or_ident) : Var :=
  match coi with
  | COIConstant v  => const v
  | COIIdent ident =>
      match smap.find ident (c_constants c) with
      | Some v => const v
      | None => var_name ident
      end
  end.

Definition variable_array (c : collected) (arg : constr_arg) : result (list Var) :=
  match arg with
  | CAArray arr   => ok (List.map (to_variable c) arr)
  | CAConstant _  => err "Expected variable array, got constant."
  | CAIdent ident =>
      let* arr := from_option (smap.find ident (c_var_arrays c))
                              (fun _ => "Variable array '" ++ ident ++ "' does not exist.") in
      ok (List.map (to_variable c) arr)
  end.

Definition create_linear (c : collected) (args : list constr_arg)
  : result LinearConstraint :=
  match args with
  | [weights_arg; vars_arg; bound_arg] =>
      let* coefs := constant_array c weights_arg in
      let* vs    := variable_array c vars_arg in
      let* b     := arg_to_constant c bound_arg in
      ok {| l_terms := List.combine coefs vs; l_bound := b |}
  | _ => err "int_lin_le"
  end.

Definition Var_eq_dec : forall x y : Var, {x = y} + {x <> y}.
Proof. decide equality; [apply string_dec | apply Z.eq_dec]. Defined.

Definition create_alldifferent (c : collected) (args : list constr_arg)
  : result AlldifferentConstraint :=
  match args with
  | [vars_arg] =>
      let* vs    := variable_array c vars_arg in
      let* proof := from_dec (ListDec.NoDup_dec Var_eq_dec vs)
                             (fun _ => "alldifferent: argument contains duplicate variables") in
      ok {| diff_variables := vs; diff_unique_vars := proof |}
  | _ => err "alldifferent"
  end.

Definition z_to_N_nonneg (owner : string) (z : Z) : result N :=
  if Z.leb 0 z then ok (Z.to_N z)
  else err (owner ++ ": expected a non-negative integer").

Fixpoint zip_activities (starts : list Var) (durs : list N) (usgs : list N)
  : list Activity :=
  match starts, durs, usgs with
  | s :: ss, d :: ds, u :: us =>
      {| activity_start    := s;
         activity_duration := d;
         activity_usage    := u |} :: zip_activities ss ds us
  | _, _, _ => []
  end.

Definition create_cumulative (c : collected) (args : list constr_arg)
  : result CumulativeConstraint :=
  match args with
  | [start_arg; duration_arg; usage_arg; capacity_arg] =>
      let* starts := variable_array c start_arg in
      let* ds     := constant_array c duration_arg in
      let* us     := constant_array c usage_arg in
      let* cz     := arg_to_constant c capacity_arg in
      let* dns    := map_sum (z_to_N_nonneg "cumulative: duration") ds in
      let* uns    := map_sum (z_to_N_nonneg "cumulative: usage") us in
      let* cap    := z_to_N_nonneg "cumulative: capacity" cz in
      let acts := zip_activities starts dns uns in
      ok {| capacity := cap; activities := acts |}
  | _ => err "cumulative"
  end.

Definition create_constraint (c : collected) (ci : constr) : result Constraint :=
  if String.eqb (constr_name ci) "int_lin_le" then
    let* lc := create_linear c (constr_args ci) in ok (linear_leq lc)
  else if String.eqb (constr_name ci) "int_lin_eq" then
    let* lc := create_linear c (constr_args ci) in ok (linear_eq lc)
  else if String.eqb (constr_name ci) "pumpkin_cumulative" then
    let* cc := create_cumulative c (constr_args ci) in ok (cumulative_c cc)
  else if String.eqb (constr_name ci) "pumpkin_all_different" then
    let* ad := create_alldifferent c (constr_args ci) in ok (alldifferent_c ad)
  else
    err (constr_name ci).

Fixpoint build_constraint_map
  (c : collected) (idx : N) (acc : nmap.t Constraint) (cs : list constr)
  : result (nmap.t Constraint) :=
  match cs with
  | [] => ok acc
  | ci :: rest =>
      let* cn := create_constraint c ci in
      build_constraint_map c (N.succ idx) (nmap.add idx cn acc) rest
  end.

Definition to_constraint_problem (a : ast) : result ConstraintProblem :=
  let c := collect (ast_decls a) in
  let* cs := build_constraint_map c 1%N nmap.empty (ast_constraints a) in
  ok {| constraints := cs; domains := c_variables c |}.

End Lower.
