open Drcpcheck_core.Checker.Maps
open Drcpcheck_core.Checker.ConstraintDefinitions
open Big_int_Z

exception UnknownConstraintError of string
exception InvalidArgumentsError of string

type const_or_ident = Ident of string | Constant of big_int

type constr_arg =
  | Ident of string
  | Constant of big_int
  | Array of const_or_ident list

type constr = { constr_name : string; constr_args : constr_arg list }

type ast = {
  ast_constants : big_int Coq_smap.t;
  ast_constant_arrays : big_int list Coq_smap.t;
  (* A map from string to an interval domain *)
  ast_variables : coq_IntSet Coq_smap.t;
  ast_variable_arrays : const_or_ident list Coq_smap.t;
  ast_constraints : constr list;
}

let arg_to_constant (parsed_ast : ast) (arg : constr_arg) : big_int =
  match arg with
  | Constant c -> c
  | Array _ ->
      raise (InvalidArgumentsError "Expected constant, got array literal.")
  | Ident ident -> (
      match Coq_smap.find ident parsed_ast.ast_constants with
      | Some c -> c
      | None ->
          raise
            (InvalidArgumentsError
               (Printf.sprintf "Undefined constant '%s'." ident)))

let to_constant (parsed_ast : ast) (c_or_i : const_or_ident) : big_int =
  match c_or_i with
  | Constant c -> c
  | Ident ident -> (
      match Coq_smap.find ident parsed_ast.ast_constants with
      | Some c -> c
      | None ->
          raise
            (InvalidArgumentsError
               (Printf.sprintf "Undefined constant '%s'." ident)))

let constant_array (parsed_ast : ast) (arg : constr_arg) : big_int list =
  match arg with
  | Array arr -> List.map (to_constant parsed_ast) arr
  | Constant _ ->
      raise (InvalidArgumentsError "Expected constant array, got constant.")
  | Ident ident -> (
      match Coq_smap.find ident parsed_ast.ast_constant_arrays with
      | Some arr -> arr
      | None ->
          raise
            (InvalidArgumentsError
               (Printf.sprintf "Constant array '%s' does not exist." ident)))

let to_variable (parsed_ast : ast) (c_or_i : const_or_ident) : coq_Var =
  match c_or_i with
  | Constant c -> Coq_const c
  | Ident ident -> (
      match Coq_smap.find ident parsed_ast.ast_constants with
      | Some c -> Coq_const c
      | None -> Coq_var_name ident)

let variable_array (parsed_ast : ast) (arg : constr_arg) : coq_Var list =
  match arg with
  | Array arr -> List.map (to_variable parsed_ast) arr
  | Constant _ ->
      raise (InvalidArgumentsError "Expected variable array, got constant.")
  | Ident ident -> (
      match Coq_smap.find ident parsed_ast.ast_variable_arrays with
      | Some arr -> List.map (to_variable parsed_ast) arr
      | None ->
          raise
            (InvalidArgumentsError
               (Printf.sprintf "Variable array '%s' does not exist." ident)))

let create_linear parsed_ast args =
  match args with
  | [ weights_arg; vars_arg; bound_arg ] ->
      {
        l_terms =
          List.combine
            (constant_array parsed_ast weights_arg)
            (variable_array parsed_ast vars_arg);
        l_bound = arg_to_constant parsed_ast bound_arg;
      }
  | _ -> raise (InvalidArgumentsError "int_lin_le")

let create_cumulative parsed_ast args =
  match args with
  | [ start_arg; duration_arg; usage_arg; capacity_arg ] ->
      {
        capacity = arg_to_constant parsed_ast capacity_arg;
        activities =
          List.map
            (fun ((s, d), u) -> {
               activity_start = s;
               activity_duration = d;
               activity_usage = u;
             })
            (List.combine
              (List.combine
                (variable_array parsed_ast start_arg)
                (constant_array parsed_ast duration_arg))
              (constant_array parsed_ast usage_arg));
      }
  | _ -> raise (InvalidArgumentsError "cumulative")

let create_constraint parsed_ast c =
  match c.constr_name with
  | "int_lin_le" -> Coq_linear_leq (create_linear parsed_ast c.constr_args)
  | "int_lin_eq" -> Coq_linear_eq (create_linear parsed_ast c.constr_args)
  | "pumpkin_cumulative" -> Coq_cumulative_c (create_cumulative parsed_ast c.constr_args)
  | unknown -> raise (UnknownConstraintError unknown)

let accumulate_constraints parsed_ast (map, idx) c =
  let new_map = Coq_nmap.add idx (create_constraint parsed_ast c) map in
  (new_map, succ_big_int idx)

let to_constraint_problem parsed_ast =
  {
    domains = parsed_ast.ast_variables;
    constraints =
      (let map, _ =
         List.fold_left
           (accumulate_constraints parsed_ast)
           (Coq_nmap.empty, succ_big_int zero_big_int)
           parsed_ast.ast_constraints
       in
       map);
  }
