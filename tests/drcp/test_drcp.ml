open Drcpcheck_core.Checker.ConstraintDefinitions
open Drcpcheck_core.Checker.Maps
open Drcpcheck_core.Parse

let interval lb ub =
  Coq_interval (Big_int_Z.big_int_of_int lb, Big_int_Z.big_int_of_int ub)

let parse_str s = parse (Lexing.from_string s) None

let show_intset dom =
  match dom with
  | Coq_interval (lb, ub) ->
      Printf.sprintf "%s..%s"
        (Big_int_Z.string_of_big_int lb)
        (Big_int_Z.string_of_big_int ub)
  | Coq_sparse_set _ -> Printf.sprintf "sparse_set"

let ( << ) f g x = f (g x)

let show_var var =
  match var with
  | Coq_var_name name -> name
  | Coq_const value -> Big_int_Z.string_of_big_int value

let show_constr constr =
  match constr with
  | Coq_linear_leq cons ->
      let weights =
        String.concat ", "
          (List.map (Big_int_Z.string_of_big_int << fst) cons.l_terms)
      in
      let vars = String.concat ", " (List.map (show_var << snd) cons.l_terms) in
      let bound = Big_int_Z.string_of_big_int cons.l_bound in
      Printf.sprintf "constraint int_lin_le([%s], [%s], %s);" weights vars bound
  | _ -> "constraint unknown"

let show_csp csp =
  let vars =
    Coq_smap.fold
      (fun name dom acc ->
        Printf.sprintf "%svar %s: %s;\n" acc (show_intset dom) name)
      csp.domains ""
  in
  let cons =
    Coq_nmap.fold
      (fun _ cons acc -> Printf.sprintf "%s%s\n" acc (show_constr cons))
      csp.constraints ""
  in

  vars ^ cons

let test_parse input expected =
  let parsed = parse_str input in
  (*let _ =*)
  (*  if parsed = expected then ()*)
  (*  else*)
  (*in*)

  parsed = expected

let%test "parse single constant" =
  let source = {|
        int: p = 3;
        solve satisfy;
    |} in
  let expected = { domains = Coq_smap.empty; constraints = Coq_nmap.empty } in

  test_parse source expected
