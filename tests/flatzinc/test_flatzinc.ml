(*
NOTE: This file contains some test cases for the FlatZinc parsing. Since there is not a built-in equality for
the CSP type, we rely on (=) for equality. HOWEVER, for the map this equality is not order-independent, so
the order of the variables in the source and expected matter. Since we do not really care about the order,
just order the variables to make the test pass.
*)

open Drcpcheck_core.Checker.ConstraintDefinitions
open Drcpcheck_core.Checker.Maps
open Drcpcheck_flatzinc.Parse

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
  let _ =
    if parsed = expected then ()
    else
      Printf.printf
        "==========\nEXPECTED:\n%s----------\nPARSED:\n%s==========\n"
        (show_csp expected) (show_csp parsed)
  in

  parsed = expected

let%test "parse single constant" =
  let source = {|
        int: p = 3;
        solve satisfy;
    |} in
  let expected = { domains = Coq_smap.empty; constraints = Coq_nmap.empty } in

  test_parse source expected

let%test "parse single variable with interval domain" =
  let source = {|
        var 0..10: var1;
        solve satisfy;
    |} in
  let expected =
    {
      domains = Coq_smap.add "var1" (interval 0 10) Coq_smap.empty;
      constraints = Coq_nmap.empty;
    }
  in

  test_parse source expected

let%test "parse single variable with singleton domain and assignment" =
  let source =
    {|
        var 10..10: var1 = 10;
        solve satisfy;
    |}
  in
  let expected =
    {
      domains = Coq_smap.add "var1" (interval 10 10) Coq_smap.empty;
      constraints = Coq_nmap.empty;
    }
  in

  test_parse source expected

let%test "comments are ignored" =
  let source =
    {|
        % comment
        var 0..10: var1; % comment
        %comment
        solve satisfy;
    |}
  in
  let expected =
    {
      domains = Coq_smap.add "var1" (interval 0 10) Coq_smap.empty;
      constraints = Coq_nmap.empty;
    }
  in

  test_parse source expected

let%test "variable with annotation" =
  let source =
    {|
        var 0..10: var1 :: output_var;
        solve satisfy;
    |}
  in
  let expected =
    {
      domains = Coq_smap.add "var1" (interval 0 10) Coq_smap.empty;
      constraints = Coq_nmap.empty;
    }
  in

  test_parse source expected

let%test "variable with annotation and args" =
  let source =
    {|
        var 0..10: var1 :: some_annotation(arg1);
        solve satisfy;
    |}
  in
  let expected =
    {
      domains = Coq_smap.add "var1" (interval 0 10) Coq_smap.empty;
      constraints = Coq_nmap.empty;
    }
  in

  test_parse source expected

let%test "parse multiple variables with interval domain" =
  let source =
    {|
        var 2..5: var2;
        var 0..10: var1;
        solve satisfy;
    |}
  in
  let expected =
    {
      domains =
        Coq_smap.add "var1" (interval 0 10)
          (Coq_smap.add "var2" (interval 2 5) Coq_smap.empty);
      constraints = Coq_nmap.empty;
    }
  in

  test_parse source expected

let%test "parse constants array" =
  let source =
    {|
        array [1..3] of int: arr = [1, -2, 24];
        solve satisfy;
    |}
  in
  let expected = { domains = Coq_smap.empty; constraints = Coq_nmap.empty } in

  test_parse source expected

let%test "parse variable array" =
  let source =
    {|
        var 0..10: var1;
        var 2..5: var2;
        var -10..6: var3;
        array [1..3] of var int: arr = [var1, var2, var3];
        solve satisfy;
    |}
  in
  let expected =
    {
      domains =
        Coq_smap.add "var1" (interval 0 10)
          (Coq_smap.add "var2" (interval 2 5)
             (Coq_smap.add "var3" (interval (-10) 6) Coq_smap.empty));
      constraints = Coq_nmap.empty;
    }
  in

  test_parse source expected

let%test "parse variable array with annotation" =
  let source =
    {|
        var 0..10: var1;
        var 0..10: var2;
        var 0..10: var3;
        array [1..2] of var int: arr1 :: output_array([1..8]) = [var1, var2];
        array [1..1] of var int: arr2 :: some_annotation = [var3];
        solve satisfy;
    |}
  in
  let expected =
    {
      domains =
        Coq_smap.add "var1" (interval 0 10)
          (Coq_smap.add "var2" (interval 0 10)
             (Coq_smap.add "var3" (interval 0 10) Coq_smap.empty));
      constraints = Coq_nmap.empty;
    }
  in

  test_parse source expected

let%test "parse variable array with constants" =
  let source =
    {|
        var 0..10: var1;
        var 0..10: var2;
        var 0..10: var3;
        array [1..3] of var int: arr = [var1, var2, var3];
        solve satisfy;
    |}
  in
  let expected =
    {
      domains =
        Coq_smap.add "var1" (interval 0 10)
          (Coq_smap.add "var2" (interval 0 10)
             (Coq_smap.add "var3" (interval 0 10) Coq_smap.empty));
      constraints = Coq_nmap.empty;
    }
  in

  test_parse source expected

let%test "parse linear inequality with inline arguments" =
  let source =
    {|
        var 0..10: var1;
        var 0..10: var2;
        var 0..10: var3;
        constraint int_lin_le([1, -1, 2], [var1, var2, var3], 15);
        solve satisfy;
    |}
  in
  let expected =
    {
      domains =
        Coq_smap.add "var1" (interval 0 10)
          (Coq_smap.add "var2" (interval 0 10)
             (Coq_smap.add "var3" (interval 0 10) Coq_smap.empty));
      constraints =
        Coq_nmap.add
          (Big_int_Z.big_int_of_int 1)
          (Coq_linear_leq
             {
               l_terms =
                 [
                   (Big_int_Z.big_int_of_int 1, Coq_var_name "var1");
                   (Big_int_Z.big_int_of_int (-1), Coq_var_name "var2");
                   (Big_int_Z.big_int_of_int 2, Coq_var_name "var3");
                 ];
               l_bound = Big_int_Z.big_int_of_int 15;
             })
          Coq_nmap.empty;
    }
  in

  test_parse source expected

let%test "parse linear inequality with annotations" =
  let source =
    {|
        var 0..10: var1;
        var 0..10: var2;
        var 0..10: var3;
        constraint int_lin_le([1, -1, 2], [var1, var2, var3], 15) :: defines_var(var1);
        solve satisfy;
    |}
  in
  let expected =
    {
      domains =
        Coq_smap.add "var1" (interval 0 10)
          (Coq_smap.add "var2" (interval 0 10)
             (Coq_smap.add "var3" (interval 0 10) Coq_smap.empty));
      constraints =
        Coq_nmap.add
          (Big_int_Z.big_int_of_int 1)
          (Coq_linear_leq
             {
               l_terms =
                 [
                   (Big_int_Z.big_int_of_int 1, Coq_var_name "var1");
                   (Big_int_Z.big_int_of_int (-1), Coq_var_name "var2");
                   (Big_int_Z.big_int_of_int 2, Coq_var_name "var3");
                 ];
               l_bound = Big_int_Z.big_int_of_int 15;
             })
          Coq_nmap.empty;
    }
  in

  test_parse source expected

let%test "parse linear inequality with lookup of array arguments" =
  let source =
    {|
        int: b = 15;
        array [1..3] of int: w = [1, -1, 2];
        var 0..10: var1;
        var 0..10: var2;
        var 0..10: var3;
        array [1..3] of var int: arr = [var1, var2, var3];
        constraint int_lin_le(w, arr, b);
        solve satisfy;
    |}
  in
  let expected =
    {
      domains =
        Coq_smap.add "var1" (interval 0 10)
          (Coq_smap.add "var2" (interval 0 10)
             (Coq_smap.add "var3" (interval 0 10) Coq_smap.empty));
      constraints =
        Coq_nmap.add
          (Big_int_Z.big_int_of_int 1)
          (Coq_linear_leq
             {
               l_terms =
                 [
                   (Big_int_Z.big_int_of_int 1, Coq_var_name "var1");
                   (Big_int_Z.big_int_of_int (-1), Coq_var_name "var2");
                   (Big_int_Z.big_int_of_int 2, Coq_var_name "var3");
                 ];
               l_bound = Big_int_Z.big_int_of_int 15;
             })
          Coq_nmap.empty;
    }
  in

  test_parse source expected

let%test
    "parse linear inequality with lookup of array arguments and constants \
     mixed with variables" =
  let source =
    {|
        int: b = 15;
        array [1..3] of int: w = [1, -1, 2];
        var 0..10: var3;
        var 0..10: var1;
        array [1..3] of var int: arr = [var1, 2, var3];
        constraint int_lin_le(w, arr, b);
        solve satisfy;
    |}
  in
  let expected =
    {
      domains =
        Coq_smap.add "var1" (interval 0 10)
          (Coq_smap.add "var3" (interval 0 10) Coq_smap.empty);
      constraints =
        Coq_nmap.add
          (Big_int_Z.big_int_of_int 1)
          (Coq_linear_leq
             {
               l_terms =
                 [
                   (Big_int_Z.big_int_of_int 1, Coq_var_name "var1");
                   ( Big_int_Z.big_int_of_int (-1),
                     Coq_const (Big_int_Z.big_int_of_int 2) );
                   (Big_int_Z.big_int_of_int 2, Coq_var_name "var3");
                 ];
               l_bound = Big_int_Z.big_int_of_int 15;
             })
          Coq_nmap.empty;
    }
  in

  test_parse source expected

let%test "model has search heuristic" =
  let source =
    {|
        var 0..10: var1;
        solve :: seq_search([int_search([1,1,X_INTRODUCED_79_,1,1,X_INTRODUCED_88_,1,1],input_order,indomain_max,complete),int_search([1,1,1,1,1,1,1,1],input_order,indomain_max,complete),int_search(X_INTRODUCED_120_,input_order,indomain_min,complete),int_search([objective],input_order,indomain_min,complete)]) minimize objective;
    |}
  in
  let expected =
    {
      domains = Coq_smap.add "var1" (interval 0 10) Coq_smap.empty;
      constraints = Coq_nmap.empty;
    }
  in

  test_parse source expected
