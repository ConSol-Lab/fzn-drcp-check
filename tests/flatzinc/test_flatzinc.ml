open Drcpcheck_core.Checker.ConstraintDefinitions
open Drcpcheck_core.Checker.Maps
open Drcpcheck_flatzinc.Parse

let str s = List.init (String.length s) (String.get s)

let parse_str s = parse (Lexing.from_string s) None

let test_parse input expected = 
    let parsed = parse_str input in
    parsed = expected

let%test "parse single variable with interval domain" =
    let source = {|
        var 0..10: var1;
    |} in
    let expected = { domains = Coq_smap.empty; constraints = Coq_nmap.empty } in

    test_parse source expected


let%test "comments are ignored" =
    let source = {|
        % comment
        var 0..10: var1; % comment
        %comment
    |} in
    let expected = { domains = Coq_smap.empty; constraints = Coq_nmap.empty } in

    test_parse source expected


let%test "variable with annotation" =
    let source = {|
        var 0..10: var1 :: output_var;
    |} in
    let expected = { domains = Coq_smap.empty; constraints = Coq_nmap.empty } in

    test_parse source expected


let%test "parse multiple variables with interval domain" =
    let source = {|
        var 0..10: var1;
        var 1..5: var2;
    |} in
    let expected = { domains = Coq_smap.empty; constraints = Coq_nmap.empty } in

    test_parse source expected

let%test "parse constants array" =
    let source = {|
        array [1..3] of int: arr = [1, -2, 24];
    |} in
    let expected = { domains = Coq_smap.empty; constraints = Coq_nmap.empty } in

    test_parse source expected

let%test "parse variable array" =
    let source = {|
        var 0..10: var1;
        var 0..10: var2;
        var 0..10: var3;
        array [1..3] of var int: arr = [var1, var2, var3];
    |} in
    let expected = { domains = Coq_smap.empty; constraints = Coq_nmap.empty } in

    test_parse source expected

let%test "parse variable array with annotation" =
    let source = {|
        var 0..10: var1;
        var 0..10: var2;
        var 0..10: var3;
        array [1..2] of var int: arr1 :: output_array([1..8]) = [var1, var2];
        array [1..1] of var int: arr2 :: some_annotation = [var3];
    |} in
    let expected = { domains = Coq_smap.empty; constraints = Coq_nmap.empty } in

    test_parse source expected

let%test "parse variable array with constants" =
    let source = {|
        var 0..10: var1;
        var 0..10: var2;
        var 0..10: var3;
        array [1..3] of var int: arr = [var1, var2, var3];
    |} in
    let expected = { domains = Coq_smap.empty; constraints = Coq_nmap.empty } in

    test_parse source expected

let%test "parse linear inequality with inline arguments" =
    let source = {|
        var 0..10: var1;
        var 0..10: var2;
        var 0..10: var3;
        constraint int_lin_le([1, -1, 2], [var1, var2, var3], 15);
    |} in
    let expected = { domains = Coq_smap.empty; constraints = Coq_nmap.empty } in

    test_parse source expected

