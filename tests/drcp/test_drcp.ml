open Drcpcheck_core.Checker
open Drcpcheck_core.Checker.ProofFacts
open Drcpcheck_drcp.Parse
open Big_int_Z

let implication premises consequent =
  { i_premises = premises; i_consequent = Some consequent }

let nogood premises = { i_premises = premises; i_consequent = None }

let atom name atm_cmp atm_val =
  (name, { atm_cmp; atm_val = big_int_of_int atm_val })

let inference id premises consequent generated_by label =
  {
    iinf_index = big_int_of_int id;
    iinf_fact = { i_premises = premises; i_consequent = consequent };
    iinf_rule = label;
    iinf_hint = List.map big_int_of_int generated_by;
  }

let show_atomic = function
  | name, atomic ->
      let cmp =
        match atomic.atm_cmp with
        | Coq_greater_equal -> ">="
        | Coq_less_equal -> "<="
        | Coq_equal -> "=="
        | Coq_not_equal -> "!="
      in
      let value = string_of_big_int atomic.atm_val in
      Printf.sprintf "[%s %s %s]" name cmp value

let show_inference inference =
  let id = string_of_big_int inference.iinf_index in
  let premises =
    String.concat " " (List.map show_atomic inference.iinf_fact.i_premises)
  in
  let consequent =
    match inference.iinf_fact.i_consequent with
    | Some atomic -> Printf.sprintf "0 %s" (show_atomic atomic)
    | None -> ""
  in
  let generated_by =
    Printf.sprintf "c:%s" (string_of_big_int (List.hd inference.iinf_hint))
  in
  let label =
    Printf.sprintf "l:%s"
      (match inference.iinf_rule with
      | Linear -> "linear_bounds"
      | Fact_equiv -> "nogood"
      | Dom -> "dom"
      | Alldifferent -> "alldifferent"
      | Cumulative -> "cumulative" )
  in
  Printf.sprintf "i %s %s %s %s %s" id premises consequent generated_by label

let show_proof_stage stage : string =
  let inferences =
    String.concat "\n" (List.map show_inference stage.s_inferences)
  in
  let conclusion_id = string_of_big_int stage.s_conclusion_index in
  let conclusion_premises =
    String.concat " " (List.map show_atomic stage.s_conclusion.i_premises)
  in
  let sequence = String.concat " " (List.map string_of_big_int stage.s_chain) in
  Printf.sprintf "%s\nn %s %s 0 %s" inferences conclusion_id conclusion_premises
    sequence

let show_proof proof conclusion =
  let steps = String.concat "\n" (List.map show_proof_stage proof) in
  let conclusion_premises =
    String.concat " " (List.map show_atomic conclusion.i_premises)
  in
  let consequent =
    match conclusion.i_consequent with
    | Some atomic -> Printf.sprintf "0 %s" (show_atomic atomic)
    | None -> "0 False"
  in
  let conclusion = Printf.sprintf "c %s %s" conclusion_premises consequent in
  steps ^ "\n" ^ conclusion

let test_parse input expected =
  let parsed = parse_proof input in
  if parsed = expected then true
  else
    let expected_proof, expected_conclusion = expected in
    let parsed_proof, parsed_conclusion = parsed in
    let _ =
      Printf.printf
        "==========\nEXPECTED:\n%s\n----------\nPARSED:\n%s\n==========\n"
        (show_proof expected_proof expected_conclusion)
        (show_proof parsed_proof parsed_conclusion)
    in
    false

let%test "parse an empty nogood" =
  let source = {|
    n 1 0
    c UNSAT
    |} in
  let expected =
    ( [
        {
          s_conclusion = nogood [];
          s_inferences = [];
          s_chain = [];
          s_conclusion_index = big_int_of_int 1;
        };
      ],
      { i_premises = []; i_consequent = None } )
  in

  test_parse source expected

let%test "parse a unit nogood" =
  let source = {|
    a 1 [x1 >= 1]
    n 1 -1 0
    c UNSAT
    |} in
  let expected =
    ( [
        {
          s_conclusion = nogood [ atom "x1" Coq_less_equal 0 ];
          s_inferences = [];
          s_chain = [];
          s_conclusion_index = big_int_of_int 1;
        };
      ],
      { i_premises = []; i_consequent = None } )
  in

  test_parse source expected

let%test "parse a proof stage" =
  let source =
    {|
    a 1 [x1 >= 1]
    a 2 [x2 <= 2]
    a 3 [x3 >= 1]
    i 7 1 2 3 0 c:6 l:linear_bounds
    i 8 1 2 0 3 c:5 l:linear_bounds
    n 9 1 0 5 6
    c UNSAT
    |}
  in
  let expected =
    ( [
        {
          s_inferences =
            [
              inference 7
                [
                  atom "x1" Coq_greater_equal 1;
                  atom "x2" Coq_less_equal 2;
                  atom "x3" Coq_greater_equal 1;
                ]
                None [ 6 ] Linear;
              inference 8
                [ atom "x1" Coq_greater_equal 1; atom "x2" Coq_less_equal 2 ]
                (Some (atom "x3" Coq_greater_equal 1))
                [ 5 ] Linear;
            ];
          s_conclusion = nogood [ atom "x1" Coq_greater_equal 1 ];
          s_chain = [ big_int_of_int 5; big_int_of_int 6 ];
          s_conclusion_index = big_int_of_int 9;
        };
      ],
      { i_premises = []; i_consequent = None } )
  in

  test_parse source expected

let%test "parse initial domain inferences without constraint hint" =
  let source =
    {|
    a 1 [x1 >= 1]
    i 1 0 1 l:initial_domain
    i 2 0 -1 l:initial_domain
    n 3 0 1 2
    c UNSAT
    |}
  in
  let expected =
    ( [
        {
          s_inferences =
            [
              inference 1 [] (Some (atom "x1" Coq_greater_equal 1)) [] Dom;
              inference 2 [] (Some (atom "x1" Coq_less_equal 0)) [] Dom;
            ];
          s_conclusion = nogood [];
          s_chain = [ big_int_of_int 1; big_int_of_int 2 ];
          s_conclusion_index = big_int_of_int 3;
        };
      ],
      { i_premises = []; i_consequent = None } )
  in

  test_parse source expected

let%test "parse a dual bound proof" =
  let source = {|
    a 1 [x1 >= 1]
    n 3 1 0
    c -1
  |} in
  let expected =
    ( [
        {
          s_inferences = [];
          s_conclusion = nogood [ atom "x1" Coq_greater_equal 1 ];
          s_chain = [];
          s_conclusion_index = big_int_of_int 3;
        };
      ],
      { i_premises = [ atom "x1" Coq_greater_equal 1 ]; i_consequent = None } )
  in

  test_parse source expected
