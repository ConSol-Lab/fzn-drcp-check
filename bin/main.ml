open Big_int_Z
open Drcpcheck_core
open Drcpcheck_core.CheckerStreamed
open Drcpcheck_core.Spec.ProofFacts

let usage =
  {|
fzn_drcp_check [-d] <flatzinc> <drcp>

-d: debug mode. Prints precise time measurements for each step of the checking process.
|}

(* Input files *)
let flatzinc_file = ref ""
let drcp_file = ref ""
let arg_count = ref 0
let debug_mode = ref false

(* CLI Actions *)
let speclist =
  [
    ("-d", Arg.Set debug_mode, "Debug mode");
  ]

let assign_args anonymous_argument =
  arg_count := !arg_count + 1;
  if !arg_count = 1 then flatzinc_file := anonymous_argument
  else if !arg_count = 2 then drcp_file := anonymous_argument
  else raise (Arg.Bad "Too many anonymous arguments.")

let read_constraint_problem flatzinc_file =
  let channel = In_channel.open_text flatzinc_file in
  let lexbuf = Lexing.from_channel channel in
  Drcpcheck_flatzinc.Parse.parse lexbuf (Some flatzinc_file)

let _read_proof drcp_file =
  let proof_handle = open_in drcp_file in
  let source =
    really_input_string proof_handle (in_channel_length proof_handle)
  in
  close_in proof_handle;
  Drcpcheck_drcp.Parse.parse_proof source

let print_error e =
  match e with
  | Coq_deduction_implies_not_false ->
      print_endline
        "One of the deduction steps does not imply false. This should not be \
         able to happen!"
  | Coq_unknown_inference (step_id, name) ->
      Printf.printf "Inference %s (%s) is unknown\n"
        (string_of_big_int step_id)
        name
  | Coq_invalid_inference step_id ->
      Printf.printf "Inference %s is unsound\n" (string_of_big_int step_id)
  | Coq_invalid_deduction (step_id, None) ->
      Printf.printf "Deduction %s has inconsistent premises\n"
        (string_of_big_int step_id)
  | Coq_invalid_deduction (step_id, Some inferences) ->
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
      in

      let premises fact =
        String.concat " " (List.map show_atomic fact.i_premises)
      in
      let consequent fact =
        match fact.i_consequent with
        | Some atomic -> show_atomic atomic
        | None -> "False"
      in
      let print_fact fact =
        Printf.sprintf "%s => %s" (premises fact) (consequent fact)
      in
      Printf.printf
        "Deduction %s did not derive a contradiction. The following %d \
         inferences could not be used:\n"
        (string_of_big_int step_id)
        (List.length inferences);

      List.iter
        (fun inf ->
          Printf.printf "  - %s\n    Missing premises: %s\n"
            (print_fact inf.Deduction.fact)
            (String.concat ", " (List.map show_atomic inf.Deduction.missing_premises)))
        inferences
  | Coq_invalid_conclusion -> print_endline "Invalid conclusion."

let time label f =
  if not !debug_mode then f ()
  else begin
    let t = Sys.time () in
    let res = f () in
    Printf.printf "%s: %fs\n%!" label (Sys.time () -. t);
    res
  end

let run_streamed csp file =
  let fd = Unix.openfile file [ O_RDONLY ] 0 in
  let chan = Unix.in_channel_of_descr fd in
  let parser = Drcpcheck_drcp.Parse.create_steps_parser () in
  let stream =
    Drcpcheck_drcp.Parse.read_available_text_and_build_stage chan parser
      Drcpcheck_drcp.Parse.IntMap.empty
  in
  validate default_rules csp stream

let run_checker flatzinc_file drcp_file =
  let csp =
    time "parse-flatzinc" (fun () -> read_constraint_problem flatzinc_file)
  in
  let result = run_streamed csp drcp_file in
  match result with
  | Spec.Proofs.Coq_valid -> print_endline "Proof is valid!"
  | Spec.Proofs.Coq_invalid e ->
      print_error e;
      exit 1

let () =
  Arg.parse speclist assign_args usage;

  if !arg_count != 2 then print_endline usage
  else run_checker !flatzinc_file !drcp_file
