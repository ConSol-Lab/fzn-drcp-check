open Big_int_Z
open Drcpcheck_core.Checker
open Drcpcheck_core.Checker.ProofFacts
module StreamingChecker = StreamingChecker (DefaultRules)
module SeqChecker = SequentialChecker (DefaultRules)

let usage =
  {|
fzn_drcp_check [-s] [--drcp-format text|binary] [-d] <flatzinc> <drcp|bin>

--drcp-format: proof encoding. Defaults to guessing from the file extension, .drcp or .bin.
-s: streamed mode. Performs incremental reads from a file or pipe instead of loading everything in memory at once.
-d: debug mode. Prints precise time measurements for each step of the checking process.
|}

(* Input files *)
let flatzinc_file = ref ""
let drcp_file = ref ""

(* CLI Args *)
let arg_count = ref 0
let drcp_format = ref None
let streamed_mode = ref false
let debug_mode = ref false

(* CLI Actions *)
let speclist =
  [
    ( "--drcp-format",
      Arg.Symbol
        ( [ "text"; "binary" ],
          fun s -> drcp_format := Some (if s = "binary" then `Binary else `Text)
        ),
      " Proof encoding (default: guessed from the file extension)" );
    ("-s", Arg.Set streamed_mode, "Streamed mode");
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

let read_proof drcp_file =
  let proof_handle = open_in drcp_file in
  let source =
    really_input_string proof_handle (in_channel_length proof_handle)
  in
  close_in proof_handle;
  Drcpcheck_drcp.Parse.parse_proof source

let read_binary_proof bin_file =
  let chan = open_in_bin bin_file in
  let len = in_channel_length chan in
  let source = Bytes.create len in
  really_input chan source 0 len;
  close_in chan;
  Drcpcheck_drcp.Deserialize.deserialize_binary_proof source

let show_atomic (name, atomic) =
  let cmp =
    match atomic.atm_cmp with
    | Coq_greater_equal -> ">="
    | Coq_less_equal -> "<="
    | Coq_equal -> "=="
    | Coq_not_equal -> "!="
  in
  let value = string_of_big_int atomic.atm_val in
  Printf.sprintf "[%s %s %s]" name cmp value

let print_error e =
  match e with
  | Deduction_implies_not_false ->
      print_endline
        "One of the deduction steps does not imply false. This should not be \
         able to happen!"
  | Unknown_inference (step_id, name) ->
      Printf.printf "Inference %s (%s) is unknown\n"
        (string_of_big_int step_id)
        name
  | Invalid_inference step_id ->
      Printf.printf "Inference %s is unsound\n" (string_of_big_int step_id)
  | Invalid_deduction (step_id, None) ->
      Printf.printf "Deduction %s has inconsistent premises\n"
        (string_of_big_int step_id)
  | Invalid_deduction (step_id, Some inferences) ->
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
            (print_fact inf.fact)
            (String.concat ", " (List.map show_atomic inf.missing_premises)))
        inferences
  | Invalid_conclusion -> print_endline "Invalid conclusion."

let time label f =
  if not !debug_mode then f ()
  else begin
    let t = Sys.time () in
    let res = f () in
    Printf.printf "%s: %fs\n%!" label (Sys.time () -. t);
    res
  end

let run_streamed ?(format = `Text) csp file =
  let fd = Unix.openfile file [ O_RDONLY ] 0 in
  let buf = Drcpcheck_util.Buffer.DBuffer.create_default () in
  let stream =
    match format with
    | `Text ->
        let chan = Unix.in_channel_of_descr fd in
        let text_parser = Drcpcheck_drcp.Parse.create_steps_parser () in
        Drcpcheck_drcp.Parse.read_available_text_and_build_stage chan
          text_parser Drcpcheck_drcp.Parse.IntMap.empty
    | `Binary ->
        Drcpcheck_drcp.Deserialize.read_available_and_build_stage fd buf
          Drcpcheck_drcp.Parse.IntMap.empty
  in
  let result = StreamingChecker.validate csp stream in
  result

let run_checker flatzinc_file drcp_file =
  let format =
    match !drcp_format with
    | Some format -> format
    | None ->
        if
          Filename.check_suffix drcp_file ".bin"
          || Filename.check_suffix drcp_file ".bin.gz"
        then `Binary
        else if
          Filename.check_suffix drcp_file ".drcp"
          || Filename.check_suffix drcp_file ".drcp.gz"
        then `Text
        else (
          Printf.eprintf
            "cannot infer the proof format of %s: expected a .drcp or .bin \
             extension (or pass --drcp-format)\n\
             %!"
            drcp_file;
          exit 2)
  in
  let csp =
    time "parse-flatzinc" (fun () -> read_constraint_problem flatzinc_file)
  in
  let result =
    if !streamed_mode then run_streamed ~format csp drcp_file
    else
      let proof =
        match format with
        | `Binary -> time "parse-proof" (fun () -> read_binary_proof drcp_file)
        | `Text -> time "parse-proof" (fun () -> read_proof drcp_file)
      in
      time "validate" (fun () -> SeqChecker.validate csp proof)
  in
  match result with
  | Proofs.Coq_valid _ -> print_endline "Proof is valid!"
  | Proofs.Coq_invalid e ->
      print_error e;
      exit 1

let () =
  Arg.parse speclist assign_args usage;

  if !arg_count != 2 then print_endline usage
  else run_checker !flatzinc_file !drcp_file
