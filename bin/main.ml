open Big_int_Z
open Drcpcheck_core
open Drcpcheck_core.CheckerStreamed
open Drcpcheck_core.Spec.ProofFacts

let usage =
  {|
fzn_drcp_check [--drcp-format text|binary] [-d] <flatzinc> <drcp|bin>

--drcp-format: proof encoding. Defaults to guessing from the file extension, .drcp or .bin.
-d: debug mode. Prints precise time measurements for each step of the checking process.
|}

(* Input files *)
let flatzinc_file = ref ""
let drcp_file = ref ""
let arg_count = ref 0
let drcp_format = ref None
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

let _read_binary_proof ?(_compression = `Packing) bin_file =
  let () = Printf.printf "Reading binary proof from %s...\n%!" bin_file in
  Drcpcheck_drcp.Deserialize_proto.parse_binary_proof bin_file

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

let bufsz = 4096

let rec read_available_and_build_stage ?(format = `Binary) fd buf atomics :
    coq_ProofStream =
  let temp = Bytes.create bufsz in
  let eof = ref false in

  (* check if fd has data right now, timeout=-1 means block indefinitely if nothing is available *)
  let readable, _, _ = Unix.select [ fd ] [] [] (-1.) in

  (if readable <> [] then
     let n = Unix.read fd temp 0 bufsz in
     if n > 0 then Buffer.add_subbytes buf temp 0 n else eof := true);

  (* Process all full stages encountered so far *)
  let stages, new_atomics =
    match format with
    | `Binary ->
        Drcpcheck_drcp.Deserialize_proto.build_stages_from_buf buf atomics
  in

  let next =
   fun () -> read_available_and_build_stage ~format fd buf new_atomics
  in

  let open Drcpcheck_core.Lazy in
  let out = append stages (Thunk next) in

  if !eof then Unix.close fd;
  out

let run_streamed ?(format = `Text) csp file =
  let fd = Unix.openfile file [ O_RDONLY ] 0 in
  let chan = Unix.in_channel_of_descr fd in
  let buf = Buffer.create bufsz in
  let parser = Drcpcheck_drcp.Parse.create_steps_parser () in
  let stream =
    match format with
    | `Text ->
        Drcpcheck_drcp.Parse.read_available_text_and_build_stage chan parser
          Drcpcheck_drcp.Parse.IntMap.empty
    | `Binary ->
        read_available_and_build_stage fd buf Drcpcheck_drcp.Parse.IntMap.empty
  in
  let result = validate default_rules csp stream in
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
  let result = run_streamed ~format csp drcp_file in
  match result with
  | Spec.Proofs.Coq_valid -> print_endline "Proof is valid!"
  | Spec.Proofs.Coq_invalid e ->
      print_error e;
      exit 1

let () =
  Arg.parse speclist assign_args usage;

  if !arg_count != 2 then print_endline usage
  else run_checker !flatzinc_file !drcp_file
