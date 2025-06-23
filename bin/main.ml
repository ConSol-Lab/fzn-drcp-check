let usage = "drcpcheck <flatzinc> <drcp>"

(* Input files *)
let flatzinc_file = ref ""
let drcp_file = ref ""
let arg_count = ref 0

(* CLI Actions *)
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

let run_checker flatzinc_file drcp_file =
  let csp = read_constraint_problem flatzinc_file in
  let proof = read_proof drcp_file in
  if Drcpcheck_core.Checker.validate csp proof then
    print_endline "Proof is valid!"
  else print_endline "Validation failed!"

let () =
  Arg.parse [] assign_args usage;

  if !arg_count != 2 then print_endline usage
  else run_checker !flatzinc_file !drcp_file
