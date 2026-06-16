(** Test binary deserialization by diffing with text mode results *)

open Drcpcheck_drcp.Read
exception NoError of unit

let string_of_parse_error (e : exn) : string =
  match e with
  | Drcpcheck_drcp.Parse.ParseError msg -> Printf.sprintf "Parse error: %s" msg
  | NoError () -> "No error"
  | _ -> Printf.sprintf "Unknown error: %s" (Printexc.to_string e)

let input_dir = ref ""
let arg_count = ref 0

let assign_args anonymous_argument =
  arg_count := !arg_count + 1;
  if !arg_count = 1 then input_dir := anonymous_argument
  else raise (Arg.Bad "Too many anonymous arguments.")

let empty_conclusion =
  let open Drcpcheck_core.Checker.ProofFacts in
  { i_premises = []; i_consequent = None }

let errors_same error1 error2 =
  let open Drcpcheck_drcp.Parse in
  match (error1, error2) with
  | Some (ParseError _), Some (ParseError _) -> true
  | _, _ -> error1 = error2

let test_case case_name =
  let path ext = Filename.concat !input_dir (case_name ^ ext) in
  let drcp_file =
    if Sys.file_exists (path ".drcp") then path ".drcp" else path ".drcp.gz"
  in
  let bin_file =
    if Sys.file_exists (path ".bin") then path ".bin" else path ".bin.gz"
  in

  let error_bin = ref None in
  let error_drcp = ref None in

  let proof, conclusion =
    try read_proof drcp_file
    with e ->
      error_drcp := Some e;
      ([], empty_conclusion)
  in
  let binary_proof, binary_conclusion =
    try read_binary_proof bin_file
    with e ->
      error_bin := Some e;
      ([], empty_conclusion)
  in

  if not (errors_same !error_bin !error_drcp) then
    Printf.printf
      "Error mismatch for %s/%s: binary error = %s, drcp error = %s\n"
      !input_dir case_name
      (Option.value ~default:(NoError ()) !error_bin |> string_of_parse_error)
      (Option.value ~default:(NoError ()) !error_drcp |> string_of_parse_error)
  else (
    if proof <> binary_proof then
      Printf.printf "Proofs differ for %s/%s\n" !input_dir case_name;
    if conclusion <> binary_conclusion then
      Printf.printf "Conclusions differ for %s/%s\n" !input_dir case_name)

let () =
  Arg.parse [] assign_args
    "test_binary <proof_dir> pointing to a directory containing matching .bin \
     and .drcp[.gz] proofs of the same name";

  let cases =
    Sys.readdir !input_dir
    |> Array.to_list
    |> List.filter (fun n ->
           Filename.check_suffix n ".bin" || Filename.check_suffix n ".bin.gz")
    |> List.map (fun n ->
           Filename.chop_suffix n
             (if Filename.check_suffix n ".gz" then ".bin.gz" else ".bin"))
    |> List.sort_uniq String.compare
  in
  List.map test_case cases |> ignore
