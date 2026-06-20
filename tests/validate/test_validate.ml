open Drcpcheck_core.Checker
module SeqChecker = SequentialChecker (DefaultRules)
module StreamingChecker = StreamingChecker (DefaultRules)

type outcome = Accepted | Rejected | Errored

let string_of_outcome = function
  | Accepted -> "accepted"
  | Rejected -> "rejected"
  | Errored -> "errored"

let outcome_of validate =
  match validate () with
  | Proofs.Coq_valid _ -> Accepted
  | Proofs.Coq_invalid _ -> Rejected
  | exception _ -> Errored

let text_stream drcp =
  if Filename.check_suffix drcp ".gz" then
    Drcpcheck_drcp.Read.read_streamed_text_gz drcp
  else Drcpcheck_drcp.Parse.read_streamed_text (open_in drcp)

let binary_stream bin =
  if Filename.check_suffix bin ".gz" then
    Drcpcheck_drcp.Read.read_streamed_binary_gz bin
  else
    Drcpcheck_drcp.Deserialize.stream_proof
      (Drcpcheck_drcp.Deserialize.Source.of_channel (open_in_bin bin))

let () =
  let dir = Sys.argv.(1) in
  let fzn_dir = Filename.concat (Filename.dirname dir) "fzn" in
  let expected = if Sys.argv.(2) = "valid" then Accepted else Rejected in
  let report case label got =
    if got <> expected then
      Printf.printf "%s/%s%s: expected %s, got %s\n" dir case label
        (string_of_outcome expected) (string_of_outcome got)
  in
  Sys.readdir dir |> Array.to_list
  |> List.filter (fun n ->
         Filename.check_suffix n ".bin" || Filename.check_suffix n ".bin.gz")
  |> List.map (fun n ->
         Filename.chop_suffix n
           (if Filename.check_suffix n ".gz" then ".bin.gz" else ".bin"))
  |> List.sort_uniq String.compare
  |> List.iter (fun case ->
         let path ext = Filename.concat dir (case ^ ext) in
         let pick ext gz = if Sys.file_exists (path ext) then path ext else path gz in
         let drcp = pick ".drcp" ".drcp.gz" in
         let bin = pick ".bin" ".bin.gz" in
         let csp =
           Drcpcheck_flatzinc.Read.read_constraint_problem
             (Filename.concat fzn_dir (case ^ ".fzn"))
         in
         report case "" (outcome_of (fun () ->
             SeqChecker.validate csp (Drcpcheck_drcp.Read.read_proof drcp)));
         report case " (binary)" (outcome_of (fun () ->
             SeqChecker.validate csp (Drcpcheck_drcp.Read.read_binary_proof bin)));
         report case " (streamed)" (outcome_of (fun () ->
             StreamingChecker.validate csp (text_stream drcp)));
         report case " (streamed binary)" (outcome_of (fun () ->
             StreamingChecker.validate csp (binary_stream bin))))
