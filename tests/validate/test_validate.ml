open Drcpcheck_core.Checker
module SeqChecker = SequentialChecker (DefaultRules)

type outcome = Accepted | Rejected | Errored

let string_of_outcome = function
  | Accepted -> "accepted"
  | Rejected -> "rejected"
  | Errored -> "errored"

let check csp drcp =
  try
    match SeqChecker.validate csp (Drcpcheck_drcp.Read.read_proof drcp) with
    | Proofs.Coq_valid _ -> Accepted
    | Proofs.Coq_invalid _ -> Rejected
  with _ -> Errored

let () =
  let dir = Sys.argv.(1) in
  let fzn_dir = Filename.concat (Filename.dirname dir) "fzn" in
  let expected = if Sys.argv.(2) = "valid" then Accepted else Rejected in
  Sys.readdir dir |> Array.to_list
  |> List.filter (fun n ->
         Filename.check_suffix n ".bin" || Filename.check_suffix n ".bin.gz")
  |> List.map (fun n ->
         Filename.chop_suffix n
           (if Filename.check_suffix n ".gz" then ".bin.gz" else ".bin"))
  |> List.sort_uniq String.compare
  |> List.iter (fun case ->
         let path ext = Filename.concat dir (case ^ ext) in
         let drcp =
           if Sys.file_exists (path ".drcp") then path ".drcp" else path ".drcp.gz"
         in
         let csp =
           Drcpcheck_flatzinc.Read.read_constraint_problem
             (Filename.concat fzn_dir (case ^ ".fzn"))
         in
         let got = check csp drcp in
         if got <> expected then
           Printf.printf "%s/%s: expected %s, got %s\n" dir case
             (string_of_outcome expected) (string_of_outcome got))
