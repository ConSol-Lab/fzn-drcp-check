open Cmdliner
open Fzn_drcp_check

let parse_proof _ = { Checker.steps = []; conclusion0 = Checker.Unsat }
let parse_model _ = { Checker.constraints = []; Checker.variables = [] }

(** Convert a `nat` extracted from Coq to an OCaml integer. *)
let rec nat_to_int = function Checker.O -> 0 | Checker.S n -> 1 + nat_to_int n

let check_proof model proof =
  if not (Sys.file_exists model) then `Error (false, model ^ ": not a file")
  else if not (Sys.file_exists proof) then `Error (false, proof ^ ": not a file")
  else
    let parsed_proof = parse_proof proof in
    let parsed_model = parse_model model in
    match Checker.find_invalid_step parsed_proof parsed_model with
    | Some (step_nr, _) ->
        `Ok
          (Printf.printf "Proof is invalid! Rejected proof step %d\n"
             (nat_to_int step_nr))
    | None -> `Ok (print_endline "Proof is valid!")

let model_t =
  let doc = "The FZN file describing the model." in
  let docv = "FZN" in
  Arg.(required & pos 0 (some string) None & info [] ~docv ~doc)

let proof_t =
  let doc = "The DRCP file containing the proof." in
  let docv = "DRCP" in
  Arg.(required & pos 1 (some string) None & info [] ~docv ~doc)

let cmd =
  let doc = "Check whether a given DRCP file is a proof for a FZN model." in
  let info = Cmd.info "fzn-drcp-check" ~version:"%%VERSION%%" ~doc in
  Cmd.v info Term.(ret (const check_proof $ model_t $ proof_t))

let () = exit (Cmd.eval cmd)
