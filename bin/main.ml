(* open Cmdliner
open Fzn_drcp_check
open Conversion

let read_proof proof_file =
  let parsed_proof = Fzn_drcp_check_parsing.parse_proof proof_file in
  Printf.printf "len: %d\n" (List.length parsed_proof.steps);
  convert_proof parsed_proof

let parse_model _ = { Checker.constraints = []; Checker.variables = [] }

(** Convert a `nat` extracted from Coq to an OCaml integer. *)
let rec nat_to_int = function Checker.O -> 0 | Checker.S n -> 1 + nat_to_int n

let check_proof model proof =
  if not (Sys.file_exists model) then `Error (false, model ^ ": not a file")
  else if not (Sys.file_exists proof) then `Error (false, proof ^ ": not a file")
  else
    let parsed_proof = read_proof proof in
    let parsed_model = parse_model model in
    match Checker.validate parsed_model parsed_proof with
    | false -> `Ok
      (Printf.printf "Proof is invalid; placeholder for the proof step: %d"
        (nat_to_int Checker.O))
    | true -> `Ok (print_endline "Proof is valid")

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

*)