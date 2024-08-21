open Cmdliner

let check_proof model proof =
    if not (Sys.file_exists model)
    then `Error (false, model ^ ": not a file")
    else if not (Sys.file_exists proof)
    then `Error (false, proof ^ ": not a file")
    else `Ok (Printf.printf "model = %s\nproof = %s\n" model proof)

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
