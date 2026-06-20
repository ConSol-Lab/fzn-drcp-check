(* FZN=model.fzn PROOF=proof.drcp|proof.bin dune exec benchmark/bench.exe -- -quota 150 +time +alloc +gc *)
open Core_bench
open Drcpcheck_core.Checker
open Drcpcheck_drcp
module SC = StreamingChecker (DefaultRules)

let () =
  let csp = Drcpcheck_flatzinc.Read.read_constraint_problem (Sys.getenv "FZN") in
  let proof = Sys.getenv "PROOF" in
  let read ch =
    if Filename.check_suffix proof ".bin" then
      Deserialize.(stream_proof (Source.of_channel ch))
    else if Filename.check_suffix proof ".drcp" then Parse.read_streamed_text ch
    else failwith "PROOF must end in .drcp (text) or .bin (binary)"
  in
  let test =
    Bench.Test.create ~name:(Filename.basename proof) (fun () ->
        let ch = open_in_bin proof in
        ignore (SC.validate csp (read ch));
        close_in ch)
  in
  Command_unix.run (Bench.make_command [ test ])
