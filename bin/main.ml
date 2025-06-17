let usage = "drcpcheck <flatzinc>"

let input_file = ref ""

let assign_args filename = input_file := filename

let () = 
    Arg.parse [] assign_args usage;
    if !input_file != "" then
        let channel = In_channel.open_text !input_file in
        let lexbuf = Lexing.from_channel channel in
        let _ = Drcpcheck_flatzinc.Parse.parse lexbuf (Some !input_file) in  
            print_endline "Parsed successfully!"
    else
        print_endline "Provide a flatzinc model."


(* open Drcpcheck_core.Checker

let str_to_char_list s = List.init (String.length s) (String.get s)

let n_of_int n =
  let rec pos_of_int n =
    if n = 1 then XH
    else if n mod 2 = 0 then XO (pos_of_int (n / 2))
    else XI (pos_of_int (n / 2))
  in
  if n = 0 then N0 else Npos (pos_of_int n)

let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (let rec f n = if n = 1 then XH else if n mod 2 = 0 then XO (f (n / 2)) else XI (f (n / 2)) in f n)
  else Zneg (let rec f n = if n = 1 then XH else if n mod 2 = 0 then XO (f (n / 2)) else XI (f (n / 2)) in f (-n))

let nat_of_int n =
  let rec f n = if n = 0 then O else S (f (n - 1)) in f n

(* ---------- Activity definitions ---------- *)

let act_x     = { def_x = str_to_char_list "x" ; def_p = n_of_int 4 ; def_u = n_of_int 1 }
let act_y_p3  = { def_x = str_to_char_list "y" ; def_p = n_of_int 3 ; def_u = n_of_int 1 }
let act_y_p1  = { def_x = str_to_char_list "y" ; def_p = n_of_int 1 ; def_u = n_of_int 1 }
let act_y_p2  = { def_x = str_to_char_list "y" ; def_p = n_of_int 2 ; def_u = n_of_int 1 }

(* ---------- Cumulative-resource constraints ---------- *)

let constr1 = { capacity = n_of_int 1 ; activities = [ act_x ; act_y_p3 ] }   (* mandatory-conflict *)
let constr2 = { capacity = n_of_int 1 ; activities = [ act_x ; act_y_p1 ] }   (* 1-step + simple  *)
(* example 3 re-uses constr2 *)
let constr4 = { capacity = n_of_int 1 ; activities = [ act_x ; act_y_p2 ] }   (* multi-step hole  *)

(* ---------- Small helpers for atoms ---------- *)

let ge v = { atm_cmp = Greater_equal ; atm_val = z_of_int v }
let le v = { atm_cmp = Less_equal   ; atm_val = z_of_int v }

(* ---------- Facts (inferences) ---------- *)

(* Example 1 – Mandatory conflict *)
let fact1 = {
  i_premises = [
    (str_to_char_list "x", ge 0) ;
    (str_to_char_list "x", le 2) ;
    (str_to_char_list "y", ge 1) ;
    (str_to_char_list "y", le 3)
  ] ;
  i_consequent = None
}

(* Example 2 – 1-step overlap *)
let fact2 = {
  i_premises = [
    (str_to_char_list "x", ge 0) ;
    (str_to_char_list "x", le 2) ;
    (str_to_char_list "y", ge 2)
  ] ;
  i_consequent = Some (str_to_char_list "y", ge 3)
}

(* Example 3 – Multi-step simple *)
let fact3 = {
  i_premises = [
    (str_to_char_list "x", ge 0) ;
    (str_to_char_list "x", le 2) ;
    (str_to_char_list "y", ge 2)
  ] ;
  i_consequent = Some (str_to_char_list "y", ge 4)
}

(* Example 4 – Multi-step hole *)
let fact4 = {
  i_premises = [
    (str_to_char_list "x", ge 0) ;
    (str_to_char_list "x", le 2) ;
    (str_to_char_list "y", ge 1)
  ] ;
  i_consequent = Some (str_to_char_list "y", ge 4)
}

let rec positive_to_int = function
  | XI p -> 2 * (positive_to_int p) + 1
  | XO p -> 2 * (positive_to_int p)
  | XH -> 1

let rec nat_to_int = function
  | O -> 0
  | S n -> 1 + nat_to_int n

let n_to_int = function
  | N0 -> 0
  | Npos p -> positive_to_int p

let z_to_int = function
  | Z0 -> 0
  | Zpos p -> positive_to_int p
  | Zneg p -> -(positive_to_int p)

(* Updated string conversion functions using decimal representation *)
let string_of_n n = string_of_int (n_to_int n)
let string_of_z z = string_of_int (z_to_int z)

let () =
  let r1 = cumulative_checker fact1 constr1 in
  let r2 = cumulative_checker fact2 constr2 in
  let r3 = cumulative_checker fact3 constr2 in
  let r4 = cumulative_checker fact4 constr4 in
  Printf.printf "Example 1: %b\n" r1;
  Printf.printf "Example 2: %b\n" r2;
  Printf.printf "Example 3: %b\n" r3;
  Printf.printf "Example 4: %b\n" r4; *)

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
