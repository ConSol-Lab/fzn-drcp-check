open Fzn_drcp_check
open Printf
open Lexing
open Litmap_parser
open Litmap_lexer
open Litmap

let pp_map (m : litmap) =
  IntMap.iter
    (fun k { variable; comparator; value } ->
      printf "%d -> [%s %s %d]\n" k variable (to_string comparator) value)
    m

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let parse_litmap_with_error lexbuf =
  try litmap token lexbuf with
  | SyntaxError msg ->
      fprintf stderr "%a: %s\n" print_position lexbuf msg;
      exit (-1)
  | Error ->
      fprintf stderr "%a: syntax error\n" print_position lexbuf;
      exit (-1)

let parse_and_print lexbuf =
  let lits = parse_litmap_with_error lexbuf in
  pp_map lits;
  lits

let read_litmap litmap_file =
  let inx = In_channel.open_text litmap_file in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = litmap_file };
  let _ = parse_and_print lexbuf in
  In_channel.close inx

let read_proof _proof_file _lits =
  { Checker.steps = []; Checker.conclusion0 = Unsat }

let parse_proof litmap_file = read_proof "" (read_litmap litmap_file)
