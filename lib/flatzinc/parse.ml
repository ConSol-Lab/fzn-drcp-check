open Lexing
open Printf
open Drcpcheck_core.Checker

exception ParseError of string

let print_position lexbuf source_name =
  let pos = lexbuf.lex_curr_p in
  match source_name with
  | Some name -> sprintf "%s:%d:%d" name pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
  | None -> sprintf "%d:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let rec token_buffer lexbuf : MenhirLibParser.Inter.buffer =
  lazy (MenhirLibParser.Inter.Buf_cons
          (Lexer.read_token lexbuf, token_buffer lexbuf))

let parse_fuel = Big_int_Z.big_int_of_int 60

let parse lexbuf source_name =
  let err msg =
    let pos = print_position lexbuf source_name in
    raise (ParseError (sprintf "%s: %s\n" pos msg)) in
  let buf = token_buffer lexbuf in
  let ast =
    match model parse_fuel buf with
    | MenhirLibParser.Inter.Parsed_pr (ast, _rest) -> ast
    | MenhirLibParser.Inter.Fail_pr_full (_, _)    -> err "syntax error"
    | MenhirLibParser.Inter.Timeout_pr             -> err "timeout" in
  match Lower.to_constraint_problem ast with
  | Inl csp -> csp
  | Inr msg -> err ("cannot lower FlatZinc model: " ^ msg)
