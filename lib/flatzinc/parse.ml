open Lexing
open Lexer
open Printf

exception ParseError of string

let print_position lexbuf source_name =
  let pos = lexbuf.lex_curr_p in
  match source_name with
  | Some name ->
      sprintf "%s:%d:%d" name pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
  | None -> sprintf "%d:%d" pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse lexbuf source_name =
  try Parser.model Lexer.read_token lexbuf with
  | SyntaxError msg ->
      let position = print_position lexbuf source_name in
      let msg = sprintf "%s: %s\n" position msg in
      raise (ParseError msg)
  | Parser.Error ->
      let position = print_position lexbuf source_name in
      let msg = sprintf "%s: syntax error\n" position in
      raise (ParseError msg)
