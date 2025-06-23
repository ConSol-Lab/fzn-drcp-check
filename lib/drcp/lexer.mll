{
open Lexing
open Parser
open Big_int_Z

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }

exception SyntaxError of string

let at_start = ref true
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let int = '-'? ['0'-'9']+

rule read_token =
    parse
    | white { read_token lexbuf }
    | newline { at_start := true; read_token lexbuf }
    | ident   { IDENT (Lexing.lexeme lexbuf) }
    | "a" { at_start := false; ATOMIC_DEFINITION }
    | "i" { at_start := false; INFERENCE }
