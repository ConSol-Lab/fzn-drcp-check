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
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*
let int = '-'? ['0'-'9']+

rule read_token =
  parse
  | white    { read_token lexbuf }
  | newline  { next_line lexbuf; read_token lexbuf }
  | "%"      { single_line_comment lexbuf }
  | int      { INT_LITERAL (big_int_of_string (Lexing.lexeme lexbuf)) }
  | "var"    { VAR }
  | "array"  { ARRAY }
  | "of"     { OF }
  | "int"    { INT }
  | "::"     { DOUBLE_COLON }
  | ":"      { COLON }
  | ";"      { SEMICOLON }
  | ".."     { DOUBLE_PERIOD }
  | "["      { OPEN_BRACKET }
  | "]"      { CLOSE_BRACKET }
  | "("      { OPEN_PAREN }
  | ")"      { CLOSE_PAREN }
  | "="      { EQUALS }
  | ","      { COMMA }
  | ident    { IDENT (Lexing.lexeme lexbuf) }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
  | eof      { EOF }

and single_line_comment = parse
  | newline { next_line lexbuf; read_token lexbuf }
  | eof { EOF }
  | _ { single_line_comment lexbuf }
