{
open Lexing
open Litmap_parser

exception SyntaxError of string

let next_line lexbuf =
    { lexbuf.lex_curr_p with pos_lnum = lexbuf.lex_curr_p.pos_lnum + 1 }
}

let int = '-'? ['0'-'9'] ['0'-'9']*

let ident = ['A'-'Z' 'a'-'z']['A'-'Z' 'a'-'z' '0'-'9' '_']*

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule token = parse
    | white     { token lexbuf }
    | int       { INT (int_of_string (Lexing.lexeme lexbuf)) }
    | ident     { IDENT (Lexing.lexeme lexbuf) }
    | "<="      { LEQ } 
    | ">="      { GEQ }
    | "=="      { EQ }
    | "!="      { NE }
    | "["       { LBRACKET }
    | "]"       { RBRACKET }
    | newline   { EOL }
    | _ { raise (SyntaxError ("Unexpected char: '" ^ Lexing.lexeme lexbuf ^ "'")) }
    | eof       { EOF }
