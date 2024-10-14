%{
open Litmap
%}

%token <int> INT
%token <string> IDENT 
%token LBRACKET
%token RBRACKET
%token LEQ
%token GEQ
%token EQ
%token NE
%token EOF
%token EOL

%type <predicate> predicate_list
%type <comparator> comparator

%start <litmap> litmap
%%

litmap:
    | EOF {Printf.printf "EMPTY"; empty }
    | lit_id = INT; preds = predicate_list; EOL; map = litmap
        { Printf.printf "id: %d" lit_id; add lit_id preds map }
    ;

predicate_list:
    | LBRACKET; ident = IDENT; comp = comparator; value = INT; RBRACKET
        { { variable = ident; comparator = comp; value = value } }
    ;

comparator:
    | LEQ { LessEqual }
    | GEQ { GreaterEqual }
    | EQ { Equal }
    | NE { NotEqual }
    ;
