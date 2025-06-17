%{
open Drcpcheck_core.Checker.ConstraintDefinitions
open Drcpcheck_core.Checker.Maps
open Ast

let to_coq_map empty add pairs = List.fold_left (fun acc (key, value) -> add key value acc) empty pairs
%}

%token <Big_int_Z.big_int> INT_LITERAL
%token <string> IDENT
%token VAR
%token ARRAY
%token OF
%token INT
%token CONSTRAINT
%token DOUBLE_PERIOD
%token DOUBLE_COLON
%token COLON
%token SEMICOLON
%token OPEN_BRACKET
%token CLOSE_BRACKET
%token OPEN_PAREN
%token CLOSE_PAREN
%token EQUALS
%token COMMA
%token EOF

%type <Drcpcheck_core.Checker.ConstraintDefinitions.coq_ConstraintProblem> model
%type <coq_IntSet Coq_smap.t> variables
%type <coq_IntSet> int_domain
%type <Big_int_Z.big_int * Big_int_Z.big_int> int_interval
%type <Big_int_Z.big_int list> int_literal_array

%start model
%%

model: consts = constants; const_arrays = constant_arrays; vars = variables; var_arrs = var_arrays; cs = constraints; EOF { 
    to_constraint_problem { 
        ast_constants = consts;
        ast_constant_arrays = const_arrays;
        ast_variables = vars; 
        ast_variable_arrays = var_arrs;
        ast_constraints  = cs;
    }  
};

constants: cs = list(constant); { to_coq_map Coq_smap.empty Coq_smap.add cs };
constant: INT; COLON; name = IDENT; EQUALS; value = INT_LITERAL; SEMICOLON { (name, value) }

constant_arrays: vals = list(constant_array) { to_coq_map Coq_smap.empty Coq_smap.add vals };
constant_array: ARRAY; OPEN_BRACKET; int_interval; CLOSE_BRACKET; OF; INT; COLON; name = IDENT; EQUALS; value = int_literal_array; SEMICOLON { (name, value) };

variables: vars = list(variable) { to_coq_map Coq_smap.empty Coq_smap.add vars };
variable: VAR; dom = int_domain; COLON; name = IDENT; option(annotation_list); SEMICOLON { (name, dom) }

annotation_list: DOUBLE_COLON; separated_list(COMMA, annotation) {};
annotation: IDENT; option(annotation_arguments) {};
annotation_arguments: OPEN_PAREN; OPEN_BRACKET; int_interval; CLOSE_BRACKET; CLOSE_PAREN {};

int_literal_array: OPEN_BRACKET; ints = separated_list(COMMA, INT_LITERAL); CLOSE_BRACKET { ints }

var_arrays: arrays = list(var_array) { to_coq_map Coq_smap.empty Coq_smap.add arrays };
var_array: ARRAY; OPEN_BRACKET; int_interval; CLOSE_BRACKET; OF; VAR; INT; COLON; name = IDENT; option(annotation_list); EQUALS; OPEN_BRACKET; array = separated_list(COMMA, IDENT); CLOSE_BRACKET; SEMICOLON { (name, List.map (fun var_name -> (Ident var_name : const_or_ident)) array) };

int_domain: dom = int_interval { Coq_interval ((fst dom), (snd dom)) };
int_interval: lb = INT_LITERAL; DOUBLE_PERIOD; ub = INT_LITERAL { (lb, ub) };

constraints: cs = list(constr) { cs };
constr: CONSTRAINT; name = IDENT; args = delimited(OPEN_PAREN, constraint_args, CLOSE_PAREN); SEMICOLON { { constr_name = name; constr_args = args } };
constraint_args: args = separated_list(COMMA, constraint_arg); { args }
constraint_arg: 
    | name = IDENT { Ident name }
    | value = INT_LITERAL { Constant value }
    | arr = delimited(OPEN_BRACKET, separated_list(COMMA, constr_or_ident), CLOSE_BRACKET) { Array arr }

constr_or_ident:
    | name = IDENT { Ident name }
    | value = INT_LITERAL { Constant value }
