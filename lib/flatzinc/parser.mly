%{
open Drcpcheck_core.Checker.ConstraintDefinitions
open Drcpcheck_core.Checker.Maps
open Ast
%}

%token <Big_int_Z.big_int> INT_LITERAL
%token <string> IDENT
%token VAR
%token ARRAY
%token OF
%token INT
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

model: constant_arrays; vars = variables; var_arrays; EOF { 
    to_constraint_problem { 
        ast_constants = Coq_smap.empty;
        ast_constant_arrays = Coq_smap.empty;
        ast_variables = vars; 
        ast_variable_arrays = Coq_smap.empty;
        ast_constraints  = [];
    }  
};

constant_arrays: vals = list(constant_array) { vals };
constant_array: ARRAY; OPEN_BRACKET; int_interval; CLOSE_BRACKET; OF; INT; COLON; name = IDENT; EQUALS; int_literal_array; SEMICOLON { name };

variables: vars = list(variable) { List.fold_left (fun acc (name, dom) -> Coq_smap.add name dom acc) Coq_smap.empty vars };
variable: VAR; dom = int_domain; COLON; name = IDENT; option(annotation_list); SEMICOLON { (name, dom) }

annotation_list: DOUBLE_COLON; separated_list(COMMA, annotation) {};
annotation: IDENT; option(annotation_arguments) {};
annotation_arguments: OPEN_PAREN; OPEN_BRACKET; int_interval; CLOSE_BRACKET; CLOSE_PAREN {};

int_literal_array: OPEN_BRACKET; ints = separated_list(COMMA, INT_LITERAL); CLOSE_BRACKET { ints }

var_arrays: arrays = list(var_array) { arrays };
var_array: ARRAY; OPEN_BRACKET; int_interval; CLOSE_BRACKET; OF; VAR; INT; COLON; name = IDENT; option(annotation_list); EQUALS; OPEN_BRACKET; separated_list(COMMA, IDENT); CLOSE_BRACKET; SEMICOLON { name };

int_domain: dom = int_interval { Coq_interval ((fst dom), (snd dom)) };
int_interval: lb = INT_LITERAL; DOUBLE_PERIOD; ub = INT_LITERAL { (lb, ub) };
