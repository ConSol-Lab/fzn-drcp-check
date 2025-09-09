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
%token BOOL
%token CONSTRAINT
%token PREDICATE
%token MINIMIZE
%token MAXIMIZE
%token DOUBLE_PERIOD
%token DOUBLE_COLON
%token COLON
%token SEMICOLON
%token SOLVE
%token SATISFY
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

model: list(predicate); consts = constants; const_arrays = constant_arrays; vars = variables; var_arrs = var_arrays; cs = constraints; solve_item; EOF { 
    to_constraint_problem { 
        ast_constants = consts;
        ast_constant_arrays = const_arrays;
        ast_variables = vars; 
        ast_variable_arrays = var_arrs;
        ast_constraints  = cs;
    }  
};

predicate: PREDICATE; IDENT; OPEN_PAREN; separated_list(COMMA, predicate_parameter); CLOSE_PAREN; SEMICOLON {}
predicate_parameter: predicate_parameter_type; COLON; IDENT {}
predicate_parameter_type:
    | basic_predicate_parameter_type {}
    | ARRAY; OPEN_BRACKET; INT; CLOSE_BRACKET; OF; basic_predicate_parameter_type {}
basic_predicate_parameter_type:
    | BOOL {}
    | INT {}
    | VAR; BOOL {}
    | VAR; INT {}

solve_item: 
    | SOLVE; annotation_list; SATISFY; SEMICOLON {}
    | SOLVE; annotation_list; MINIMIZE; IDENT; SEMICOLON {}
    | SOLVE; annotation_list; MAXIMIZE; IDENT; SEMICOLON {}


constants: cs = list(constant); { to_coq_map Coq_smap.empty Coq_smap.add cs };
constant: INT; COLON; name = IDENT; EQUALS; value = INT_LITERAL; SEMICOLON { (name, value) }

constant_arrays: vals = list(constant_array) { to_coq_map Coq_smap.empty Coq_smap.add vals };
constant_array: ARRAY; OPEN_BRACKET; int_interval; CLOSE_BRACKET; OF; INT; COLON; name = IDENT; EQUALS; value = int_literal_array; SEMICOLON { (name, value) };

variables: vars = list(variable) { to_coq_map Coq_smap.empty Coq_smap.add vars };
variable: 
    | VAR; BOOL; COLON; name = IDENT; annotation_list; SEMICOLON { (name, Coq_interval (Big_int_Z.zero_big_int, Big_int_Z.zero_big_int)) }
    | VAR; dom = int_domain; COLON; name = IDENT; annotation_list; SEMICOLON { (name, dom) }
    | VAR; dom = int_domain; COLON; name = IDENT; annotation_list; EQUALS; assigned = INT_LITERAL; SEMICOLON
        { if dom = Coq_interval (assigned, assigned) then (name, dom) else failwith "Assignment operator only supported on variables with singleton domains." }
    ;

var_arrays: arrays = list(var_array) { to_coq_map Coq_smap.empty Coq_smap.add arrays };
var_array: ARRAY; OPEN_BRACKET; int_interval; CLOSE_BRACKET; OF; VAR; INT; COLON; name = IDENT; annotation_list; EQUALS; OPEN_BRACKET; array = separated_list(COMMA, constr_or_ident); CLOSE_BRACKET; SEMICOLON { (name, array) };

int_domain: dom = int_interval { Coq_interval ((fst dom), (snd dom)) };
int_interval: lb = INT_LITERAL; DOUBLE_PERIOD; ub = INT_LITERAL { (lb, ub) };

constraints: cs = list(constr) { cs };
constr: CONSTRAINT; name = IDENT; args = delimited(OPEN_PAREN, constraint_args, CLOSE_PAREN); annotation_list; SEMICOLON { { constr_name = name; constr_args = args } };
constraint_args: args = separated_list(COMMA, constraint_arg); { args }
constraint_arg: 
    | name = IDENT { Ident name }
    | value = INT_LITERAL { Constant value }
    | arr = delimited(OPEN_BRACKET, separated_list(COMMA, constr_or_ident), CLOSE_BRACKET) { Array arr }

constr_or_ident:
    | name = IDENT { Ident name }
    | value = INT_LITERAL { Constant value }

annotation_list: list(preceded(DOUBLE_COLON, annotation)) {};
annotation: 
    | IDENT {}
    | IDENT; delimited(OPEN_PAREN, separated_list(COMMA, ann_expr), CLOSE_PAREN) {}

ann_expr:
    | basic_ann_expr {}
    | delimited(OPEN_BRACKET, separated_list(COMMA, basic_ann_expr), CLOSE_BRACKET) {}

basic_ann_expr:
    | basic_literal_expr {}
    | annotation {}

basic_literal_expr:
    | INT_LITERAL {}
    | int_interval {}

int_literal_array: OPEN_BRACKET; ints = separated_list(COMMA, INT_LITERAL); CLOSE_BRACKET { ints }
