(* menhir --coq does not support parametric rules (list, separated_list,
 * option, preceded, delimited); every list is expanded into explicit
 * X_list / X_list_tail pairs. *)

%{
From Coq Require Import ZArith String List.
From Checker Require Import Utility.
From Checker Require Import Spec.
From FlatZinc Require Import Ast.

Import ListNotations.
Import Utility.Maps.
Import Spec.ConstraintDefinitions.
Import Ast.
%}

%token <Z>      INT_LITERAL
%token <string> IDENT
%token VAR ARRAY OF INT BOOL CONSTRAINT PREDICATE MINIMIZE MAXIMIZE
%token DOUBLE_PERIOD DOUBLE_COLON COLON SEMICOLON
%token SOLVE SATISFY
%token OPEN_BRACKET CLOSE_BRACKET OPEN_PAREN CLOSE_PAREN
%token EQUALS COMMA EOF

%start <Ast.ast> model

%type <IntSet>                           int_domain
%type <Z * Z>                            int_interval
%type <list Z>                           int_literal_array

%type <list decl_item>                   decl_list
%type <decl_item>                        decl_item
%type <list constr>                      constraints constr_list
%type <constr>                           constr
%type <list constr_arg>                  constraint_args
%type <list constr_arg>                  constraint_arg_list
%type <list constr_arg>                  constraint_arg_list_tail
%type <constr_arg>                       constraint_arg
%type <const_or_ident>                   constr_or_ident
%type <list const_or_ident>              constr_or_ident_list
%type <list const_or_ident>              constr_or_ident_list_tail
%type <list Z>                           int_literal_list
%type <list Z>                           int_literal_list_tail

%type <unit>                             solve_item
%type <unit>                             predicate predicate_parameter
%type <unit>                             predicate_parameter_type
%type <unit>                             basic_predicate_parameter_type
%type <list unit>                        predicate_list
%type <list unit>                        predicate_parameter_list
%type <list unit>                        predicate_parameter_list_tail
%type <unit>                             annotation_list annotation
%type <unit>                             ann_expr ann_expr_list ann_expr_list_tail
%type <unit>                             basic_ann_expr basic_ann_expr_list basic_ann_expr_list_tail
%type <unit>                             basic_literal_expr

%%

model:
  | predicate_list
    ds = decl_list
    cs = constraints
    solve_item
    EOF
    { Ast.mk_ast ds cs }

predicate_list:
  | /* empty */                           { [] }
  | predicate predicate_list              { [] }

predicate:
  | PREDICATE IDENT OPEN_PAREN predicate_parameter_list CLOSE_PAREN SEMICOLON
      { tt }

predicate_parameter_list:
  | /* empty */                                                         { [] }
  | predicate_parameter predicate_parameter_list_tail                   { [] }

predicate_parameter_list_tail:
  | /* empty */                                                         { [] }
  | COMMA predicate_parameter predicate_parameter_list_tail             { [] }

predicate_parameter:
  | predicate_parameter_type COLON IDENT                                { tt }

predicate_parameter_type:
  | basic_predicate_parameter_type                                       { tt }
  | ARRAY OPEN_BRACKET INT CLOSE_BRACKET OF basic_predicate_parameter_type { tt }

basic_predicate_parameter_type:
  | BOOL                                                                 { tt }
  | INT                                                                  { tt }
  | VAR BOOL                                                             { tt }
  | VAR INT                                                              { tt }

solve_item:
  | SOLVE annotation_list SATISFY              SEMICOLON                 { tt }
  | SOLVE annotation_list MINIMIZE IDENT       SEMICOLON                 { tt }
  | SOLVE annotation_list MAXIMIZE IDENT       SEMICOLON                 { tt }

(* Scalar-par, array-par, scalar-var, and array-var decls are merged into a
   single [decl_list]. This removes the original grammar's shift/reduce
   ambiguity at the ARRAY boundary (LR(1) can now decide par vs. var from
   the token after OF) and lets menhir certify the completeness proof. *)

decl_list:
  | /* empty */                                                          { [] }
  | hd = decl_item tl = decl_list                                        { hd :: tl }

decl_item:
  | INT COLON name = IDENT EQUALS value = INT_LITERAL SEMICOLON
      { DIParConst name value }
  | ARRAY OPEN_BRACKET int_interval CLOSE_BRACKET
    OF INT COLON name = IDENT EQUALS value = int_literal_array SEMICOLON
      { DIParArray name value }
  | VAR BOOL COLON name = IDENT annotation_list SEMICOLON
      { DIVarScalar name (interval 0%Z 0%Z) }
  | VAR dom = int_domain COLON name = IDENT annotation_list SEMICOLON
      { DIVarScalar name dom }
  | VAR dom = int_domain COLON name = IDENT annotation_list
    EQUALS INT_LITERAL SEMICOLON
      { DIVarScalar name dom }
  | ARRAY OPEN_BRACKET int_interval CLOSE_BRACKET OF
    VAR INT COLON name = IDENT annotation_list EQUALS
    OPEN_BRACKET arr = constr_or_ident_list CLOSE_BRACKET SEMICOLON
      { DIVarArray name arr }

int_domain:
  | dom = int_interval                                                   { interval (fst dom) (snd dom) }

int_interval:
  | lb = INT_LITERAL DOUBLE_PERIOD ub = INT_LITERAL                      { (lb, ub) }

constraints:
  | cs = constr_list                                                     { cs }

constr_list:
  | /* empty */                                                          { [] }
  | hd = constr tl = constr_list                                         { hd :: tl }

constr:
  | CONSTRAINT name = IDENT
    OPEN_PAREN args = constraint_args CLOSE_PAREN
    annotation_list SEMICOLON
      { mk_constr name args }

constraint_args:
  | args = constraint_arg_list                                           { args }

constraint_arg_list:
  | /* empty */                                                          { [] }
  | hd = constraint_arg tl = constraint_arg_list_tail                    { hd :: tl }

constraint_arg_list_tail:
  | /* empty */                                                          { [] }
  | COMMA hd = constraint_arg tl = constraint_arg_list_tail              { hd :: tl }

constraint_arg:
  | name  = IDENT                                                        { CAIdent name }
  | value = INT_LITERAL                                                  { CAConstant value }
  | OPEN_BRACKET arr = constr_or_ident_list CLOSE_BRACKET                { CAArray arr }

constr_or_ident:
  | name  = IDENT                                                        { COIIdent name }
  | value = INT_LITERAL                                                  { COIConstant value }

constr_or_ident_list:
  | /* empty */                                                          { [] }
  | hd = constr_or_ident tl = constr_or_ident_list_tail                  { hd :: tl }

constr_or_ident_list_tail:
  | /* empty */                                                          { [] }
  | COMMA hd = constr_or_ident tl = constr_or_ident_list_tail            { hd :: tl }

annotation_list:
  | /* empty */                                                          { tt }
  | DOUBLE_COLON annotation annotation_list                              { tt }

annotation:
  | IDENT                                                                { tt }
  | IDENT OPEN_PAREN ann_expr_list CLOSE_PAREN                           { tt }

ann_expr_list:
  | /* empty */                                                          { tt }
  | ann_expr ann_expr_list_tail                                          { tt }

ann_expr_list_tail:
  | /* empty */                                                          { tt }
  | COMMA ann_expr ann_expr_list_tail                                    { tt }

ann_expr:
  | basic_ann_expr                                                       { tt }
  | OPEN_BRACKET basic_ann_expr_list CLOSE_BRACKET                       { tt }

basic_ann_expr_list:
  | /* empty */                                                          { tt }
  | basic_ann_expr basic_ann_expr_list_tail                              { tt }

basic_ann_expr_list_tail:
  | /* empty */                                                          { tt }
  | COMMA basic_ann_expr basic_ann_expr_list_tail                        { tt }

basic_ann_expr:
  | basic_literal_expr                                                   { tt }
  | annotation                                                           { tt }

basic_literal_expr:
  | INT_LITERAL                                                          { tt }
  | int_interval                                                         { tt }

int_literal_array:
  | OPEN_BRACKET ints = int_literal_list CLOSE_BRACKET                   { ints }

int_literal_list:
  | /* empty */                                                          { [] }
  | hd = INT_LITERAL tl = int_literal_list_tail                          { hd :: tl }

int_literal_list_tail:
  | /* empty */                                                          { [] }
  | COMMA hd = INT_LITERAL tl = int_literal_list_tail                    { hd :: tl }
