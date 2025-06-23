%{
open Drcpcheck_core.Checker.Maps
open Drcpcheck_core.Checker.ProofFacts
open Big_int_Z
open Ast
%}

%token ATOMIC_DEFINITION
%token EOL
%token EOF

%type <ast> proof
%type <string * coq_BoundAtomic> atom_definition

%start proof
%%

proof: 
    | EOF { { atomics = Coq_smap.empty; steps = [] } }
    | new_atom = atom_definition; rest = proof { { atomics = Coq_smap.add (fst new_atom) (snd new_atom) rest.atomics; steps = rest.steps }  }
    ;

atom_definition: EOL { ("1", ("x1", { atm_cmp = Coq_less_equal; atm_val = zero_big_int })) }
