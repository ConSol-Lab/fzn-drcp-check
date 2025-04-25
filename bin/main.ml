open Fzn_drcp_check.Checker

let str_to_char_list s = List.init (String.length s) (String.get s)

let n_of_int n =
  let rec pos_of_int n =
    if n = 1 then XH
    else if n mod 2 = 0 then XO (pos_of_int (n / 2))
    else XI (pos_of_int (n / 2))
  in
  if n = 0 then N0 else Npos (pos_of_int n)

let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (let rec f n = if n = 1 then XH else if n mod 2 = 0 then XO (f (n / 2)) else XI (f (n / 2)) in f n)
  else Zneg (let rec f n = if n = 1 then XH else if n mod 2 = 0 then XO (f (n / 2)) else XI (f (n / 2)) in f (-n))

let nat_of_int n =
  let rec f n = if n = 0 then O else S (f (n - 1)) in f n

let mk_inf (lhs : atomic list) (rhs : atomic option) : atomic list =
  let lhs_neg = List.map atomic_not lhs in
  match rhs with
  | None -> lhs_neg
  | Some r -> lhs_neg @ [r]

(* === Example 1: Mandatory conflict === *)
let var_x = { name = str_to_char_list "x"; lower_bound = Z0; size0 = nat_of_int 20 }
let var_y = { name = str_to_char_list "y"; lower_bound = Z0; size0 = nat_of_int 20 }

let constr1 = {
  capacity = n_of_int 1;
  vs = [
    ((var_x, n_of_int 4), n_of_int 1);
    ((var_y, n_of_int 3), n_of_int 1)
  ];
  horizon_start = z_of_int 0;
  horizon_end = z_of_int 6
}

(* === Example 2: 1-step overlap === *)
let var_x2 = { name = str_to_char_list "x"; lower_bound = Z0; size0 = nat_of_int 20 }
let var_y2 = { name = str_to_char_list "y"; lower_bound = Z0; size0 = nat_of_int 20 }

let constr2 = {
  capacity = n_of_int 1;
  vs = [
    ((var_x2, n_of_int 4), n_of_int 1);
    ((var_y2, n_of_int 1), n_of_int 1)
  ];
  horizon_start = z_of_int 0;
  horizon_end = z_of_int 6
}


(* === Example 3: Multi-step (simple) === *)

(* === Example 4: Multi-step (duration two) === *)
let var_y3 = { name = str_to_char_list "y"; lower_bound = Z0; size0 = nat_of_int 20 }

let constr4 = {
  capacity = n_of_int 1;
  vs = [
    ((var_x2, n_of_int 4), n_of_int 1);
    ((var_y3, n_of_int 2), n_of_int 1)
  ];
  horizon_start = z_of_int 0;
  horizon_end = z_of_int 6
}

(* === Example 5: Multi-step (with hole) === *)
let var_z5 = { name = str_to_char_list "z"; lower_bound = Z0; size0 = nat_of_int 20 }

let constr5 = {
  capacity = n_of_int 1;
  vs = [
    ((var_z5, n_of_int 2), n_of_int 1);
    ((var_x2, n_of_int 1), n_of_int 1);
    ((var_y3, n_of_int 2), n_of_int 1)
  ];
  horizon_start = z_of_int 0;
  horizon_end = z_of_int 8
}


let fact1 = mk_inf [
  { var0 = var_x; comparator = Greater_equal; value = z_of_int 0 };
  { var0 = var_x; comparator = Less_equal; value = z_of_int 2 };
  { var0 = var_y; comparator = Greater_equal; value = z_of_int 1 };
  { var0 = var_y; comparator = Less_equal; value = z_of_int 3 };
] None

let fact2 = mk_inf [
  { var0 = var_x2; comparator = Greater_equal; value = z_of_int 0 };
  { var0 = var_x2; comparator = Less_equal; value = z_of_int 2 };
  { var0 = var_y2; comparator = Greater_equal; value = z_of_int 2 };
] (Some { var0 = var_y2; comparator = Greater_equal; value = z_of_int 3 })

let fact3 = mk_inf [
  { var0 = var_x2; comparator = Greater_equal; value = z_of_int 0 };
  { var0 = var_x2; comparator = Less_equal; value = z_of_int 2 };
  { var0 = var_y2; comparator = Greater_equal; value = z_of_int 2 };
] (Some { var0 = var_y2; comparator = Greater_equal; value = z_of_int 4 })

let fact4 = mk_inf [
  { var0 = var_x2; comparator = Greater_equal; value = z_of_int 0 };
  { var0 = var_x2; comparator = Less_equal; value = z_of_int 2 };
  { var0 = var_y3; comparator = Greater_equal; value = z_of_int 1 };
] (Some { var0 = var_y3; comparator = Greater_equal; value = z_of_int 4 })

let fact5 = mk_inf [
  { var0 = var_x2; comparator = Greater_equal; value = z_of_int 0 };
  { var0 = var_x2; comparator = Less_equal; value = z_of_int 0 };
  { var0 = var_z5; comparator = Greater_equal; value = z_of_int 2 };
  { var0 = var_z5; comparator = Less_equal; value = z_of_int 2 }; 
  { var0 = var_y3; comparator = Greater_equal; value = z_of_int 0 };
] (Some { var0 = var_y3; comparator = Greater_equal; value = z_of_int 4 })

let rec positive_to_int = function
  | XI p -> 2 * (positive_to_int p) + 1
  | XO p -> 2 * (positive_to_int p)
  | XH -> 1

let rec nat_to_int = function
  | O -> 0
  | S n -> 1 + nat_to_int n

let n_to_int = function
  | N0 -> 0
  | Npos p -> positive_to_int p

let z_to_int = function
  | Z0 -> 0
  | Zpos p -> positive_to_int p
  | Zneg p -> -(positive_to_int p)

(* Updated string conversion functions using decimal representation *)
let string_of_n n = string_of_int (n_to_int n)
let string_of_z z = string_of_int (z_to_int z)

let cumulative_checker_debug inference constraint1 =
  Printf.printf "Starting cumulative_checker_debug\n";
  Printf.printf "Horizon: %d to %d\n" 
    (z_to_int constraint1.horizon_start) 
    (z_to_int constraint1.horizon_end);
    
  let times =
    ZRange.build_range constraint1.horizon_start constraint1.horizon_end
  in
  Printf.printf "Times range built with %d elements\n" (List.length times);
  
  Printf.printf "Constraint capacity: %d\n" (n_to_int constraint1.capacity);
  Printf.printf "Inference list contains %d elements\n" (List.length inference);
  
  Printf.printf "Calling inferred_cumulative_bounds...\n";
  match inferred_cumulative_bounds constraint1 inference with
  | [] -> 
      Printf.printf "inferred_cumulative_bounds returned empty list\n";
      false
  | p :: l ->
      let bounds = p :: l in
      Printf.printf "inferred_cumulative_bounds returned %d elements\n" (List.length bounds);
      
      (* Print some info about the first few bounds *)
      List.iteri (fun i ((name, interval), (duration, resource)) ->
          if i < 5 then  (* Limit to first 5 to avoid overflow *)
            let lower_bound = z_to_int (fst interval) in
            let size = n_to_int (snd interval) in
            let upper_bound = lower_bound + size in
            
            Printf.printf "  Bound %d: %s [%d,%d] Duration=%d Resource=%d\n" 
              i
              (String.concat "" (List.map (String.make 1) name))
              lower_bound
              upper_bound
              (n_to_int duration)
              (n_to_int resource)
        ) bounds;
      
      Printf.printf "Calling resource_profile...\n";
      match resource_profile constraint1.capacity bounds times with
      | Profile_usages r_profile ->
          Printf.printf "resource_profile returned Profile_usages with %d elements\n" 
            (List.length r_profile);
          
          (* Print some resource profile points *)
          List.iteri (fun i (time, usage) ->
              if i < 10 then  (* Limit to first 10 *)
                Printf.printf "  Profile point %d: time=%d usage=%d\n" 
                  i
                  (z_to_int time)
                  (n_to_int usage)
            ) r_profile;
          
          let conflict_exists = existsb
            (cannot_schedule_activity_w_profile constraint1.capacity r_profile)
            bounds
          in
          Printf.printf "existsb check returned: %b\n" conflict_exists;
          conflict_exists
          
      | Profile_conflict conflict_info ->
          Printf.printf "resource_profile returned Profile_conflict\n";
          true
(* === Run and print results === *)

let () =
  let r1 = cumulative_checker fact1 constr1 in
  let r2 = cumulative_checker fact2 constr2 in
  let r3 = cumulative_checker fact3 constr2 in
  let r4 = cumulative_checker fact4 constr4 in
  Printf.printf "Mandatory Conflict: %b\n" r1;
  Printf.printf "1-step: %b\n" r2;
  Printf.printf "Multi-step Simple: %b\n" r3;
  Printf.printf "Multi-step Hole: %b\n" r4

let () =
  Printf.printf "---------- Test case 1 ----------\n";
  let r1 = cumulative_checker_debug fact1 constr1 in
  Printf.printf "Result: %b\n\n" r1;
  
  Printf.printf "---------- Test case 2 ----------\n";
  let r2 = cumulative_checker_debug fact2 constr2 in
  Printf.printf "Result: %b\n\n" r2;
  
  Printf.printf "---------- Test case 3 ----------\n";
  let r3 = cumulative_checker_debug fact3 constr2 in
  Printf.printf "Result: %b\n\n" r3;
  
  Printf.printf "---------- Test case 4 ----------\n";
  let r4 = cumulative_checker_debug fact4 constr4 in
  Printf.printf "Result: %b\n\n" r4;

  Printf.printf "---------- Test case 5 ----------\n";
  let r5 = cumulative_checker_debug fact5 constr5 in
  Printf.printf "Result: %b\n\n" r5;


(* open Cmdliner
open Fzn_drcp_check
open Conversion

let read_proof proof_file =
  let parsed_proof = Fzn_drcp_check_parsing.parse_proof proof_file in
  Printf.printf "len: %d\n" (List.length parsed_proof.steps);
  convert_proof parsed_proof

let parse_model _ = { Checker.constraints = []; Checker.variables = [] }

(** Convert a `nat` extracted from Coq to an OCaml integer. *)
let rec nat_to_int = function Checker.O -> 0 | Checker.S n -> 1 + nat_to_int n

let check_proof model proof =
  if not (Sys.file_exists model) then `Error (false, model ^ ": not a file")
  else if not (Sys.file_exists proof) then `Error (false, proof ^ ": not a file")
  else
    let parsed_proof = read_proof proof in
    let parsed_model = parse_model model in
    match Checker.validate parsed_model parsed_proof with
    | false -> `Ok
      (Printf.printf "Proof is invalid; placeholder for the proof step: %d"
        (nat_to_int Checker.O))
    | true -> `Ok (print_endline "Proof is valid")

let model_t =
  let doc = "The FZN file describing the model." in
  let docv = "FZN" in
  Arg.(required & pos 0 (some string) None & info [] ~docv ~doc)

let proof_t =
  let doc = "The DRCP file containing the proof." in
  let docv = "DRCP" in
  Arg.(required & pos 1 (some string) None & info [] ~docv ~doc)

let cmd =
  let doc = "Check whether a given DRCP file is a proof for a FZN model." in
  let info = Cmd.info "fzn-drcp-check" ~version:"%%VERSION%%" ~doc in
  Cmd.v info Term.(ret (const check_proof $ model_t $ proof_t))

let () = exit (Cmd.eval cmd)

*)