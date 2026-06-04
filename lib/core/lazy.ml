(* Re-export what the extracted MenhirLib code expects from Stdlib.Lazy. *)
type 'a t = 'a Stdlib.Lazy.t
let force = Stdlib.Lazy.force

type ('a, 'b) lazylist =
  | LNil
  | Single of 'b
  | Cons of 'a * ('a, 'b) lazylist
  | Thunk of (unit -> ('a, 'b) lazylist)

(** If l1 is a Thunk, it gets evaluated.*)
let rec append l1 l2 =
  match l1 with
  | LNil -> l2
  | Single _ -> (
      match l2 with
      | LNil -> l1
      | _ ->
          raise
            (Invalid_argument
               "append: cannot append non-nil element to a Single"))
  | Cons (x, xs) -> Cons (x, append xs l2)
  | Thunk f -> append (f ()) l2

(** Appends l1 to l2, terminating the list if l1 is a Single *)
let rec append_terminate l1 l2 =
  match l1 with
  | LNil -> l2
  | Single _ -> l1
  | Cons (x, xs) -> Cons (x, append_terminate xs l2)
  | Thunk f -> append_terminate (f ()) l2

let rec map f g = function
  | LNil -> LNil
  | Single s -> Single (g s)
  | Cons (x, xs) -> Cons (f x, map f g xs)
  | Thunk h -> Thunk (fun () -> map f g (h ()))

let rec map_i f g = function
  | LNil -> LNil
  | Single s -> Single (g s)
  | Cons (x, xs) -> Cons (f x, map_i f g xs)
  | Thunk _ -> raise (Invalid_argument "map_i: cannot map_i over a Thunk")

let ( @ ) l1 l2 = append l1 l2

let rec rev = function
  | LNil -> LNil
  | Single _ as s -> s
  | Cons (x, xs) -> append (rev xs) (Cons (x, LNil))
  | Thunk f -> rev (f ())

let rec rev_i = function
  | LNil -> LNil
  | Single _ as s -> s
  | Cons (x, xs) -> append (rev_i xs) (Cons (x, LNil))
  | Thunk _ -> raise (Invalid_argument "rev_i: cannot reverse a Thunk")

let rec to_list = function
  | LNil -> []
  | Single _ ->
      raise
        (Invalid_argument
           "to_list: cannot convert a Single to a list (type mismatch)")
  | Cons (x, xs) -> x :: to_list xs
  | Thunk f -> to_list (f ())

let rec to_list_i = function
  | LNil -> []
  | Single _ ->
      raise
        (Invalid_argument
           "to_list_i: cannot convert a Single to a list (type mismatch)")
  | Cons (x, xs) -> x :: to_list_i xs
  | Thunk _ ->
      raise (Invalid_argument "to_list_i: cannot convert a Thunk to a list")

let rec of_list = function [] -> LNil | x :: xs -> Cons (x, of_list xs)
let ( +: ) x xs = Cons (x, xs)
