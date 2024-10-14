module IntMap = Map.Make (Int)

type comparator = LessEqual | GreaterEqual | Equal | NotEqual
type predicate = { variable : string; comparator : comparator; value : int }
type litmap = predicate IntMap.t

let empty : litmap = IntMap.empty
let add : int -> predicate -> litmap -> litmap = IntMap.add

let to_string (c : comparator) =
  match c with
  | LessEqual -> "<="
  | GreaterEqual -> ">="
  | NotEqual -> "!="
  | Equal -> "=="
