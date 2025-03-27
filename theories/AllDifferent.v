Require Import Coq.Strings.String.
Require Import Checker.Domain.
Require Import Checker.Variable.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.


Record AllDifferentConstraint :=
  {
    vars_ad : sstr.t;
    var_ad_bounds : list zn_interval;
    consistency : length var_ad_bounds = sstr.cardinal vars_ad
  }.

Definition get_vars (c : AllDifferentConstraint) : list Var :=
  map 
  (fun x =>
    match x with
    | (x, (lb, x_size)) =>
      interval {| name := x; lower_bound := lb; size := N.to_nat x_size |}
    end
  )
  (combine (sstr.elements c.(vars_ad)) c.(var_ad_bounds)).

Definition valuation_from_assignment (c : AllDifferentConstraint) (a : Assignment) : string -> Z :=
  let vs := get_vars c in
  fun x =>
    match find (fun v =>
      match v with
      | interval v =>
        (v.(name) =? x)%string
      end
    ) vs with
    | None => Z0
    | Some v => a.(find_value) v
    end
  .

Definition AllDifferent (c : sstr.t) (v : string -> Z) : Prop :=
  (forall (x y : string), 
  x <> y -> sstr.In x c -> sstr.In y c -> v x <> v y).

Definition find_conflict_filter_f (n : Z) (el: (Z * string)) :=
  let (n', _) := el in (n =? n')%Z.

Definition find_conflict (x : string) (n : Z) (values : sintstr.t) : option (Z * string) := 
  sintstr.choose (sintstr.filter (find_conflict_filter_f n) values).

Definition values_or_conflict (x : string) (n : Z) (acc : option (string * string) * sintstr.t) :=
  let (maybeConfl, values) := acc in
    match maybeConfl with
    | Some confl => (Some confl, values)
    | None => match find_conflict x n values with
              | Some (_, y) => (Some (x, y), values)
              | None => (None, sintstr.add (n, x) values)
              end
    end
.

Definition all_different_fold_f (v : string -> Z) (x : string) (acc : option (string * string) * sintstr.t) :=
  values_or_conflict x (v x) acc.

Definition all_different_fold (vs : sstr.t) (v : string -> Z) :=
  sstr.fold (all_different_fold_f v) vs (None, sintstr.empty).

Definition dec_all_different (vs : sstr.t) (v : string -> Z) : bool :=
  match all_different_fold vs v with
  | (Some _, _) => false
  | (None, _) => true
  end
.

Definition alldifferent_decide (constraint : AllDifferentConstraint) (a : Assignment) : bool :=
  let valuation := valuation_from_assignment constraint a in
  dec_all_different constraint.(vars_ad) valuation
.



(* Definition ex_confl_set (st : state) (vs : vars) := 
(exists (confl_vars : vars), sstr.Subset confl_vars vs /\ dom_size (vars_union_domain st confl_vars) < vars_len confl_vars). *)