Require Import Coq.Strings.String.
Require Import Checker.Domain.
Require Import Checker.Variable.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import Utility.Sets.

Module Z_String_as_OT := OrdersEx.PairOrderedType OrdersEx.Z_as_OT OrdersEx.String_as_OT.
Module sintstr := MSetAVL.Make Z_String_as_OT.


Record AllDifferentConstraint :=
  {
    vars_ad : sstr.t;
    var_ad_bounds : list (Z * N);
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

(* Definition AllDifferent (c : sstr.t) (v : string -> Z) : Prop :=
  (forall (x y : string), 
  x <> y -> sstr.In x c -> sstr.In y c -> v x <> v y).
 *)

Definition FullDomain := sint.t.

(* Note that we materialize each domain because otherwise computing the shared domain is quite expensive. *)
Definition state := string -> FullDomain.



(* Record BoundedDomain := {
  bd_lb : Z;
  bd_ub : Z;
  bd_holes : sint.t
}.

Definition dom_size (dom : BoundedDomain) : Z :=
  dom.(bd_ub) - dom.(bd_lb) + 1 - (Z.of_nat (sint.cardinal dom.(bd_holes))).
 *)
Definition dom_size (dom : FullDomain) : nat := sint.cardinal dom.

Definition vars_dom_union (st : state) (vs : sstr.t) := 
    sstr.fold 
    (fun x acc => sint.union (st x) acc)
    vs 
    sint.empty.

Definition vars_len (vs : sstr.t) : nat := sstr.cardinal vs.

Open Scope nat_scope.

Definition ex_confl_set (st : state) (vs : sstr.t) := 
  exists confl_vars, 
    sstr.Subset confl_vars vs 
      /\ 
    dom_size (vars_dom_union st confl_vars) < vars_len confl_vars.

Definition valuation_in_state (st : state) (vs : sstr.t) (v : string -> Z) : Prop :=
  forall (x : string), sstr.In x vs -> sint.In (v x) (st x).

Definition AllDifferent_sat (st : state) (vs : sstr.t) :=
  exists v, valuation_in_state st vs v -> AllDifferent vs v.

Lemma conflict_if_ex_confl_set (st : state) (vs : sstr.t) :
  ex_confl_set st vs -> ~ AllDifferent_sat st vs.
Proof.
  intros H.
  destruct H as [confl_vars [Hsub Hlt]].
  unfold AllDifferent_sat. intros Halldiff.
  destruct Halldiff as [v [Hdom Hdiff]].
  enough (dom_size (vars_union_domain st confl_vars) >= vars_len confl_vars).
  - apply Nat.lt_nge in Hlt.
    contradiction.
  - apply all_different_subset with (vs' := confl_vars) in Hdiff; try assumption.
    destruct (alldiff_valuation_values_props confl_vars st v Hdiff) as [Hvals Hins].
    rewrite Hvals.
    unfold ge.
    apply sint_prps.subset_cardinal.
    unfold sint.Subset.
    intros n Hin.
    destruct (Hins n Hin)  as [x [Hxin Hvx]].
    subst n.
    specialize (vars_union_domain_correct st confl_vars x Hxin) as Hunion.
    autounfold with short_unfold_db in *.
    apply Hunion.
    apply Hdom.
    apply Hsub.
    exact Hxin.
Qed.

(* Definition ex_confl_set (st : state) (vs : vars) := 
(exists (confl_vars : vars), sstr.Subset confl_vars vs /\ dom_size (vars_union_domain st confl_vars) < vars_len confl_vars). *)