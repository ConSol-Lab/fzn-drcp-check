## Checker modifications

The checker has been modified in just one way. Namely, the requirement that every IntervalVariable should evaluate to the same value if they share the same name. Therefore, the following was added to `Assignment` (in `Variable.v`):

```
find_value_eq_name : forall (v1 v2 : Var), var_name v1 = var_name v2 -> find_value v1 = find_value v2
```

We also add a function that extracts the name of any variable:

```
Definition var_name (v : Var) : string :=
  match v with
  | interval v_i => v_i.(name)
  end.
```

## Cumulative

The cumulative implementation is spread over a number of files.

First, a file `Utility.v` provides useful definitions and lemmas that are not related to CP. In particular, we define:

```
Definition build_range (start_incl : Z) (end_incl : Z) : list Z := ...
```

As the name implies, it defines a range between `start_incl` and `end_incl` and is used by cumulative to generate a list of times to check.

Furthermore, it defines `sub_list`, which is a stronger form of inclusion on lists, where the count of each element is less than in the larger list, to ensure that sums over the smaller list are indeed smaller than the larger list.

```
Definition sub_list {A} (eq_dec : forall x y : A, {x = y}+{x <> y} ) (l1 l2 : list A) :=
  (forall a, In a l1 -> (count_occ eq_dec l1 a <= count_occ eq_dec l2 a)%nat).
```

To aid with proofs over sub_list, it defines `remove_once` that removes a particular element at most once (as opposed to the stdlib's version, which removes all instances of an element). A number of lemmas about `sub_list` and `remove_once` are included that are used for cumulative.

Next, the file `Cumulative.v` defines the most important definitions and types that are used in Cumulative. The main idea is that looking at that file is enough to determine that the specification of cumulative matches what we want it to. To be sure of the cumulative checker's soundness, we only need to check that there is a cumulative case in `ConstraintProblem.v` that actually uses the definition in `Cumulative.v`, that the definitions in that file are correct and that the proofs in `Proof.v` succeed.

We will now go into more detail on these definitions.

### `Cumulative.v`

For now, we define a cumulative constraint as follows:

```
Record CumulativeConstraint :=
  {
    capacity: N;
    vs: list (Var * N * N);
    horizon_start : Z;
    horizon_end : Z;
    horizon_consistent : horizon_start <= horizon_end
  }.
```

The horizons could in the future be inferred from the variable bounds, this was mostly done to make the initial implementation easier.

Now, we determine that an assignment satisfies a particular constraint if the following function returns true:

```
Definition cumulative_decide (constraint : CumulativeConstraint) (a : Assignment) : bool :=
  let c_activities := activity_list constraint a in
  forallb 
    (fun t => 
      usage_sum (activities_at_t c_activities t) <=? constraint.(capacity)
    )
    (ZRange.build_range constraint.(horizon_start) constraint.(horizon_end))
.
```

Here `activity_list` converts the `vs : list (Var * N * N)` in the constraint into a list of activities with start time set to the value of the associated variable using the assignment. `usage_sum` is defined as the sum of the usages of a list of activities, where we first filter the activities to only include activities active at a certain time.

...

### Proof

Our goal is to validate inferences made using the cumulative constraint. We add an inference rule, "cumulative", which checks the validity of an inference that names a particular cumulative constraint.

Our checker, given an inference, returns `true` when the inference is valid and `false` when it is invalid or it cannot determine its validity.

For soundness, the following must hold:

```
given any assignment a,
  - if it satisfies the cumulative constraint
  - and our checker returns that an inference is valid
  - we must have that the inference is indeed valid for that assignment 
```

We implement the checker in such a way that it does not try to exactly reproduce the inference, but it simply negates it and returns true if there a conflict. This is simpler, because the negation of an inference `p /\ q /\ ... -> r` is equivalent to `p /\ q /\ ... /\ not r`. Since each of `p, q, ..., r` are atomic constraints, if we have a conjunction of them we can constrain our variables using all of them. 

In more detail, we want to prove, given premises `a_satisfies_c` (assignment `a` satisfies the constraint `c`) and `checker_validates_inference` (the checker determines that the inference is true) that `inference_is_valid_for_a` (the inference is true for a).

Now, again, our checker works by assuming the negation of the inference and deriving a conflict. So we can prove `checker_validates_inference` and `NOT inference_is_valid_for_a` implies that `NOT a_satisfies_c`. This is then enough to prove the above.

#### validates -> conflict

We now discuss how we prove that if the checker returns true and the negation of the inference is true, we have that the constraint is not satisfied.

First notice a cumulative constraint is not satisfied when there is a time t within the horizon where the summed usages of activities active at t is greater than the capacity.

We therefore seek to show that when our checker returns true, such a time t indeed exists. For this we must inspect the implementation of our checker.

First, it determines lower and upper bounds on all variables in the constraint from all the atomic constraints that we know are true based on negation of the inference holding. We use a general function called `apply_atomics_to_variables`, defined in `Domain.v` (see below for more details). 

We then use the function `find_overloaded_t_with_mandatory`, which iterates over all timepoints. At each timepoint, it checks, using mandatory time reasoning, whether an activity is surely active at that time point based on the computed bounds. If it is active, it is included in the sum calculation.

For computing this sum, we use `res_sum`, which is somewhat more complicated than strictly necessary as it returns early once the sum exceeds the capacity and returns which activities it looked at. This could be useful for completeness and actually building a propagator.

At this point, we quite readily find that the sum of the mandatory activities using the bounds is greater than the capacity, but this must be related to the actual particular solution at hand, which we know satisfies all the atomic constraints used to determine the bounds.

We first use the properties of the sum function we define to reduce our proof to ensuring that the activities active at t determined using the bounds `activities_bounds_active_at t
bounds`, are a sub_list of the activities active at time t of the particular solution. 

This can be reduced to a simple list inclusion if we know that the former list has no duplicates. This is not trivial to show (it would require showing that a number of successive functions used to compute the bounds are injective), so to make the proof easier we simply wrap the bounds computation in a `nodup`.

Having done that, we need to show that given a computed bound active at t, there exists an activity that is active at t. 

We now use the correctness of `apply_atomics_to_variables` that there exists a list of atomic constraints that are valid that imply the bounds found. For this we use an inductive prop called `Atomic_proof` which can be built only from increasingly tight bounds, even using not equals on the edges. Since we added the assumption that for equal variable names an assignment must assign equal values, if we know that all the atomics hold for an `Atomic_proof`, that means all variables with matching name and initial bounds obey the bound of the `Atomic_proof`.

Furthermore, given the definition of how we convert the constraint to intervals, we can find such a matching variable. This allows us to construct an activity that is indeed active at t. We finally use the `active_at` lemma to indeed show that the activity is indeed active at t using mandatory reasoning.