(* Definition cumulative_checker (inference : list Atomic) (constraint : CumulativeConstraint) : bool :=
  let times := (ZRange.build_range constraint.(horizon_start) constraint.(horizon_end)) in
  match inferred_cumulative_bounds constraint inference with
  | None => false
  | Some bounds => 
    match find_overloaded_t_with_mandatory (constraint.(capacity)) times bounds with
    | None => 
      let r_profile := resource_profile (constraint.(capacity)) bounds times in
      existsb (cannot_schedule_activity_w_profile (constraint.(capacity)) r_profile) bounds 
    | Some _ => true
    end
  end
.

Definition inferred_cumulative_bounds (c : CumulativeConstraint) (inference : list Atomic) :=
  apply_atomics_to_variables (constraint_to_intervals c) (map atomic_not inference). *)