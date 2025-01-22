Require Import String.
Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Checker.Atomic.
Require Import Checker.Nogood.
Require Import Checker.Linear.
Require Import Checker.Variable.
Require Import Checker.ConstraintProblem.
Require Import Checker.Proof.


Compute
  let x := interval {|
    name := "x" ;
    lower_bound := 0 ;
    size := 2 ;
  |} in
  let y := interval {|
    name := "y" ;
    lower_bound := 0 ;
    size := 3 ;
  |} in
  let z := interval {|
    name := "z" ;
    lower_bound := 0 ;
    size := 2 ;
  |} in
  let c0 := linear_leq {|
    terms := [(-2, x); (-1, y); (-2, z)] ;
    bound := -2 ;
  |} in
  let c1 := linear_leq {|
    terms := [(-2, x); (-1, y); (2, z)] ;
    bound := 0 ;
  |} in
  let c2 := linear_leq {|
    terms := [(-2, x); (1, y); (-2, z)] ;
    bound := 0 ;
  |} in
  let c3 := linear_leq {|
    terms := [(-2, x); (1, y); (2, z)] ;
    bound := 2 ;
  |} in
  let c4 := linear_leq {|
    terms := [(2, x); (-1, y); (-2, z)] ;
    bound := -2 ;
  |} in
  let c5 := linear_leq {|
    terms := [(2, x); (-1, y); (2, z)] ;
    bound := 0 ;
  |} in
  let csp := {|
    variables := [x; y; z];
    constraints := [c0; c1; c2; c3; c4; c5]
  |} in
  let fact11 := [
    {| var := x ; comparator := greater_equal ; value := 1 |} ;
    {| var := y ; comparator := less_equal ; value := 1 |} ;
    {| var := z ; comparator := greater_equal ; value := 1 |} 
  ] in
  let fact12 := [
    {| var := x ; comparator := greater_equal ; value := 1 |} ;
    {| var := y ; comparator := less_equal ; value := 1 |} ;
    {| var := z ; comparator := less_equal ; value := 0 |} 
  ] in
  let nogood1 := [
    {| var := x ; comparator := greater_equal ; value := 1 |} ;
    {| var := y ; comparator := less_equal ; value := 1 |} 
  ] in
  let fact21 := [
    {| var := x ; comparator := greater_equal ; value := 1 |} ;
    {| var := y ; comparator := greater_equal ; value := 2 |} ;
    {| var := z ; comparator := greater_equal ; value := 1 |} 
  ] in
  let fact22 := [
    {| var := x ; comparator := greater_equal ; value := 1 |} ;
    {| var := y ; comparator := greater_equal ; value := 2 |} ;
    {| var := z ; comparator := less_equal ; value := 0 |} 
  ] in
  let nogood2 := [
    {| var := x ; comparator := greater_equal ; value := 1 |} ;
    {| var := y ; comparator := greater_equal ; value := 2 |}
  ] in
  let nogood3 := [
    {| var := x ; comparator := greater_equal ; value := 1 |}
  ] in
  let fact41 := [
    {| var := x ; comparator := less_equal ; value := 0 |} ;
    {| var := z ; comparator := greater_equal ; value := 1 |} 
  ] in
  let fact42 := [
    {| var := x ; comparator := less_equal ; value := 0 |} ;
    {| var := z ; comparator := less_equal ; value := 0 |} 
  ] in
  let nogood4 := [
    {| var := x ; comparator := less_equal ; value := 0 |}
  ] in
  forallb (fun x => x) [
    validate_inference
      fact11
      [c2]
      linear ;
    validate_inference
      fact12
      [c3]
      linear ;
    rup
      [fact11 ; fact12]
      (map atomic_not nogood1) ;
    validate_inference
      fact21
      [c0]
      linear ;
    validate_inference
      fact22
      [c1]
      linear ;
    rup
      [fact21 ; fact22]
      (map atomic_not nogood2) ;
    rup
      [nogood1 ; nogood2]
      (map atomic_not nogood3) ;
    validate_inference
      fact41
      [c4]
      linear ;
    validate_inference
      fact42
      [c5]
      linear ;
    rup
      [fact41 ; fact42]
      (map atomic_not nogood4) ;
    rup
      [nogood3 ; nogood4]
      (map atomic_not nil) ;
    validate csp
    {|
      steps := [
        inference fact11 [2%nat] linear ;
        inference fact12 [3%nat] linear ;
        nogood nogood1 [fact11 ; fact12] ;
        inference fact21 [0%nat] linear ;
        inference fact22 [1%nat] linear ;
        nogood nogood2 [fact21 ; fact22] ;
        nogood nogood3 [nogood1 ; nogood2] ;
        inference fact41 [4%nat] linear ;
        inference fact42 [5%nat] linear ;
        nogood nogood4 [fact41 ; fact42] ;
        nogood [] [nogood3 ; nogood4]
      ] ;
      conclusion := unsat
    |}
  ].
