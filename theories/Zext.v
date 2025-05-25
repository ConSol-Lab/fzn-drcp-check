Require Import ZArith.ZArith.
Require Import Structures.Orders.
Require Import Structures.OrdersTac.
Require Import Structures.GenericMinMax.
Require Import Structures.OrdersFacts.
Require Import Lia.

Inductive Zext :=
| zz : Z -> Zext
| neg_inf : Zext
| pos_inf : Zext.

Declare Scope Zext_scope.
Delimit Scope Zext_scope with Zext.
Open Scope Zext_scope.
Module Zext_as_OTF <: UsualOrderedTypeFull'.

  Definition t := Zext.
  Include HasUsualEq <+ UsualIsEq.
  Definition eqb (x y : Zext) :=
    match x, y with
    | neg_inf, neg_inf => true
    | pos_inf, pos_inf => true
    | zz x, zz y => Z.eqb x y
    | _, _ => false
    end.

  Lemma eqb_eq :
    forall x y, eqb x y = true <-> x = y.
  Proof.
    intros x y; destruct x; destruct y; simpl;
    try easy.
    rewrite Z.eqb_eq; split; intros H.
    - now f_equal.
    - now inversion H.
  Qed.

  Include HasEqBool2Dec.

  Definition compare (x y : Zext)
    := match x, y with
       | pos_inf, pos_inf => Eq
       | neg_inf, neg_inf => Eq
       | zz x, zz y => Z.compare x y
       | neg_inf, _ => Lt
       | pos_inf, _ => Gt
       | _, neg_inf => Gt
       | _, pos_inf => Lt
       end.
  
  Infix "?=" := compare (at level 70, no associativity) : Zext_scope.

  Definition lt x y := (x ?= y) = Lt.
  Definition le x y := (x ?= y) <> Gt.

  #[global]
  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
    intros x x' Hx y y' Hy. rewrite Hx, Hy. reflexivity.
  Qed.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
    intros x y.
    unfold CompSpec. unfold lt, eq, compare.
    destruct (compare x y) eqn:Hcmp; unfold compare in Hcmp;
    destruct x as [x| |]; destruct y as [y| |]; simpl in *;
    try discriminate; try rewrite Hcmp; try apply CompEq; try apply CompLt; try apply CompGt; try easy.
    - rewrite Z.compare_eq_iff in Hcmp. subst x; reflexivity.
    - rewrite Z.compare_gt_iff in Hcmp.
      rewrite Z.compare_lt_iff.
      exact Hcmp. 
  Qed.

  #[global]
  Instance lt_strorder : StrictOrder lt.
  Proof.
    split; unfold lt; [ intro x | intros x y z ]; unfold complement;
    unfold compare.
    - destruct x as [x| |]; simpl in *; try easy.
      intros Hx. rewrite Z.compare_lt_iff in Hx.
      lia.
    - destruct x as [x| |]; destruct y as [y| |]; destruct z as [z| |]; simpl in *; try easy.
      repeat rewrite Z.compare_lt_iff.
      lia.
  Qed.
  
  Infix "<=" := le : Zext_scope.
  Infix "<" := lt : Zext_scope.
  
  Lemma le_lteq : forall x y, x<=y <-> x<y \/ x = y.
  Proof.
    intros x y.
    destruct (compare x y) eqn:Hcmp;
    destruct x as [x| |]; destruct y as [y| |]; 
    unfold compare in *; simpl in *;
    try easy; split; intros H; try destruct H as [H | H]; try easy;
    unfold compare in *; try inversion H; try intros Hneg; unfold compare in *; try rewrite Z.compare_eq_iff in *;
    try rewrite Z.compare_lt_iff in *; try rewrite Z.compare_gt_iff in *; try lia.
    - right. now f_equal.
    - right; reflexivity.
    - right; reflexivity.
    - now left.
    - left; reflexivity.
    - left; reflexivity.
    - left; reflexivity.
  Qed.
  Include OTF_LtIsTotal.

  Definition ltb (x y : Zext) : bool :=
    match compare x y with
    | Lt => true
    | _ => false
    end.

  Definition leb (x y : Zext) : bool :=
    match compare x y with
    | Gt => false
    | _ => true
    end.

  Infix "<=?" := leb (at level 70, no associativity) : Zext_scope.

  Infix "<?" := ltb (at level 70, no associativity) : Zext_scope.

  Lemma ltb_lt n m : (n <? m) = true <-> n < m.
  Proof.
    unfold ltb, lt. destruct compare; easy'.
  Qed.

  Lemma leb_le n m : (n <=? m) = true <-> n <= m.
  Proof.
    unfold leb, le. destruct compare; easy'.
  Qed.

End Zext_as_OTF.

Module Zext <: UsualOrderedTypeFull'.
  Include Zext_as_OTF.
  Include OrderedTypeFullFacts.
  Include GenericMinMax Zext_as_OTF.
  Include UsualMinMaxLogicalProperties.
  Include UsualMinMaxDecProperties.
End Zext.

Bind Scope Zext_scope with Zext.
Bind Scope Zext_scope with Zext.t.

Infix "?=" := Zext.compare (at level 70, no associativity) : Zext_scope.
Infix "<=" := Zext.le : Zext_scope.
Infix "<" := Zext.lt : Zext_scope.
Infix "<=?" := Zext.leb (at level 70, no associativity) : Zext_scope.
Infix "<?" := Zext.ltb (at level 70, no associativity) : Zext_scope.
Infix "=?" := Zext.eqb (at level 70, no associativity) : Zext_scope.

Local Open Scope Z_scope.
Ltac z_compare_to_ops :=
  repeat match goal with
  | H: context[ Z.compare ?a ?b = Gt ] |- _ =>
    setoid_rewrite Z.compare_gt_iff in H
  | H: context[ Z.compare ?a ?b = Lt ] |- _ =>
    setoid_rewrite Z.compare_lt_iff in H
  | H: context[ Z.compare ?a ?b = eq ] |- _ =>
    setoid_rewrite Z.compare_eq_iff in H
  | |- context[ Z.compare ?a ?b = Gt ] =>
    setoid_rewrite Z.compare_gt_iff
  | |- context[ Z.compare ?a ?b = Lt ] =>
    setoid_rewrite Z.compare_lt_iff
  | |- context[ Z.compare ?a ?b = eq ] =>
    setoid_rewrite Z.compare_eq_iff
  end.

Lemma z_helper_not_lt_as_le :
  forall x y, ~ (x < y) <-> y <= x.
Proof. lia. Qed. 

Ltac normalize_not_z :=
  repeat match goal with
  | H: context[ ~ (?x < ?y) ] |- _ =>
    rewrite z_helper_not_lt_as_le in H
  | |- context[ ~ (?x < ?y) ] =>
    rewrite z_helper_not_lt_as_le
  end.

Local Open Scope Zext_scope.

Lemma zext_compare_as_z :
  forall x y, Zext.compare (zz x) (zz y) = Z.compare x y.
Proof.
  intros x y. simpl. reflexivity.
Qed.

Ltac zext_easy :=
  unfold Zext.le, Zext.lt in *; easy.

Ltac check_destruct_Zext t :=
  let T := type of t in
  constr_eq T Zext;
  lazymatch t with
  | zz _ => fail
  | neg_inf => fail
  | pos_inf => fail
  | _ => destruct t; try zext_easy
  end.

Ltac destruct_Zext :=
  repeat match goal with
  | x : Zext |- _  => destruct x
  | H : context[?t] |- _ =>
    check_destruct_Zext t
  | |- context[?t] =>
    check_destruct_Zext t
  end.

Lemma zext_helper_le_not_gt_iff :
    forall z z', ~ (z < z') <-> z' <= z.
  Proof.
    intros z z'. destruct_Zext; try zext_easy.
    unfold Zext.le, Zext.lt; simpl.
    z_compare_to_ops. lia.
  Qed.

Ltac normalize_not_zext :=
  repeat match goal with
  | H: context[ ~ (?x < ?y) ] |- _ =>
    setoid_rewrite zext_helper_le_not_gt_iff in H
  | |- context[ ~ (?x < ?y) ] =>
    setoid_rewrite zext_helper_le_not_gt_iff
  end.

  Ltac compare_to_ops :=
  repeat match goal with
  | H: context[ Zext.compare ?a ?b = Gt ] |- _ =>
    let Hf := fresh "H" in
    specialize Zext.compare_gt_iff as Hf;
    fold Zext.compare in Hf; fold Zext.lt in Hf;
    rewrite Hf in H; clear Hf
  | H: context[ Zext.compare ?a ?b = Lt ] |- _ =>
    let Hf := fresh "H" in
    specialize Zext.compare_lt_iff as Hf;
    fold Zext.compare in Hf; fold Zext.lt in Hf;
    rewrite Hf in H; clear Hf 
  | |- context[ Zext.compare ?a ?b = Gt ] =>
    let Hf := fresh "H" in
    specialize Zext.compare_gt_iff as Hf;
    fold Zext.compare in Hf; fold Zext.lt in Hf;
    rewrite Hf; clear Hf
  | |- context[ Zext.compare ?a ?b = Lt ] =>
    let Hf := fresh "H" in
    specialize Zext.compare_lt_iff as Hf;
    fold Zext.compare in Hf; fold Zext.lt in Hf;
    rewrite Hf; clear Hf 
  end.

Ltac zext_as_z :=
  repeat match goal with
  | H: context[Zext.le (zz ?a) (zz ?b)] |- _ =>
    unfold Zext.le in H;
    setoid_rewrite zext_compare_as_z in H;
    z_compare_to_ops
  | H: context[Zext.lt (zz ?a) (zz ?b)] |- _ =>
    unfold Zext.lt in H;
    setoid_rewrite zext_compare_as_z in H;
    z_compare_to_ops
  | |- context[Zext.le (zz ?a) (zz ?b)] =>
    unfold Zext.le;
    setoid_rewrite zext_compare_as_z;
    z_compare_to_ops
  | |- context[Zext.lt (zz ?a) (zz ?b)] =>
    unfold Zext.lt;
    setoid_rewrite zext_compare_as_z;
    z_compare_to_ops
  end; normalize_not_z; compare_to_ops; normalize_not_zext.

Ltac decompose_min x y :=
  let Hc := fresh "Hc" in
  let Hmin := fresh "Hmin" in
  destruct (Zext.min_spec x y) as [[Hc Hmin] | [Hc Hmin]];
  fold Zext.min in Hmin;
  try setoid_rewrite Hmin; try rewrite Hmin in *;
  clear Hmin.

Ltac decompose_max x y :=
  let Hc := fresh "Hc" in
  let Hmin := fresh "Hmax" in
  destruct (Zext.max_spec x y) as [[Hc Hmax] | [Hc Hmax]];
  fold Zext.max in Hmax;
  try setoid_rewrite Hmax; try rewrite Hmax in *;
  clear Hmax.

   
Ltac destruct_minmax :=
  match goal with
  | |- context[Zext.min ?a ?b] =>
    let x := a in
    let y := b in
    decompose_min x y
  | H : context[ Zext.min ?a ?b ] |- _ => 
    let x := a in
    let y := b in
    decompose_min x y
  | |- context[Zext.max ?a ?b] =>
    let x := a in
    let y := b in
    decompose_max x y
  | H : context[ Zext.max ?a ?b ] |- _ => 
    let x := a in
    let y := b in
    decompose_max x y
  end.