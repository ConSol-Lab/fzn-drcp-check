Require Import Coq.Logic.FinFun.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import String.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Arith.PeanoNat.
Require Import Bool.

Require Import Lia.
Require Checker.Atomic.
Require Import Checker.Variable.
Require Import Checker.DomainAll.
Require Coq.Structures.OrdersEx.
Require Checker.Utility.
Import Utility.ListEx.
Require MMaps.Interface.
Require MMaps.RBT.

Module smap := RBT.Make OrdersEx.String_as_OT.

Definition AtomicsMap := smap.t (list Atomic).

Definition VarAtomic := Atomic.Atomic.

Definition zn_interval := (Z * N)%type.

Definition var_cmp_to_cmp (var_cmp : Atomic.AtomicComparator) : AtomicComparator :=
  match var_cmp with
  | Atomic.less_equal => less_equal
  | Atomic.greater_equal => greater_equal
  | Atomic.equal => equal
  | Atomic.not_equal => not_equal
  end.

Definition var_atm_to_atm (atm : VarAtomic) : Atomic :=
  {| atm_cmp := (var_cmp_to_cmp (Atomic.comparator atm)); atm_val := (Atomic.value atm) |}.

Definition find_previous (name : string) (m : AtomicsMap) :=
  match smap.find name m with
  | Some l => l 
  | None => nil
  end.

Definition find_convert (name : string) (a : VarAtomic) (m : AtomicsMap) :=
  let converted := var_atm_to_atm a in
    converted :: (find_previous name m).

Fixpoint var_atomics_to_atomics (atomics : list VarAtomic) (m : AtomicsMap) :=
  match atomics with
  | nil => m
  | a :: atomics' =>
    let name := (var_name (Atomic.var a)) in
      var_atomics_to_atomics atomics' (smap.add name (find_convert name a m) m)
  end.

Definition var_atomic_equiv (v_a : Atomic.Atomic) (a : Atomic) :=
  var_cmp_to_cmp (Atomic.comparator v_a) = a.(atm_cmp)
    /\
  (Atomic.value v_a) = a.(atm_val).

Lemma In_to_InA_Duo_eq :
  forall {A B} (x : A) (y : B) (l : list (A * B)),
    In (x, y) l -> SetoidList.InA (Interface.Duo eq eq) (x, y) l.
Proof.
  intros A B x y l Hin.
  apply SetoidList.In_InA.
  - unfold Interface.Duo. constructor.
    + intros [a b]; split; reflexivity.
    + intros [a b] [a' b']. intros H.
      inversion H; simpl in *; subst; easy.
    + intros [a b] [a' b'] [a'' b''].
      intros H H'; inversion H; inversion H';
      simpl in *; subst; easy.
  - exact Hin.
Qed.

Definition previous_or_add (x : string) (v : VarAtomic) (m : AtomicsMap) :=
  let add := 
    if (x =? (var_name (Atomic.var v)))%string
      then var_atm_to_atm v :: nil
      else nil
    in
  add ++ find_previous x m.

Lemma var_atomics_correct :
  forall var_atomics initial initial_atoms,
    forall x atomics,
      In (x, atomics) (smap.bindings (var_atomics_to_atomics var_atomics initial))
        ->
      smap.MapsTo x initial_atoms initial
        ->
      forall a,
        In a atomics
          ->
        In a initial_atoms
          \/
        exists v_a,
          In v_a var_atomics
            /\
          var_atomic_equiv v_a a
            /\
          var_name (Atomic.var v_a) = x.
Proof.
  induction var_atomics as [| v var_atomics IH].
  - intros init initial_atomics x atomics. simpl.
    intros Hin. apply In_to_InA_Duo_eq in Hin.
    rewrite smap.bindings_spec1 in Hin.
    intros Hmap.
    intros a Hinatom.
    left.
    rewrite <- smap.find_spec in *. 
    rewrite Hmap in Hin; inversion Hin; subst initial_atomics.
    exact Hinatom.
  - intros initial initial_atoms x atomics Hin Hinit.
    intros a Hinatom.
    simpl in Hin.
    apply IH with (a := a) (initial_atoms := previous_or_add x v initial) in Hin.
    + destruct Hin as [Hprevadd | Hv].
      * unfold previous_or_add in Hprevadd.
        destruct (x =? (var_name (Atomic.var v)))%string eqn:Hvx.
        {
          simpl in Hprevadd.
          destruct Hprevadd.
          - clear -H Hvx.
            right. exists v.
            split; [|split] .
            + left. reflexivity.
            + unfold var_atomic_equiv.
              unfold var_atm_to_atm in H.
              inversion H. simpl.
              split; reflexivity.
            + rewrite String.eqb_eq in Hvx.
              symmetry. exact Hvx.
          - unfold find_previous in H.
            rewrite <- smap.find_spec in Hinit.
            rewrite Hinit in H.
            left. exact H.  
        }
        {
          unfold find_previous in Hprevadd.
          rewrite <- smap.find_spec in Hinit.
          rewrite Hinit in Hprevadd.
          left. apply Hprevadd. 
        }
      * clear -Hv.
        right.
        destruct Hv as (v' & Hin & Hequiv & Hname).
        exists v'.
        split; [|split].
        -- right. exact Hin.
        -- exact Hequiv.
        -- exact Hname.
    + clear -Hinit.
      rewrite <- smap.find_spec.
      unfold previous_or_add.
      destruct (x =? (var_name (Atomic.var v)))%string eqn:Hvx.
      * rewrite String.eqb_eq in Hvx. rewrite <- Hvx.
        rewrite smap.add_spec1.
        f_equal.
      * rewrite String.eqb_neq in Hvx.
        rewrite smap.add_spec2.
        2: easy.
        unfold find_previous.
        rewrite <- smap.find_spec in Hinit.
        destruct (smap.find x initial) eqn:Hfind.
        -- reflexivity.
        -- discriminate Hinit.
    + exact Hinatom.  
Qed.

Fixpoint map_valid {A B} (f : A -> option B) (l : list A) (acc : list B) : list B :=
  match l with
  | nil => acc
  | a :: l' =>
    match f a with
    | Some b => map_valid f l' (b :: acc)
    | None => nil
    end
  end.  

Record Domain := mkDom {
  d_name : string;
  d_lb : option Z;
  d_ub : option Z;
  holes : sint.t
}.

Definition domain_holds (dom : Domain) (sol : Assignment) :=
  forall v,
    var_name v = dom.(d_name)
      ->
    current_bound_holds (sol.(find_value) v) (dom.(d_lb)) (dom.(d_ub)) /\ is_not_holes  (sol.(find_value) v) dom.(holes).

Definition to_domain_f (elt : string * list Atomic) :=
  match elt with
  | (x, atomics) => match apply_atomics atomics None None sint.empty with
    | Some (lb, ub, holes) => Some (mkDom x lb ub holes)
    | None => None
    end
  end.

Definition atomics_to_domains (l : list (string * list Atomic)) :=
  map_valid to_domain_f l nil.
  
Definition var_atomics_to_domains (l : list VarAtomic) (init : AtomicsMap) :=
  let per_name := smap.bindings (var_atomics_to_atomics l init) in
  atomics_to_domains per_name.

Definition var_to_atoms (v : Var) :=
  match v with
  | interval v =>
    (mk_atm_ge v.(lower_bound)) ::
    (mk_atm_le v.(upper_bound)) ::
    nil
  end.

Definition add_atoms_from_var (m : AtomicsMap) (v : Var) : AtomicsMap :=
  let name := var_name v in
  let atoms := var_to_atoms v ++ find_previous name m in
  smap.add name atoms m. 

Definition vars_to_atoms (l : list Var) : AtomicsMap :=
  fold_left add_atoms_from_var l smap.empty.

Definition vars_with_atomics_to_domains (atomics : list Atomic.Atomic) (vs : list Var) :=
  var_atomics_to_domains atomics (vars_to_atoms vs).

Definition NoDup_f {A B} (l : list A) (f : A -> B) :=
  NoDup (map f l).

Ltac destruct_pairs :=
  repeat match goal with
  | [ x : _ * _ |- _ ] => destruct x
  end.

Ltac solve_equiv :=
  constructor;
  repeat (
    repeat intro;
    destruct_pairs;
    simpl in *;
    subst;
    try reflexivity;
    try symmetry; try assumption;
    try easy
  ).

Lemma domains_nodup :
  forall atomics vs,
  NoDup (map d_name (vars_with_atomics_to_domains atomics vs)).
Proof.
  intros atomics vs.
  unfold vars_with_atomics_to_domains.
  unfold var_atomics_to_domains.
  unfold atomics_to_domains.
  remember
    (var_atomics_to_atomics
    atomics (vars_to_atoms vs)) as atm_map.
  assert (NoDup (map fst (smap.bindings atm_map))).
  {
    (* This shouldn't be so hard... *)
    specialize (smap.bindings_spec2w (atm_map)) as Hbind.
    unfold smap.eq_key in Hbind.
    remember (smap.bindings atm_map) as l.
    clear -Hbind.
    assert (forall (x y : string * list Atomic), {x = y} + {x <> y}).
    { repeat decide equality. }
    induction l.
    - simpl. apply NoDup_nil.
    - simpl. inversion Hbind; clear Hbind.
      apply NoDup_cons.
      + destruct (in_dec H a l) as [Hin | ].
        * subst x; subst l0. apply SetoidList.In_InA with (eqA := (fun p p' => fst p = fst p')) in Hin.
          contradiction.
          solve_equiv.
        * subst x; subst l0.
          unfold not. intros Hfstin.
          rewrite in_map_iff in Hfstin.
          destruct Hfstin as [a' [Hfst Ha']].
          rewrite SetoidList.InA_alt in H2.
          assert (exists y, fst a = fst y /\ In y l).
          { exists a'. split; easy. }
          contradiction.
      + apply IHl.
        exact H3.
  }
  remember (smap.bindings atm_map) as bl.
  destruct (map_valid to_domain_f bl nil) as [| d l'] eqn:Hvalid.
  - simpl. apply NoDup_nil.
  - remember (d :: l') as l.
    assert (map_valid to_domain_f bl nil <> nil) as Hnnil.
    { unfold not. intros Hnil. subst l. rewrite Hnil in Hvalid. discriminate Hvalid. }
    specialize map_valid_all_some with (f := to_domain_f) (acc := nil) (l := bl) as Hsome.
    specialize (Hsome Hnnil).
    rewrite map_valid_as_map with (d := d) in Hvalid.
    + rewrite app_nil_r in Hvalid.
      rewrite <- map_rev in Hvalid.
      rewrite <- Hvalid.
      apply nodup_key with (a_k := fst).
      * rewrite map_rev. apply NoDup_rev.
        exact H.
      * intros [x dom].
        intros Hrev.
        simpl.
        rewrite <- in_rev in Hrev.
        rename Hrev into Hin.
        unfold option_map_default.
        destruct (to_domain_f (x, dom)) as [dom' |] eqn:Hto_dom.
        2: { apply Hsome in Hin. rewrite Hto_dom in Hin. contradiction. }
        clear -Hto_dom.
        unfold to_domain_f in Hto_dom.
        destruct (apply_atomics dom None None
          sint.empty) as [((lb & ub) & holes) |]; try discriminate Hto_dom.
        inversion Hto_dom as [Hdom']; clear Hto_dom.
        simpl. reflexivity.
    + exact Hnnil.
Qed.
