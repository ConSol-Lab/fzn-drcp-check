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
Require Import Checker.Domain.
Require Coq.Structures.OrdersEx.
Require Checker.Utility.
Import Utility.ListEx.
Import Utility.Maps.
Require MMaps.Interface.
Require MMaps.RBT.

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

Definition to_atomics_new_map (a : VarAtomic) (m : AtomicsMap) :=
  let name := (var_name (Atomic.var a)) in
  match smap.find name m with
  | Some l => 
    let to_add := var_atm_to_atm a :: l in
    smap.add name to_add m
  | None => m
  end.

Fixpoint var_atomics_to_atomics (atomics : list VarAtomic) (m : AtomicsMap) :=
  match atomics with
  | nil => m
  | a :: atomics' =>
      var_atomics_to_atomics atomics' (to_atomics_new_map a m)
  end.

Definition var_atomic_equiv (v_a : Atomic.Atomic) (a : Atomic) :=
  var_cmp_to_cmp (Atomic.comparator v_a) = a.(atm_cmp)
    /\
  (Atomic.value v_a) = a.(atm_val).

Ltac destruct_pairs :=
  repeat match goal with
  | [ x : _ * _ |- _ ] => destruct x
  end.

Ltac destruct_ands :=
  repeat match goal with
  | [ H: _ /\ _ |- _ ] =>
      let H1 := fresh H "1" in
      let H2 := fresh H "2" in
      destruct H as [H1 H2]
  end.

Ltac solve_equiv :=
  constructor;
  repeat (
    repeat intro;
    destruct_pairs;
    simpl in *;
    destruct_ands;
    subst;
    try reflexivity;
    try symmetry; try assumption;
    try easy
  ).

Lemma In_to_InA_Duo_eq :
  forall {A B} (x : A) (y : B) (l : list (A * B)),
    In (x, y) l -> SetoidList.InA (Interface.Duo eq eq) (x, y) l.
Proof.
  intros A B x y l Hin.
  apply SetoidList.In_InA.
  - unfold Interface.Duo.
    solve_equiv. 
  - exact Hin.
Qed.

Lemma var_atomics_only_initial :
  forall var_atomics initial,
    forall x atomics,
      In (x, atomics) (smap.bindings (var_atomics_to_atomics var_atomics initial))
        ->
      (* Would be nice if we could use smap.In, but that one unfolds a bit strangely making it harder to work with *)
      exists initial_atoms, smap.MapsTo x initial_atoms initial.
Proof.
  induction var_atomics as [| v var_atomics IH].
  - intros initial x atomics.
    intros Hin. 
    apply In_to_InA_Duo_eq in Hin.
    rewrite smap.bindings_spec1 in Hin.
    simpl in Hin.
    exists atomics.
    exact Hin.
  - intros initial x atomics.
    simpl. intros Hin.
    unfold to_atomics_new_map in Hin.
    remember (var_name (Atomic.var v)) as name.
    destruct (smap.find name initial) as [atomics' |] eqn:Hfind.
    + rewrite smap.find_spec in Hfind.
      destruct (String.string_dec name x) as [Hxname|Hxname].
      * subst x.
        exists atomics'.
        apply Hfind.
      * apply IH in Hin.
        destruct Hin as [x_atoms Hx].
        rewrite <- smap.find_spec in Hx.
        rewrite smap.add_spec2 in Hx.
        -- rewrite smap.find_spec in Hx.
          exists x_atoms.
          exact Hx.
        -- exact Hxname.
    + apply IH in Hin. exact Hin.
Qed.

Definition find_default (x : string) (m : AtomicsMap) :=
  match smap.find x m with
  | Some atoms => atoms
  | None => nil
  end.

Lemma var_atomics_correct :
  forall var_atomics initial,
    forall x atomics,
      In (x, atomics) (smap.bindings (var_atomics_to_atomics var_atomics initial))
        ->
      forall a,
        In a atomics
          ->
        In a (find_default x initial)
          \/
        exists v_a,
          In v_a var_atomics
            /\
          var_atomic_equiv v_a a
            /\
          var_name (Atomic.var v_a) = x.
Proof.
  induction var_atomics as [| v var_atomics IH].
  - intros init x atomics. simpl.
    intros Hin. apply In_to_InA_Duo_eq in Hin.
    rewrite smap.bindings_spec1 in Hin.
    intros a Hinatom.
    left.
    rewrite <- smap.find_spec in *.
    unfold find_default. rewrite Hin.
    exact Hinatom.
  - intros initial x atomics Hin.
    intros a Hinatom.
    simpl in Hin.
    pose proof Hin as Hinit.
    apply var_atomics_only_initial in Hinit.
    destruct Hinit as (x_init & Hinit).
    apply IH with (a := a) in Hin.
    + destruct Hin as [Hprevadd | Hv].
      * unfold find_default in Hprevadd.
        destruct (x =? (var_name (Atomic.var v)))%string eqn:Hvx.
        {
          clear -Hvx Hprevadd Hinit. 
          rewrite String.eqb_eq in Hvx.
          unfold to_atomics_new_map in Hprevadd, Hinit.
          rewrite <- Hvx in *.
          unfold find_default.
          destruct (smap.find x initial) eqn:Hfind_init.
          2: { rewrite Hfind_init in Hprevadd. destruct Hprevadd. }
          rewrite smap.add_spec1 in Hprevadd.
          simpl in Hprevadd.
          destruct Hprevadd.
          - right. exists v.
            split; [|split] .
            + left. reflexivity.
            + unfold var_atomic_equiv.
              unfold var_atm_to_atm in H.
              inversion H. simpl.
              split; reflexivity.
            + symmetry. exact Hvx.
          - left. exact H.  
        }
        {
          clear -Hvx Hprevadd Hinit.
          unfold to_atomics_new_map in Hprevadd, Hinit.
          remember (var_name (Atomic.var v)) as v_name.
          rewrite String.eqb_neq in Hvx.
          unfold find_default.
          destruct (smap.find v_name initial).
          - rewrite <- smap.find_spec in Hinit.
            rewrite smap.add_spec2 in Hprevadd, Hinit;
            try (symmetry; assumption).
            rewrite Hinit in *.
            left. exact Hprevadd.
          - rewrite <- smap.find_spec in Hinit. rewrite Hinit in *.
            left. exact Hprevadd.
        }
      * clear -Hv.
        right.
        destruct Hv as (v' & Hin & Hequiv & Hname).
        exists v'.
        split; [|split].
        -- right. exact Hin.
        -- exact Hequiv.
        -- exact Hname.
    + exact Hinatom.
Qed.

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
    current_bound_holds (sol.(find_value) v) (dom.(d_lb)) (dom.(d_ub)) /\ is_not_holes (sol.(find_value) v) dom.(holes).

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

Definition vars_to_atoms (vs : list Var) : AtomicsMap :=
  build_map var_name var_to_atoms vs.

Definition vars_with_atomics_to_domains (atomics : list Atomic.Atomic) (vs : list Var) :=
  var_atomics_to_domains atomics (vars_to_atoms vs).

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

Definition default_dom :=
  mkDom ""%string None None sint.empty.

Definition atoms_hold_for_var (atoms : list Atomic) (sol : Assignment) (v : Var) :=
  forall a,
    In a atoms ->
    atomic_holds (sol.(find_value) v) a.

Lemma vars_to_atoms_correct :
forall vs sol x atoms_from_var, smap.MapsTo x atoms_from_var (vars_to_atoms vs) ->
    exists v, In v vs /\ var_name v = x /\ atoms_hold_for_var atoms_from_var sol v.
Proof.
  intros vs sol x atoms_from_var.
  intros Hmap.
  apply build_map_maps_to in Hmap.
  destruct Hmap as (v & Hin & Hname & Hto_atoms).
  exists v.
  split; [|split].
  - exact Hin.
  - exact Hname.
  - unfold atoms_hold_for_var.
    unfold var_to_atoms in Hto_atoms.
    destruct v.
    rewrite <- Hto_atoms.
    intros a Hain.
    unfold atomic_holds.
    specialize sol.(consistency_proof) with (v := interval var) as Hsol.
    unfold is_in in Hsol.
    apply Is_true_eq_true in Hsol.
    destruct Hain as [Hlb | [Hub | Hnil]].
    + unfold mk_atm_ge in Hlb. rewrite <- Hlb. simpl.
      lia.
    + unfold mk_atm_le in Hub. rewrite <- Hub. simpl.
      lia.
    + destruct Hnil.
Qed.

Lemma to_domains_sound :
  forall sol dom var_atomics vs,
  (forall a, In a var_atomics ->
    Atomic.test_atomic_assignment a sol = true)
    ->
  In dom
    (vars_with_atomics_to_domains
      var_atomics
      vs)
    ->
  exists (v : Var),
    In v vs 
     /\
    var_name v = (dom.(d_name))
     /\
    domain_holds dom sol.
Proof.
  intros sol dom var_atomics vs.
  intros Hvar_atoms_hold.
  intros Hin.
  unfold vars_with_atomics_to_domains in Hin.
  unfold var_atomics_to_domains in Hin.
  unfold atomics_to_domains in Hin.
  remember (smap.bindings
    (var_atomics_to_atomics
    var_atomics
    (vars_to_atoms vs))) as bindings.
  assert (map_valid to_domain_f bindings nil <> nil).
  { intros Hnil. rewrite Hnil in Hin. destruct Hin. }
  rewrite map_valid_as_map with (d := default_dom) in Hin.
  - rewrite app_nil_r in Hin. rewrite <- in_rev in Hin.
    rewrite in_map_iff in Hin.
    destruct Hin as ((x & atoms) & Hto_dom & Hin).
    subst bindings.
    apply map_valid_all_some with (a := (x, atoms)) in H; try assumption.
    unfold option_map_default in Hto_dom.
    destruct (to_domain_f (x, atoms)) eqn:Hdom; try contradiction; clear H; subst d.
    unfold to_domain_f in Hdom.
    destruct (apply_atomics atoms None None sint.empty) as [[[lb ub] holes]|] eqn:Happly; try discriminate Hdom.
    rename Hdom into Hdom_some; inversion Hdom_some as [Hdom]; clear Hdom_some.
    specialize (var_atomics_correct var_atomics (vars_to_atoms vs) x atoms Hin) as Hvar_atomics.
    apply var_atomics_only_initial in Hin.
    destruct Hin as (var_atoms & Hvar_atoms).
    assert (var_atoms = find_default x (vars_to_atoms vs)) as Hvar_atoms_find.
    { unfold find_default. rewrite <- smap.find_spec in Hvar_atoms. rewrite Hvar_atoms. reflexivity. }
    rewrite <- Hvar_atoms_find in Hvar_atomics; clear Hvar_atoms_find.
    apply vars_to_atoms_correct with (sol := sol) in Hvar_atoms.
    destruct Hvar_atoms as (v & Hinvs & Hname & Hvar_atoms).
    exists v.
    split; [|split].
    + exact Hinvs.
    + simpl. exact Hname.
    + unfold domain_holds.
      intros v'. simpl.
      intros Hvname'.
      assert (sol.(find_value) v' = sol.(find_value) v) as Hvv'.
      { apply sol.(find_value_eq_name). rewrite Hvname'. rewrite Hname. reflexivity. }
      rewrite Hvv'.
      apply apply_atomics_some with (atoms := atoms).
      * exact Happly.
      * subst x. clear -Hvar_atoms_hold Hvar_atomics Hvar_atoms.
        intros a Hin.
        apply Hvar_atomics in Hin; clear Hvar_atomics.
        destruct Hin as [Hin_var_atoms | Hex_atom].
        { unfold atoms_hold_for_var in Hvar_atoms. apply Hvar_atoms. exact Hin_var_atoms. }
        destruct Hex_atom as (v_a & Hin & Hequiv & Hname).
        apply Hvar_atoms_hold in Hin; clear Hvar_atoms_hold.
        unfold Atomic.test_atomic_assignment in Hin.
        unfold var_atomic_equiv in Hequiv.
        destruct Hequiv as (Hcmp & Hval).
        assert (find_value sol (Atomic.var v_a) = find_value sol v).
        { apply sol.(find_value_eq_name). exact Hname. }
        unfold var_cmp_to_cmp in Hcmp.
        unfold atomic_holds.
        unfold Atomic.test_atomic in Hin.
        destruct (Atomic.comparator v_a); rewrite <- Hcmp; lia.
  - intros Hnil. rewrite Hnil in Hin. destruct Hin.
Qed.

Definition Consequent := (string * Atomic)%type.
Definition Premises := list (string * Atomic).

Definition Inference := (Premises * Consequent)%type.
Definition Nogood := list (string * Atomic)%type.

Inductive Step :=
| step_inference (premises : list (string * Atomic)) (consequent : string * Atomic)
.

Definition check_premise (domains : smap.t Domain) (premise : string * Atomic) := 
  match premise with
  | (x, a) =>
    match smap.find x domains with
    | Some dom =>
      check_holds a dom.(d_lb) dom.(d_ub) dom.(holes)
    | None => false
    end
  end.

Definition apply_consequent (domains : smap.t Domain) (consequent : string * Atomic) : option (smap.t Domain) :=
  match consequent with
  | (x, a) =>
    let (bounds, holes) := 
      match smap.find x domains with
      | Some dom => (dom.(d_lb), dom.(d_ub), dom.(holes))
      | None => (None, None, sint.empty)
      end in
    let (lb, ub) := bounds in
    match apply_atomics (a :: nil) lb ub holes with
    | None => None
    | Some (lb, ub, holes) => 
      let new_dom := mkDom x lb ub holes in
      Some (smap.add x new_dom domains)
    end
  end.

Inductive StepCheck :=
| step_domains (domains : smap.t Domain)
| nogood_valid
| step_reject.

Definition check_inference (premises : list (string * Atomic)) (consequent : string * Atomic) (domains : smap.t Domain) :=
  if forallb (check_premise domains) premises
    then 
      match apply_consequent domains consequent with
      | None => nogood_valid
      | Some domains => step_domains domains
      end
    else step_reject.

Fixpoint check_combine (steps : list Step) (domains : smap.t Domain) : bool :=
  match steps with
  | nil => false
  | step_inference premises consequent :: steps' => 
    match check_inference premises consequent domains with
    | step_domains new_domains => check_combine steps' new_domains
    | nogood_valid => true
    | step_reject => false
    end
  end.