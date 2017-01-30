From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp
Require Import choice fintype finset tuple ssralg zmodp matrix bigop mxalgebra.
From CoqEAL
Require Import hrel param refinements.

Require Import bitseq bitword notation bits bitocaml bitset.

Import Refinements.Op.
Import Logical.Op.
Import Sets.Op.

(* Board size *)
Definition n := 8. (* XXX: generalize to any [n > 0] *)

Definition T := [finType of 'I_n].

Module Fintype : FINTYPE with Definition T := T.
  Definition T: finType := T.
End Fintype.


(*****************************************************************)
(** * n-queens positions                                         *)
(*****************************************************************)

(** We offer a generic, iterator-like interface for board positions,
    together with an accessibility predicate for recursion over
    positions. *)

Module Type POS.

Parameter Pos: Type.

Parameter init: Pos.
Parameter is_full: Pos -> bool.
Parameter has_valid: Pos -> bool.
Parameter next_valid_with_curr: Pos -> Pos.
Parameter next_valid_without_curr: Pos -> Pos.

Parameter Pos_order: Pos -> Pos -> Prop.

Axiom Pos_wf: well_founded Pos_order.
Axiom next_valid_with_curr_wf: forall p, Pos_order (next_valid_with_curr p) p.
Axiom next_valid_without_curr_wf: forall p, Pos_order (next_valid_without_curr p) p.

End POS.

(*********************************************************)
(** ** Board specification                               *)
(*********************************************************)

(** This is the proof-oriented and computationally inert specification
of the board position. *)

Module Spec <: POS.

Local Open Scope ring_scope.

Definition board := 'M[bool]_n.

Definition is_valid_col (b: board)(i j: 'I_n): bool :=
  [forall (x : 'I_n | x < i), ~~ b x j].

Definition is_valid_row (b: board)(i j: 'I_n): bool :=
  [forall (y : 'I_n | y != j), ~~ b i y].

Definition is_valid_asc_diag (b: board)(i j: 'I_n): bool := 
  [forall (x : 'I_n | x < i),
      forall (y : 'I_n | (max i j - min i j == max x y - min x y)%N),
        ~~ b x y ].

Definition is_valid_desc_diag (b: board)(i j: 'I_n): bool := 
  [forall (x : 'I_n | x < i),
      forall (y : 'I_n | (i + j == x + y)%N),
        ~~ b x y].

Definition is_valid_pos (b: board)(i j: 'I_n): bool :=
  [&& is_valid_col b i j
   ,  is_valid_row b i j
   ,  is_valid_asc_diag b i j
   &  is_valid_desc_diag b i j ].

Definition is_full_below (b: board)(i: 'I_n): bool := 
  [forall (x : 'I_n | x < i),
      exists y, 
        b x y && is_valid_pos b x y ].

Definition is_empty_above (b: board)(i: 'I_n): bool :=
  [forall (x : 'I_n | x > i), forall j, ~~ b x j].


Record Pos' := Mk_pos' { p_board: board  ;
                         p_curr_row: 'I_n ;
                         p_curr_col: 'I_n ;
(*
                         (* Current position is valid: *)
                         _: is_valid_pos p_board p_curr_row p_curr_col ;
                         (* One valid queen on each row below [p_curr_row]: *)
                         _: is_full_below p_board p_curr_row ;
                         (* No queen on any row above [p_curr_row]: *)
                         _: is_empty_above p_board p_curr_row ;
*)
                       }.

Definition inv (p: Pos'): bool :=
  [&& is_valid_pos p.(p_board) p.(p_curr_row) p.(p_curr_col) 
   ,  is_full_below p.(p_board) p.(p_curr_row)
   &  is_empty_above p.(p_board) p.(p_curr_row) ].


Definition Pos := Pos'. 
(* XXX: Why couldn't I directly declare [Pos] as a [record]? *)

Definition cols (p: Pos): {set 'I_n} :=
  let b := p.(Spec.p_board) in
  let i := p.(Spec.p_curr_row) in
  [set j in 'I_n | is_valid_col b i j].

Lemma curr_col_cols: forall p, inv p ->
    (p.(p_curr_col) : nat) = (n - #| cols p |)%N.
Proof.
move=>[b i j] /=.
rewrite /cols.
Admitted.

Definition asc_diag (p: Spec.Pos): {set 'I_n} :=
  let b := p.(Spec.p_board) in
  let i := p.(Spec.p_curr_row) in
  [set j in 'I_n | Spec.is_valid_asc_diag b i j ].

Definition desc_diag (p: Spec.Pos): {set 'I_n} :=
  let b := p.(Spec.p_board) in
  let i := p.(Spec.p_curr_row) in
  [set j in 'I_n | Spec.is_valid_desc_diag b i j ].

Definition valid_cols (p: Pos): {set 'I_n} :=
  let b := p.(p_board) in
  let i := p.(p_curr_row) in
  let j := p.(p_curr_col) in
  [set y in 'I_n | (j <= y) && is_valid_pos b i y ].

Lemma curr_col_valid: forall p, inv p ->
    p.(p_curr_col) = [arg min_(j' < p.(p_curr_col) | j' \in valid_cols p ) j' ]%N.
Proof.
move=> [b i j] /and3P [Hval_ij Hfull Hemp]; simpl in *.
case arg_minP.
- rewrite inE.
  by apply/and3P; split.
- rewrite /valid_cols.
  move=> x H1 H2.
  rewrite inE in H1.
  move/and4P: H1=> /= [H11 H12 H13 H14].
  have H3: (x <= j)
    by apply H2; rewrite inE; apply/and3P; split.
  
  apply /eqP.
  etransitivity.
  apply eqn_leq.
    by apply/andP.
Qed.

(*
Lemma valid_cols_eq: forall p, inv p ->
    valid_cols p = cols p :&: ~: (asc_diag p :|: desc_diag p).
Admitted.
*)

Definition init: Pos := Mk_pos' (\matrix_(i, j) false) ord0 ord0.

Lemma inv_init: inv init.
Admitted.
(*
Next Obligation.
apply/forallP=> x.
by apply/implyP.
Qed.
Next Obligation.
apply/forallP=> i.
apply/implyP=> ?.
apply/forallP=> j.
by rewrite mxE.
Qed.
Next Obligation.
Admitted. (* by def.*)
*)


Definition is_full (p: Pos): bool := #| cols p | == 0%N.


Definition has_valid (p: Pos): bool := 
  (#| valid_cols p | != 0)%N.

Definition next_rowN (n i: nat): nat :=
  if i.+1 == n then i else i.+1.

Lemma next_row_proof n (i : 'I_n): next_rowN n i < n.
Proof.
rewrite /next_rowN.
case: ifP=> [/eqP -> | /eqP H ] //.
case: ltngtP=> // [le_Si_n | eq_Si_n].
- have le_i_n: (i.+1.-1 < n) 
    by rewrite -pred_Sn; apply ltn_ord.
  rewrite ltnNge in le_i_n.
  by case/negP: le_i_n.
- by rewrite -eq_Si_n in H.
Qed.

Definition next_row {n} (i : 'I_n) := Ordinal (next_row_proof n i).

(*
Lemma le_incO {n}: forall (i: 'I_n) k,
    i < incO k -> i < k \/ i = k.
Proof.
move=> i k. 
Admitted.

Lemma incO_le {n}: forall (i k: 'I_n),
    incO k < i -> k < i.
Admitted.

Lemma incO_in {n}: forall(k: 'I_n.+1),
    k <> ord_max -> incO k <> k.
Admitted.
*)

Definition next_valid_with_curr (p: Pos): Pos :=
  let b := p.(p_board) in
  let i := p.(p_curr_row) in
  let j := p.(p_curr_col) in
  let b := \matrix_(x , y) 
            if (x == i) && (y == j) then true
            else  b x y in
  let 'row := next_row i in
  match [pick col in 'I_n | is_valid_pos b row col ] with
  | Some col => 
    let 'col := [arg min_(j' < col | is_valid_pos b row j' ) j' ]%N in
    Mk_pos' b row col
  | None => p
  end.


Lemma inv_next_valid_with_curr: forall p, inv p -> inv (next_valid_with_curr p).

(*
Next Obligation.
(*
apply/forallP=> i.
apply/implyP=> Hi.
have {Hi} [Hle | Heq]: (i < p.(p_curr_row) \/ i = p.(p_curr_row))
  by apply: le_incO.

- have H: (\sum_(j < n)
            (row i
              (\matrix_(i0, j0) p.(p_board) i0 j0)) ord0 j == 1)%N.
  {
    destruct p as [ ? ? ? ? He ?]. simpl in *.
    move: He=> /forallP /(_ i).
    move/implyP=> /(_ Hle).
    move=> H.
    erewrite eq_bigr.
    apply: H=> //. move=> i' _.
    by rewrite !mxE.
  }

  erewrite eq_bigr; first by apply H.
  move=> i' _ /=.
  rewrite !mxE.
  case: ifP=> // /andP [/eqP H1 H2].
  by rewrite H1 ltnn in Hle.
- rewrite Heq. 
  have H1: (\sum_(j < n)
            (\row_j0 
              (if (j0 == p_curr_col p) then true
               else false)) ord0 j == 1)%N.
  {
    admit. (* by def. *)
  }
  have H2: (\sum_(j < n)
            (\row_j0 
              (if (j0 == p_curr_col p) then true
               else p.(p_board) (p_curr_row p) j0)) ord0 j == 1)%N.
  {
    erewrite eq_bigr; first by apply H1.
    move=> j _ /=.
    rewrite !mxE.
    case: ifP=> // _.
    destruct p as [? ? ? ? ? ? Hcurr_row]. simpl in *.
    rewrite - Heq_anonymous0 in Hcurr_row.
    admit. (* by the sum on row [p_curr_row0] being [0] *)
  }
  erewrite eq_bigr; first by apply H2.
  move=> j _ //=.
  rewrite !mxE eq_refl /=.
  by case: ifP.
*)
Admitted.
Next Obligation.
(*
apply/forallP=> i.
apply/implyP=> Hi.
apply/forallP=> j.
rewrite mxE.
have -> /=:((i == p_curr_row p) = false).
{
  apply incO_le in Hi.
  rewrite ltn_neqAle in Hi.
  move/andP: Hi=> [/eqP Hi _].
  apply/eqP=> Heq.
  apply Hi.
  by rewrite Heq.
}
destruct p as [b curr_i curr_j finished Hin Hex Hlast].
simpl in *.
move/forallP: Hex => /(_ i).
have Hcurr_i: curr_i < i.
{
  rewrite /inc_bounded in Hi.
  destruct (curr_i.+1 == n) eqn:Hc=> //.
  by apply ltnW.
}
move/implyP=> /(_ Hcurr_i).
by move/forallP=> /(_ j).
Qed.*)
Admitted.
Next Obligation.
(*
case (eqP (x := p.(p_curr_row))(y := ord_max))=> [Heq | Hneq].
- (* p_curr_row p = ord_max *)
  rewrite Heq.
  have -> : (incO ord_max = ord_max) by admit. (* def. *)
  have H0: forall j, ~~ p.(p_board) ord_max j.
  {
    destruct p as [b curr_i curr_j finished Hin Hex Hlast]; simpl in *.
    rewrite -Heq_anonymous0 Heq in Hlast.
    admit. (* by [Hlast] sums to [0] *)
  }
  
  have H1: (\sum_(j < n)
              (\row_j0 
                (if (j0 == p_curr_col p) then true
                 else false)) ord0 j == 1)%N.
  { 
    admit. (* by rearranging the sum *)
  }

  have H2: (\sum_(j < n)
              (\row_j0 
                (if (j0 == p_curr_col p) then true
                 else p.(p_board) ord_max j0)) ord0 j == 1)%N.
  {
    erewrite eq_bigr; first by apply H1.
    move=> j ? /=.
    rewrite !mxE.
    case eqP=> // ?.
    by move: H0=> /(_ j) /negPf ->.
  }

  erewrite eq_bigr; first by apply H2.
  move=> j ? /=.
  by rewrite !mxE eq_refl.

- (* p_curr_row p <> ord_max *)
  have Hinc: incO (p_curr_row p) != p_curr_row p
    by apply/eqP; apply incO_in.

  have H0: forall j, ~~ p.(p_board) (incO (p_curr_row p)) j.
  {
    move=> j.
    destruct p as [b curr_i curr_j finished Hin Hex Hlast]; simpl in *.
    move/forallP: Hex=> /(_ (incO curr_i)).
    have Hcurr_i: (curr_i < incO curr_i).
    {
      admit. (* by def. of [incO] on [curr_i < ord_max] *)
    }
    move/implyP=> /(_ Hcurr_i).
    by move/forallP=> /(_ j).
  }

  have H1: (\sum_(j < n)
             (\row_j0 p.(p_board) (incO (p_curr_row p)) j0) ord0 j)%N == false.
  { 
    admit. (* by H0 *) 
  }

  erewrite eq_bigr; first by apply H1.
  move=> i ? /=.
  rewrite !mxE.
  apply (congr1 nat_of_bool).
  erewrite Bool.andb_if.
  by etransitivity; first by apply ifN_eq.
*)
Admitted.
*)
Admitted.

Lemma next_with_cols: forall p, inv p ->
    cols (next_valid_with_curr p) = cols p :\ p.(p_curr_col).
Admitted.
   
Lemma next_with_asc_diag: forall p p', inv p ->
    p.(p_curr_row) < n ->
    p' = next_valid_with_curr p ->
    asc_diag p' = shrS (p'.(p_curr_col) |: asc_diag p) (inord 1).
Admitted.

Lemma next_with_desc_diag: forall p p',
    p.(p_curr_row) < n ->
    p' = next_valid_with_curr p ->
    desc_diag p' = shlS (p'.(p_curr_col) |: desc_diag p) (inord 1).
Admitted.

Lemma next_with_valid_cols: forall p,
    valid_cols (next_valid_with_curr p) = valid_cols p :\ p.(p_curr_col).
Admitted.

Definition next_valid_without_curr (p: Pos): Pos :=
  let b := p.(p_board) in
  let i := p.(p_curr_row) in
  let j := p.(p_curr_col) in
  match [pick col in 'I_n | (j < col) && is_valid_pos b i col ] with
  | Some col => 
    let 'col := [arg min_(j' < col | (j < j') && is_valid_pos b i j') j' ]%N in
    Mk_pos' b i col
  | None => p
  end.

Lemma inv_next_valid_without_curr: forall p, inv p -> inv (next_valid_without_curr p).
Admitted.

Lemma next_without_cols: forall p, inv p ->
    cols (next_valid_without_curr p) = cols p.
Proof.
move=> [b i j] /and3P[Hv Hf Hb] //=.
rewrite /next_valid_without_curr.
by case pickP=> [col /and3P [Hcol1 Hcol2 Hcol3]|Hempty].
Qed.

Lemma next_without_asc_diag: forall p, inv p ->
    asc_diag (next_valid_without_curr p) = asc_diag p.
move=> [b i j] /and3P[Hv Hf Hb] //=.
rewrite /next_valid_without_curr.
by case pickP=> [col /and3P [Hcol1 Hcol2 Hcol3]|Hempty].
Qed.

Lemma next_without_desc_diag: forall p, inv p ->
    desc_diag (next_valid_without_curr p) = desc_diag p.
move=> [b i j] /and3P[Hv Hf Hb] //=.
rewrite /next_valid_without_curr.
by case pickP=> [col /and3P [Hcol1 Hcol2 Hcol3]|Hempty].
Qed.

Lemma next_without_valid_cols: forall p, inv p ->
    valid_cols (next_valid_without_curr p) = valid_cols p :\ p.(p_curr_col).
Proof.
move=> [b i j] /and3P[Hv Hf Hb] //=.
rewrite /next_valid_without_curr.
case pickP=> [col /and3P [Hcol1 Hcol2 Hcol3]|Hempty].
- simpl in *.
  rewrite /valid_cols.
  apply setP.
  move=> y.
  rewrite !inE //=.
  apply/andP/and3P.
  + move=> [H1 H2].
    have Hjy: j < y by admit. (* by H1 *)
    split=> //.
    * by rewrite neq_ltn Hjy orbT.
    * by apply ltnW.
  + move=> [H1 H2 Hval].
    split=> //.
    case arg_minP.
    * by apply/andP; split.
    * move=> y' /andP [Hjy' Hval_y'] H.
      apply H. apply /andP; split=> //.
      rewrite ltn_neqAle; apply /andP; split=> //.
      apply/eqP=> H'.
      apply val_inj in H'.
      rewrite H' //= in H1 .      
      move/eqP: H1.
      by apply.
- have H0: valid_cols {| p_board := b; p_curr_row := i; p_curr_col := j |} = set0.
  admit.
Admitted.


Require Import Wellfounded.Lexicographic_Product.
Import Relation_Operators.

Definition Pos_order (p1 p2: Pos): Prop.
(* XXX: disgusting and useless definition *)
eapply lexprod with (A := 'I_n)(B := fun _ => ('I_n * board)%type).
exact (fun x y => lt (val x) (val y)).
move=> ?.
intros.
eapply lexprod with (A := 'I_n) (B := fun _ => board).
exact (fun x y => lt (val x) (val y)).
move=> ?.
exact (fun b1 b2 => [forall i, [forall j, b1 i j ==> b2 i j]]).
split; case:X => [? ?] //.
split; case:X0 => [? ?] //.
split; [|split]; case: p1=> [? ? ?]//.
split; [|split]; case: p2=> [? ? ?]//.
Defined.

Lemma Pos_wf: well_founded Pos_order.
Admitted. (* XXX: define *)
 Lemma next_valid_with_curr_wf: forall p, Pos_order (next_valid_with_curr p) p.
Admitted. (* XXX: prove *)
Lemma next_valid_without_curr_wf: forall p, Pos_order (next_valid_without_curr p) p.
Admitted. (* XXX: prove *)

(*
Lemma lt_wf: well_founded lt.
Proof.
have H : forall m n, (n < m)%coq_nat -> Acc lt n.
{
  move=> m; elim: m=> [|m IHm] n Hlt_n.
  - inversion Hlt_n.
  - constructor=> y Hlt_y.
    eapply IHm, PeanoNat.Nat.lt_le_trans; eauto using Lt.lt_n_Sm_le. 
}
by move=> n; constructor; apply H.
Qed.
*)

Local Close Scope ring_scope.

End Spec.

(*********************************************************)
(** ** Board implementation                              *)
(*********************************************************)

(** This is the computation-oriented implementation of the board
    position. It is parameterized over the concrete implementation of
    machine words: we shall do a refinement there too, once using the
    axiomatized (native) integers and once using the ssrbit model. *)

Section Machine.

Variable (int: Type).

Context `{eq_of int}.
Context `{inter_of int}.
Context `{compl_of int}.
Context `{union_of int}.
Context `{empty_of int}.
Context `{full_of int}.
Context `{keep_min_of int}.
Context `{cardinal_of nat int}.
Context `{succ_of int}.
Context `{pred_of int}.

Record Pos := Mk_pos { p_cols: int ; 
                       p_asc_diag: int;
                       p_desc_diag: int;
                       p_valid: int }.

Definition Pos_order (p1 p2: Pos): Prop :=
    (cardinal_op p1.(p_cols) < cardinal_op p2.(p_cols))
  \/ (  cardinal_op p1.(p_cols) = cardinal_op p2.(p_cols)
     /\ cardinal_op p1.(p_valid) < cardinal_op p2.(p_valid)).

Definition init := Mk_pos full_op full_op full_op full_op.
Definition is_full p := eq_op p.(p_cols) empty_op.
Definition has_valid p := negb (eq_op p.(p_valid) empty_op).

Definition next_valid_with_curr p :=
  let d := keep_min_op p.(p_valid) in
  let cols := (p.(p_cols) :&: (compl_op d))%C in
  let asc_diag := succ_op (p.(p_asc_diag) :|: d)%C in
  let desc_diag := pred_op (p.(p_desc_diag) :|: d)%C in
  let valid := (cols :&: compl_op (asc_diag :|: desc_diag))%C in
  Mk_pos cols asc_diag desc_diag valid.

Definition next_valid_without_curr p :=
  let d := keep_min_op p.(p_valid) in
  let valid := (p.(p_valid) :&: (compl_op d))%C in
  Mk_pos p.(p_cols) p.(p_asc_diag) p.(p_desc_diag) valid.


End Machine.

Arguments Mk_pos {_} p_cols p_asc_diag p_desc_diag p_valid.
Arguments p_cols [_] p.
Arguments p_asc_diag [_] p.
Arguments p_desc_diag [_] p.
Arguments p_valid [_] p.

Parametricity Pos.
(* Parametricity Pos_order. *)
Parametricity init.
Parametricity is_full.
Parametricity has_valid.
Parametricity next_valid_with_curr.
Parametricity next_valid_without_curr.

(*************************************************)
(** *** Abstract machine board                   *)
(*************************************************)

(** This implementation models the behavior of the machine
    representation. It is proof-oriented. *)

Module FSet <: POS.

Definition Pos := Pos {set 'I_n}.
Definition Pos_order := Pos_order {set 'I_n}.

Definition init := init {set 'I_n}.
Definition is_full := is_full {set 'I_n}.
Definition has_valid := has_valid {set 'I_n}.
Definition next_valid_with_curr := next_valid_with_curr {set 'I_n}.
Definition next_valid_without_curr := next_valid_without_curr {set 'I_n}.


Lemma Pos_wf: well_founded Pos_order. 
Admitted. (* XXX: TODO *)

Lemma next_valid_with_curr_wf: forall p, Pos_order (next_valid_with_curr p) p.
Admitted. (* XXX: TODO *)

Lemma next_valid_without_curr_wf: forall p, Pos_order (next_valid_without_curr p) p.
Admitted. (* XXX: TODO *)

End FSet.

(*************************************************)
(** *** Native machine board                     *)
(*************************************************)

(** This is the extraction-oriented definition. It is purely axiomatic
    and won't execute inside Coq. *)

Module R  := Make(Fintype).
Module Native := R.Native.

Module NSet <: POS.

Definition Pos := Pos Native.Int.
Definition Pos_order := Pos_order Native.Int.

Definition init := init Native.Int.
Definition is_full := is_full Native.Int.
Definition has_valid := has_valid Native.Int.
Definition next_valid_with_curr := next_valid_with_curr Native.Int.
Definition next_valid_without_curr := next_valid_without_curr Native.Int.

(* XXX: Follow from the refinements above. *)
Axiom Pos_wf: well_founded Pos_order.
Axiom next_valid_with_curr_wf: forall p, Pos_order (next_valid_with_curr p) p. 
Axiom next_valid_without_curr_wf: forall p, Pos_order (next_valid_without_curr p) p.

End NSet.

(*********************************************************)
(** ** Board refinement                                  *)
(*********************************************************)

Local Open Scope rel.

(*************************************************)
(** *** Abstract [->] Machine refinement         *)
(*************************************************)

(** From the abstract board to the machine board *)

Local Open Scope ring_scope.

Definition Rspec (p_spec: Spec.Pos)(p_word: FSet.Pos): Type :=
  [/\ Spec.inv p_spec
   ,  Spec.cols p_spec =i p_word.(p_cols)
   ,  Spec.asc_diag p_spec =i p_word.(p_asc_diag)
   ,  Spec.desc_diag p_spec =i p_word.(p_desc_diag)
   &  Spec.valid_cols p_spec =i p_word.(p_valid) ].
  
Global Instance Rspec_init: 
  refines Rspec Spec.init FSet.init.
Proof.
rewrite refinesE; split.
- by apply Spec.inv_init.
- rewrite /Spec.init/Spec.is_valid_col/Spec.cols /= /full_op/bitset.full_fin.
  move=> k /=.
  rewrite !inE. 
  apply/forallP=> i.
  apply/implyP=> _.
  by rewrite mxE.
- move=> k /=.
  rewrite !inE.
  apply/forallP=> x.
  by apply/implyP.
- move=> k /=.
  rewrite !inE /=.
  apply/forallP=> x.
  by apply/implyP.
- move=> k /=.
  rewrite !inE /=.
  apply/and4P; split=> //.
  + apply/forallP=> x.
    by apply/implyP.
  + apply/forallP=> x.
    apply/implyP=> _.
    by rewrite mxE.
  + apply/forallP=> x.
    by apply/implyP.
  + apply/forallP=> x.
    by apply/implyP.
Qed.

Global Instance Rspec_is_full: 
  refines (Rspec ==> param.bool_R) Spec.is_full FSet.is_full.
Proof.
rewrite refinesE.
move=> x y [Hinv Hcols Hasc_diag Hdesc_diag Hvalid].
suff ->: (Spec.is_full x = FSet.is_full y)
  by apply bool_Rxx.
rewrite /Spec.is_full/FSet.is_full/is_full
        /empty_op/bitset.empty_fin/eq_op/bitset.eq_fin.
move/setP: Hcols=> ->.
apply cards_eq0.
Qed.

(*
apply/idP/idP=> H.
- suff Hy: y.(p_cols) =i set0 by apply/eqP/setP.
  move=> i.
  move/existsP: {H} (H i) => [j /andP [Hb Hj]].
  rewrite !inE.
  apply/eqP.
  rewrite eqbF_neg -Hcols /Spec.cols/Spec.is_valid_col !inE /=.
  apply/negP.
  move/andP=> [Hj /forallP /(_ i)].
  by move/implyP=> /(_ Hb) /negP.
- move=> j. apply /existsP.
  move/eqP: H=> -> in Hcols.
  move: Hcols =>/(_ j).
  rewrite !inE /=.
  move=> Hval.
  apply negbT in Hval.
  rewrite /Spec.is_valid_col in Hval.
  rewrite negb_forall in Hval.
  move/existsP: Hval=> [i Hval].
  rewrite negb_imply in Hval.
  move/andP: Hval=> [Hi /negPn Hspec].
  exists i; by apply/andP.
*)

Global Instance Rspec_has_valid: 
  refines (Rspec ==> param.bool_R) Spec.has_valid FSet.has_valid.
Proof.
rewrite refinesE.
move=> x y [Hinv Hcols Hasc_diag Hdesc_diag Hvalid].
suff ->: (Spec.has_valid x = FSet.has_valid y)
  by apply bool_Rxx.
rewrite /Spec.has_valid/FSet.has_valid.
rewrite /has_valid.
rewrite /empty_op/bitset.empty_fin/eq_op/bitset.eq_fin.
rewrite -lt0n.
move/setP: Hvalid=> ->.
apply card_gt0.
Qed.

(*
apply/idP/idP=> H.
- move/setP: Hvalid=> <-.
  apply/eqP=> /setP Hvalid.
  suff [j Hval] : exists j, j \in valid x
      by move: Hvalid=> /(_ j); rewrite Hval inE.
  set b := Spec.p_board x in H *.
  set curr_i := Spec.p_curr_row x in H *.
  set curr_j := Spec.p_curr_col x in H *.
  have Hval_cols: (0 < #|Spec.valid_cols b curr_i curr_j|)
    by rewrite lt0n.
  move/card_gt0P: Hval_cols=> [j Hj].
  rewrite /Spec.is_valid/valid.
  by exists j.
- move/setP: Hvalid=> <- in H.
  rewrite /valid in H.
  rewrite -lt0n.
  apply /card_gt0P.
  move/set0Pn: H=> [j Hval].
  by exists j.
*)

Global Instance Rspec_next_valid_with_curr: 
  refines (Rspec ==> Rspec) Spec.next_valid_with_curr FSet.next_valid_with_curr.
Proof.
rewrite refinesE.
move=> x y [Hinv Hcols Hasc_diag Hdesc_diag Hvalid].
have Hspec_curr: [set Spec.p_curr_col x] = keep_min_op (p_valid y) by admit.
split=> //=;
  first by apply Spec.inv_next_valid_with_curr.
- rewrite Spec.next_with_cols ?Hspec_curr //.
  move/setP: Hcols=> ->.
  rewrite setDE //.
- rewrite (Spec.next_with_asc_diag x) //.
  have Hshr: forall (x y: {set 'I_n}), x =i y -> shrS x (inord 1) =i FSet.shrS y.
  admit.
  apply Hshr.
  move/setP: Hasc_diag=> ->.
  admit. (* XXX: probably false *)
- rewrite (Spec.next_with_desc_diag x) //.
  have Hshl: forall (x y: {set 'I_n}), x =i y -> shlS x (inord 1) =i FSet.shlS y.
  admit.
  apply Hshl.
  move/setP: Hdesc_diag=> ->.
  admit. (* XXX: probably false *)
- rewrite Spec.next_with_valid_cols.
  move/setP: Hvalid=> ->.
  rewrite -Hspec_curr //=.
  rewrite /compl_op/compl_fin //=.
  admit.
Admitted.

Global Instance Rspec_next_valid_without_curr: 
  refines (Rspec ==> Rspec) Spec.next_valid_without_curr FSet.next_valid_without_curr.
Proof.
rewrite refinesE.
move=> x y [Hinv Hcols Hasc_diag Hdesc_diag Hvalid].
split=> //=;
rewrite ?Spec.next_without_cols
        ?Spec.next_without_asc_diag 
        ?Spec.next_without_desc_diag 
        ?Spec.next_without_valid_cols //;
 try now apply Spec.inv_next_valid_without_curr.
move/setP: Hvalid=> ->.
rewrite /inter_op/inter_fin/compl_op/compl_fin/keep_min_op/keep_min_fin.
rewrite Spec.curr_col_valid //.
rewrite setDE.
move=> i.
rewrite !inE.
admit. (* Better/different spec for [keep_min] or for [curr_col_valid]? *)
Admitted.

(*************************************************)
(** *** Machine [->] Native refinement           *)
(*************************************************)

(** From the specification of machine words to native integers. *)

Definition T := [finType of 'I_n].

Module Fintype : FINTYPE with Definition T := T.
  Definition T: finType := T.
End Fintype.

Module R := bits.Make(Fintype).


Definition Rword (wp: FSet.Pos)(np: Native.Pos): Type
  := Pos_R _ _ R.Rbitset wp np.

(** XXX: This should follow directly by parametricity of the [Machine]
    section *)

Global Instance Rword_init: 
  refines Rword FSet.init Native.init.
Admitted. (* TODO *)

Global Instance Rword_is_full: 
  refines (Rword ==> param.bool_R) FSet.is_full Native.is_full.
Admitted. (* TODO *)

Global Instance Rword_has_valid: 
  refines (Rword ==> param.bool_R) FSet.has_valid Native.has_valid.
Admitted. (* TODO *)

Global Instance Rword_next_valid_with_curr: 
  refines (Rword ==> Rword) FSet.next_valid_with_curr Native.next_valid_with_curr.
Admitted. (* TODO *)

Global Instance Rword_next_valid_without_curr: 
  refines (Rword ==> Rword) FSet.next_valid_without_curr Native.next_valid_without_curr.
Admitted. (* TODO *)

(*************************************************)
(** *** Abstract [->] Native  refinement         *)
(*************************************************)

(** Composition of the previous refinements *)

Definition RPos: Spec.Pos -> NSet.Pos -> Type := Rspec \o Rword.


Global Instance RPos_init: 
  refines RPos Spec.init NSet.init.
Proof. eapply refines_trans; tc. Qed.

Global Instance RPos_is_full: 
  refines (RPos ==> param.bool_R) Spec.is_full NSet.is_full.
Proof. eapply refines_trans; tc. Qed.

Global Instance RPos_has_valid: 
  refines (RPos ==> param.bool_R) Spec.has_valid NSet.has_valid.
Proof. eapply refines_trans; tc. Qed.

Global Instance RPos_next_valid_with_curr: 
  refines (RPos ==> RPos) Spec.next_valid_with_curr NSet.next_valid_with_curr.
Proof. eapply refines_trans; tc. Qed.

Global Instance RPos_next_valid_without_curr: 
  refines (RPos ==> RPos) Spec.next_valid_without_curr NSet.next_valid_without_curr.
Proof. eapply refines_trans; tc. Qed.

Local Close Scope rel.

(*****************************************************************)
(** * n-queens positions                                         *)
(*****************************************************************)


Section Queen_generic.

Variable Pos: Type.

Variable init: Pos.
Variable is_full: Pos -> bool.
Variable has_valid: Pos -> bool.
Variable next_valid_with_curr: Pos -> Pos.
Variable next_valid_without_curr: Pos -> Pos.

Variable Pos_order: Pos -> Pos -> Prop.
Variable Pos_wf: well_founded Pos_order.
Variable next_valid_with_curr_wf: forall p, Pos_order (next_valid_with_curr p) p.
Variable next_valid_without_curr_wf: forall p, Pos_order (next_valid_without_curr p) p.

Definition nqueens_loop: Pos -> nat ->  nat * Pos.
simple
  refine (Fix Pos_wf (fun pos => nat -> nat * Pos) 
              (fun p nqueens_loop score  =>
    (match has_valid p as b
           return b = has_valid p -> nat * Pos with
    | false => fun _ => (score, p) 
    | true => fun His_not_full => 
      let rec_result := 
          if is_full p then
            1%nat
          else
            let p' := next_valid_with_curr p in
            let (score' , _) := nqueens_loop p' _ score in
            score'
      in
      let score' := (score + rec_result)%N in
      let p' := next_valid_without_curr p in
      let total := nqueens_loop p' _ score' in
      total
     end) (Logic.eq_refl _))); 
  eauto using next_valid_with_curr_wf, next_valid_without_curr_wf.
Defined.


Definition nqueens :=
  let (res , _) := nqueens_loop init 1 in
  res.

End Queen_generic.

Parametricity Acc.
Parametricity nqueens_loop.
Parametricity nqueens.

Module Make (P: POS).

Definition nqueens 
  := nqueens P.Pos 
             P.init P.is_full P.has_valid 
             P.next_valid_with_curr P.next_valid_without_curr
             P.Pos_order P.Pos_wf
             P.next_valid_with_curr_wf P.next_valid_without_curr_wf.

End Make.

(*********************************************************)
(** ** Correctness                                       *)
(*********************************************************)

Module Prove := Make Spec.

Definition valid_board (b: Spec.board): bool.
Admitted. (* XXX: define *)

Definition solutions :=  [set x in Spec.board | valid_board x ].

Lemma correctness_spec: Prove.nqueens = #| solutions |.
Admitted. (* XXX *)

(*********************************************************)
(** ** Extraction                                        *)
(*********************************************************)

Module Run := Make NSet.

(* XXX: drop the code to a file and check that it's efficient. *)
(* XXX: write benchmark handler *)
(* Recursive Extraction Run.nqueens. *)

Lemma eq_nqueens: Prove.nqueens = Run.nqueens.
Proof.
have Href_eq: refines Logic.eq Prove.nqueens Run.nqueens.
{
  apply refines_nat_eq.
  param nqueens_R. 
  rewrite refinesE.
  all: admit. 
}
by rewrite refinesE in Href_eq.
Admitted. (* XXX: complete missing instances *)

Lemma correctness: Run.nqueens = #| solutions |.
Proof. by rewrite <- correctness_spec, eq_nqueens. Qed.
