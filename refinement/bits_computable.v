From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp
Require Import choice fintype finset tuple finfun.
From CoqEAL
Require Import hrel param refinements.

Require Import bitseq bitword notation computable_N.

Import Refinements.Op.
Import Logical.Op.
Import Sets.Op.

Local Open Scope rel_scope.
Local Open Scope bits_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**

 The refinement relations have a type of the following form

<<
   R : specification -> implementation -> Type
>>

  while the transport lemmas have the form

<<
   Lemma R_op: refines refinement_relation specification implementation.
>>

*)


(************************************************************************)
(** * Refinement Relations                                                 *)
(************************************************************************)

(* Sets and efficient bit operators *)
Require Import bitocaml bitset.

Module Type FINTYPE.
  Parameter T: finType.
  Parameter n: nat.
  Parameter card_of_T : #|T| = n.
End FINTYPE.

Module Make (FT: FINTYPE).

Definition T := FT.T.
Definition n := FT.n.
Definition FT_T_eq_n := FT.card_of_T.

Lemma T_eq_n : #|T| = n.
Proof.
  by rewrite FT_T_eq_n /n.
Qed.

Module Wordsize.
  Definition wordsize := n.
End Wordsize.

Module Native := MakeOps(Wordsize).

(** ** From sets over a finite type to machine words: *)

Definition Rfin: {set T} -> 'B_#|T| -> Type  := fun_hrel (@finB T).
Definition Rfin' : 'B_#|T| -> 'B_n -> Type := (fun a b => val a =  val b).
Definition Rtuple : 'B_n -> bitseq -> Type :=  fun a b => tval a = b.
Definition Rnative: bitseq -> Native.Int -> Type := fun_hrel (bitsFromInt Native.w).

Definition Rbitseq : {set T} -> bitseq -> Type := Rfin \o Rfin' \o Rtuple.
Definition Rbitset: {set T} -> Native.Int -> Type := Rfin \o (Rfin' \o (Rtuple \o Rnative)).

(** ** From finite type to machine words: *)

Definition Rord: T -> 'I_#| T | -> Type := fun t n => enum_rank t = n.
Definition Rord': 'I_#| T | -> 'I_n -> Type := fun t t' => val t = val t'.
Definition RidxI: 'I_n -> nat -> Type := fun k n => val k = n.
CoInductive RidxN: nat -> Native.Int -> Type :=
  Ridx_spec (k: nat)(i: Native.Int)(b: bitseq) of
    Rnative b i
  & (k <= #| T |)%N
  & b = bitn #| T | k : RidxN k i.

Definition Rbits: T -> Native.Int -> Type :=
  Rord \o (Rord' \o (RidxI \o RidxN)).
Definition Rbitsq: T -> nat -> Type :=
  Rord \o Rord' \o RidxI.

(************************************************************************)
(** * Notations                                                         *)
(************************************************************************)

(** ** Notations for native integers *)

Global Instance   eq_N : eq_of   Native.Int := Native.eq.
Global Instance zero_N : zero_of Native.Int := Native.zero.
Global Instance  one_N : one_of  Native.Int := Native.one.
Global Instance   or_N : or_of   Native.Int := Native.lor.
Global Instance  shl_N : shl_of  Native.Int Native.Int := Native.lsl.
Global Instance  and_N : and_of  Native.Int := Native.land.
Global Instance  shr_N : shr_of  Native.Int Native.Int := Native.lsr.
Global Instance  not_N : not_of  Native.Int := Native.lnot.
Global Instance  xor_N : xor_of  Native.Int := Native.lxor.
Global Instance  add_N : add_of  Native.Int := Native.add.
Global Instance  sub_N : sub_of  Native.Int := Native.sub.
Global Instance  opp_N : opp_of  Native.Int := Native.opp.

Global Instance get_N       : get_of Native.Int Native.Int       := get.
Global Instance singleton_N : singleton_of Native.Int Native.Int := singleton (Bits := Native.Int).
Global Instance compl_N     : compl_of Native.Int                := compl.
Global Instance empty_N     : empty_of Native.Int                := empty (Bits := Native.Int).
Global Instance full_N      : full_of Native.Int                 := full  (Bits := Native.Int).
Global Instance set_N       : set_of Native.Int Native.Int       := insert.
Global Instance remove_N    : remove_of Native.Int Native.Int    := remove.
Global Instance inter_N     : inter_of Native.Int                := inter.
Global Instance union_N     : union_of Native.Int                := union.
Global Instance symdiff_N   : symdiff_of Native.Int              := symdiff.
Global Instance subset_N    : subset_of Native.Int               := subset.
Global Instance cardinal_N  : cardinal_of nat Native.Int.
Admitted.
Global Instance keep_min_N  : keep_min_of Native.Int.
Admitted.
Global Instance succ_N      : succ_of Native.Int.
Admitted.
Global Instance pred_N      : pred_of Native.Int.
Admitted.

(** ** Notations for bit sequences (of size #| T |) *)

(* These classes are not strictly necessary: the code below would work
without them. *)

Global Instance eq_s   : eq_of bitseq   := fun x y => x == y.
Global Instance zero_S : zero_of bitseq := '0_n.
Global Instance  one_S : one_of  bitseq := bitn n 1.
Global Instance   or_S : or_of   bitseq := ors.
Global Instance  shl_S : shl_of  nat bitseq := shls.
Global Instance  and_S : and_of  bitseq := ands.
Global Instance  shr_S : shr_of  nat bitseq := shrs.
Global Instance  not_S : not_of  bitseq := negs.
Global Instance  xor_S : xor_of  bitseq := xors.
Global Instance  add_S : add_of  bitseq := adds.
Global Instance  sub_S : sub_of  bitseq := subs.

Global Instance get_S       : get_of nat bitseq       := get.
Global Instance singleton_S : singleton_of nat bitseq := singleton (Bits := bitseq).
Global Instance compl_S     : compl_of bitseq            := compl (Bits := bitseq).
Global Instance full_S      : full_of bitseq             := full (Bits := bitseq).
Global Instance empty_S     : empty_of bitseq            := empty (Bits := bitseq).
Global Instance set_S       : set_of nat bitseq       := insert (Bits := bitseq).
Global Instance remove_S    : remove_of nat bitseq    := remove (Bits := bitseq).
Global Instance inter_S     : inter_of bitseq            := inter.
Global Instance union_S     : union_of bitseq            := union.
Global Instance symdiff_S   : symdiff_of bitseq          := symdiff.
Global Instance subset_S    : subset_of bitseq           := subset.

(************************************************************************)
(** * From finset to bit vectors                                        *)
(************************************************************************)

Lemma eq_bool_R x y : x = y -> bool_R x y.
Proof. by move->; apply/bool_Rxx. Qed.

Let can_enum D := can2_imset_pre D (@enum_valK T) (@enum_rankK _).
Let enum_can D := can2_imset_pre D (@enum_rankK T) (@enum_valK _).

Ltac runfold_cut :=
  rewrite /singleton/get/full/empty/insert/remove/subset.

Ltac runfold_op  :=
  rewrite
          /eq_op/one_op/zero_op/shl_op/and_op/or_op/sub_op
          /singleton_op/set_op/get_op/full_op/empty_op/remove_op/subset_op.

Ltac runfold_fin :=
  rewrite /finB/Rfin/eq_fin
          /singleton_fin/set_fin/get_fin/full_fin/empty_fin/remove_fin/subset_fin.

Ltac runfold_B   :=
  rewrite /eq_B/one_B/zero_B/shl_B/and_B/or_B/sub_B
          /singleton_B/set_B/get_B/full_B/empty_B/remove_B/subset_B.

(* Ltac runfold_N  := rewrite /get_B/one_B/zero_B/shl_B/and_B/or_B *)

Ltac runfold := runfold_op; runfold_fin; runfold_B; runfold_cut.

Global Instance Rfin_eq:
  refines (Rfin ==> Rfin ==> param.bool_R) eq_op eq_op.
Proof.
rewrite refinesE=> E bs <- E' bs' <-; apply/eq_bool_R; runfold.
by rewrite (inj_eq (can_inj (@bitFK _))).
Qed.

Global Instance Rfin_get:
  refines (Rord ==> Rfin ==> param.bool_R) get_op get_op.
Proof.
rewrite refinesE => t _ <- E2 bs2 <-; apply eq_bool_R; runfold.
by rewrite /finB can_enum inE mem_setb gets_def !size_tuple bitn_zero.
Qed.

Global Instance Rfin_singleton:
    refines (Rord ==> Rfin) singleton_op singleton_op.
Proof.
rewrite refinesE => t _ <-; runfold; apply/setP=> x.
rewrite /singleton /shl_op /shl_B /one_op /one_B /finB.
by rewrite !inE can_enum inE mem_setB tnth_shlB_one (inj_eq enum_rank_inj).
Qed.

Global Instance Rfin_full :
  refines Rfin full_op full_op.
Proof.
rewrite refinesE; do 3!runfold.
apply/setP=> t; rewrite can_enum inE.
(* XXX *)
have := full_def; rewrite /decB /subB /= => <-.
by rewrite mem_setb nth_nseq ltn_ord inE.
Qed.

Global Instance Rfin_empty :
  refines Rfin empty_op empty_op.
Proof.
rewrite refinesE; do 2!runfold.
by apply/setP=> t; rewrite can_enum inE mem_setb nth_nseq ltn_ord inE.
Qed.

Global Instance Rfin_insert:
  refines (Rord ==> Rfin ==> Rfin) set_op set_op.
Proof.
rewrite refinesE => t _ <- E bs2 <-; do 2!runfold.
apply/setP=> x.
rewrite !can_enum inE mem_setB !tnth_liftz 3!inE orbC mem_setB tnth_shlB_one.
by rewrite (inj_eq enum_rank_inj) eq_sym.
Qed.


Global Instance Rfin_remove:
  refines (Rfin ==> Rord ==> Rfin) remove_op remove_op.
Proof.
(* XXX: proof duplication with [Rfin_insert] *)
rewrite refinesE => E bs2 <- t _ <-; do 2!runfold.
apply/setP=> x; rewrite !can_enum inE mem_setB 3!inE mem_setB.
(* XXX: FIXME *)
rewrite !(tnth_nth false) /= -{2}[#|T|](size_tuple bs2) -(sets_def _ _ false).
rewrite /setls size_tuple ltn_ord nth_set_nth /=.
case: ifP => [/eqP/val_inj/enum_rank_inj->|].
  by rewrite eqxx.
by rewrite val_eqE (inj_eq enum_rank_inj) => ->.
Qed.

Global Instance Rfin_compl :
  refines (Rfin ==> Rfin) compl_op compl_op.
Proof.
by rewrite refinesE => E bs <-; rewrite /Rfin /fun_hrel Fcompl_morphL.
Qed.

Global Instance Rfin_union:
  refines (Rfin ==> Rfin ==> Rfin) union_op union_op.
Proof.
rewrite refinesE => E1 bs1 <- E2 bs2 <-.
by rewrite /Rfin /fun_hrel Funion_morphL.
Qed.

Global Instance Rfin_inter:
  refines (Rfin ==> Rfin ==> Rfin) inter_op inter_op.
Proof.
rewrite refinesE => E1 bs1 <- E2 bs2 <- .
by rewrite /Rfin /fun_hrel Finter_morphL.
Qed.

Global Instance Rfin_symdiff:
  refines (Rfin ==> Rfin ==> Rfin) symdiff_op symdiff_op.
Proof.
rewrite refinesE => E1 bs1 <- E2 bs2 <- .
by rewrite /Rfin /fun_hrel Fsymdiff_morphL.
Qed.

Global Instance Rfin_subset:
  refines (Rfin ==> Rfin ==> bool_R) subset_op subset_op.
Proof.
rewrite refinesE => E1 bs1 <- E2 bs2 <-; apply eq_bool_R; do 2!runfold.
apply/setIidPl/eqP; rewrite -Finter_morphL; last by move->.
by move/(can_inj (@bitFK _)).
Qed.

(** Rfin' lemmas *)
(*Lemma Rfin'_implies_eq : forall a b, Rfin' a b -> (tval a = b).
Proof.
  move => a b. by rewrite /Rfin'.
Qed.*)

Notation RfinC := (Rfin \o Rfin') (only parsing).
Notation RordC := (Rord \o Rord') (only parsing).

(* Lemma tcast_injective : injective (tcast (T := bool) T_eq_n).
Proof. exact: can_inj (tcastK T_eq_n). Qed. *)

Global Instance Rfin'_eq:
  refines (Rfin' ==> Rfin' ==> param.bool_R) eq_op eq_op.
Proof.
  rewrite refinesE => E bs; rewrite /Rfin' => /= HE.
  rewrite /Rfin' => E2 bs2 /= HE2. apply/eq_bool_R.
  rewrite /eq_op /eq_B -2?(inj_eq val_inj) //=.
  by rewrite HE HE2.
Qed.


Global Instance Rfin'_empty:
  refines Rfin' empty_op empty_op.
Proof.
  rewrite refinesE; rewrite /Rfin'; apply/eqP; rewrite //=.
  by rewrite T_eq_n.
Qed.

Global Instance Rfin'_full:
  refines Rfin' full_op full_op.
Proof.
  rewrite refinesE; rewrite /Rfin'; apply/eqP; rewrite //=.
  by rewrite T_eq_n.
Qed.

Global Instance Rfin'_compl :
  refines (Rfin' ==> Rfin') compl_op compl_op.
Proof.
  by rewrite refinesE => bs bs'; rewrite /Rfin' => /= ->.
Qed.

Global Instance Rfin'_union:
  refines (Rfin' ==> Rfin' ==> Rfin') union_op union_op.
Proof.
  rewrite refinesE => b b'; rewrite /Rfin' => /= Hb.
  move => c c'; rewrite /Rfin' => /= Hc.
  by rewrite Hb Hc.
Qed.

Global Instance Rfin'_insert:
  refines (Rord' ==> Rfin' ==> Rfin') set_op set_op.
Proof.
  rewrite refinesE => v v'; rewrite /Rfin' /Rord' => /= H.
  by move => a a' /= ->; rewrite H; rewrite T_eq_n.
Qed.

Global Instance Rfin'_remove:
  refines (Rfin' ==> Rord' ==> Rfin') remove_op remove_op.
Proof.
  rewrite refinesE /Rfin' /Rord' => a a' /= Ha. move => v v' /= Hv.
  by rewrite Ha Hv T_eq_n.
Qed.

Global Instance Rfin'_get:
  refines (Rord' ==> Rfin' ==> param.bool_R) get_op get_op.
Proof.
  rewrite refinesE /Rord' /Rfin'.
  move => t t' /= Ht a a' /= Ha.
  rewrite /= /get_op /get_B /get. runfold. rewrite /andB /shlB /=.
  apply/eq_bool_R. by rewrite -2?(inj_eq val_inj) /= Ht Ha T_eq_n.
Qed.

Global Instance Rfin'_singleton:
    refines (Rord' ==> Rfin') singleton_op singleton_op.
Proof.
  rewrite refinesE /Rord' /Rfin'.
  move => t t' /= <-. by rewrite [X in bitn X 1]T_eq_n.
Qed.

Global Instance Rfin'_inter:
  refines (Rfin' ==> Rfin' ==> Rfin') inter_op inter_op.
Proof.
  rewrite refinesE /Rfin' => a a' /= Ha b b' /= Hb.
  by rewrite Ha Hb.
Qed.

Global Instance Rfin'_symdiff:
  refines (Rfin' ==> Rfin' ==> Rfin') symdiff_op symdiff_op.
Proof.
  rewrite refinesE /Rfin' => a a' /= Ha b b' /= Hb.
  by rewrite Ha Hb.
Qed.

Global Instance Rfin'_subset:
  refines (Rfin' ==> Rfin' ==> param.bool_R) subset_op subset_op.
Proof.
  rewrite refinesE /Rfin' => a a' /= Ha b b' /= Hb.
  rewrite /= /subset_op /subset_B /subset. runfold. rewrite /andB /=.
  by rewrite -?(inj_eq val_inj) /= Ha Hb; apply/eq_bool_R.
Qed.

(** Composition lemmas for RfinC *)
(** ******************************)

Global Instance RfinC_eq:
  refines (RfinC ==> RfinC ==> param.bool_R) eq_op eq_op.
Proof. param_comp eq_R. Qed.

Global Instance RfinC_full :
  refines RfinC full_op full_op.
Proof. param_comp full_R. Qed.

Global Instance RfinC_empty :
  refines RfinC empty_op empty_op.
Proof. param_comp empty_R. Qed.

Global Instance RfinC_singleton :
  refines (RordC ==> RfinC) singleton_op singleton_op.
Proof. param_comp singleton_R. Qed.

Global Instance RfinC_get :
  refines (RordC ==> RfinC ==> param.bool_R) get_op get_op.
Proof. param_comp get_R. Qed.

Global Instance RfinC_insert:
  refines (RordC ==> RfinC ==> RfinC) set_op set_op.
Proof. param_comp set_R. Qed.

Global Instance RfinC_remove:
  refines (RfinC ==> RordC ==> RfinC) remove_op remove_op.
Proof. param_comp remove_R. Qed.

Global Instance RfinC_compl :
  refines (RfinC ==> RfinC) compl_op compl_op.
Proof. param_comp compl_R. Qed.

Global Instance RfinC_union:
  refines (RfinC ==> RfinC ==> RfinC) union_op union_op.
Proof. param_comp union_R. Qed.

Global Instance RfinC_inter:
  refines (RfinC ==> RfinC ==> RfinC) inter_op inter_op.
Proof. param_comp inter_R. Qed.

Global Instance RfinC_symdiff:
  refines (RfinC ==> RfinC ==> RfinC) symdiff_op symdiff_op.
Proof. param_comp symdiff_R. Qed.

Global Instance RfinC_subset:
  refines (RfinC ==> RfinC ==> bool_R) subset_op subset_op.
Proof. param_comp subset_R. Qed.

(* Definition cardTT (A : {set T}) := #|A|. *)
(* Global Instance Rfin_cardinal: *)
(*   refines (Rfin ==> eq) (cardTT) (fun x => nats (cardinal_smart x)). *)
(* Proof. *)
(* rewrite !refinesE => A1 y1 <-. *)
(* by rewrite /cardTT cardinalP (card_imset _ enum_val_inj) cardbP. *)
(* Qed. *)

(* XXX: To be moved *)
Lemma arg_min_enum_rank (aT : finType) (A : {set 'I_#|aT| }) x (h_x : x \in A) :
  enum_rank [arg min_(k < (enum_val x) in [set enum_val x0 | x0 in A]) enum_rank k] =
  [arg min_(k < x in A) k].
Proof.
case: arg_minP; first by apply/imsetP; exists x.
move=> i /imsetP[xr xrin ->]; rewrite enum_valK => hmin.
case: arg_minP => // yr yrin umin.
have Ux: enum_val yr \in [set enum_val x0 | x0 in A].
  by apply/imsetP; exists yr.
have P1 := hmin _ Ux; rewrite enum_valK in P1.
have P2 := umin _ xrin.
by have/andP := conj P1 P2; rewrite -eqn_leq => /eqP /val_inj.
Qed.

(* Global Instance Rfin_ntz x (h_in : x \in T) : *)
(*   refines (Rfin ==> eq) (fun E => val (enum_rank [arg min_(k < x in E) enum_rank k])) *)
(*           (fun x => nats (ntz x)). *)
(* Proof. *)
(* rewrite !refinesE => A1 b1 <-. *)
(* rewrite ntzP /=. *)
(* rewrite /finB. *)
(* have -> : x = enum_val (enum_rank x) by rewrite enum_rankK. *)
(* rewrite arg_min_enum_rank. *)
(* Admitted. *)


(************************************************************************)
(** * From bit vectors to bit sequences                                 *)
(************************************************************************)

Global Instance Rtuple_eq:
  refines (Rtuple ==> Rtuple ==> param.bool_R) eq_op eq_op.
Proof.
rewrite refinesE => a _ <- b _ <-.
rewrite /eq_op/eq_B/eq_s val_eqE.
by apply eq_bool_R.
Qed.

Global Instance Rtuple_zero: refines Rtuple 0%C 0%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rtuple_one: refines Rtuple 1%C 1%C.
Proof. by rewrite refinesE. Qed.

Global Instance Rtuple_empty: refines Rtuple empty_op empty_op.
Proof. by rewrite refinesE. Qed.

Global Instance Rtuple_full: refines Rtuple full_op full_op.
Proof.
  rewrite refinesE /Rtuple.
Admitted.

Global Instance Rtuple_lnot:
  refines (Rtuple ==> Rtuple) ~%C ~%C.
Proof. by rewrite refinesE=> bs w <-. Qed.

Global Instance Rtuple_land:
  refines (Rtuple ==> Rtuple ==> Rtuple) &&%C &&%C.
Proof. by rewrite !refinesE => bs1 w1 <- bs2 w2 <-. Qed.

Global Instance Rtuple_lor:
  refines (Rtuple ==> Rtuple ==> Rtuple) ||%C ||%C.
Proof. by rewrite !refinesE => bs1 w1 <- bs2 w2 <-. Qed.

Global Instance Rtuple_lxor:
  refines (Rtuple ==> Rtuple ==> Rtuple) ^^%C ^^%C.
Proof. by rewrite !refinesE => bs1 w1 <- bs2 w2 <-. Qed.

Global Instance Rtuple_lsr:
  refines (Rtuple ==> RidxI ==> Rtuple) :>>:%C :>>:%C.
Proof. by rewrite !refinesE => bs1 w1 <- bs2 w2 <-. Qed.

Global Instance Rtuple_lsl:
  refines (Rtuple ==> RidxI ==> Rtuple) :<<:%C :<<:%C.
Proof. by rewrite !refinesE => bs1 w1 <- bs2 w2 <-. Qed.

Global Instance Rtuple_add:
  refines (Rtuple ==> Rtuple ==> Rtuple) (@addB _) adds.
Proof.
rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
by rewrite (adds_relE (k := n) (bv1 := bs1)(bv2 := bs2)).
Qed.

Global Instance Rtuple_sub:
  refines (Rtuple ==> Rtuple ==> Rtuple) (@subB _) subs.
Proof.
rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
by rewrite (subs_relE (k := n)(bv1 := bs1)(bv2 := bs2)).
Qed.

Global Instance Rtuple_opp:
  refines (Rtuple ==> Rtuple) (@oppB _) opps.
Proof.
rewrite !refinesE => bs w <- .
by rewrite (opps_relE (k := n)(bv := bs)).
Qed.


(************************************************************************)
(** * From bit words to bit tuples 'W_n -> 'B_n                         *)
(************************************************************************)

(* =Rword= *)
Definition Rword : 'W_n -> 'B_n -> Type := fun_hrel (@wrdB n).
(* =end= *)
(* =Rvector= *)
Definition Rvector : 'W_n -> bitseq -> Type := Rword \o Rtuple.
(* =end= *)

Instance Rword_and:
  refines (Rword ==> Rword ==> Rword) (@andw n) (@andB n).
Proof.
rewrite !refinesE => w1 b1 <- w2 b2 <-.
by rewrite /Rword /fun_hrel; apply/ffunP=> i; rewrite !ffunE tnth_liftz.
Qed.

Instance Rvector_and :
  refines (Rvector ==> Rvector ==> Rvector) (@andw n) ands.
Proof. by eapply refines_trans; tc. Qed.

Instance Rword_neg :
  refines (Rword ==> Rword) (@negw n) (@negB n).
Proof.
rewrite !refinesE => w1 b1 <-.
by rewrite /Rword /fun_hrel; apply/ffunP=> i; rewrite !ffunE tnth_map.
Qed.

Section Nand.
  Variables (B: Type)
            (and: B -> B -> B)
            (neg: B -> B).

  Definition nand (b1 b2: B): B := neg (and b1 b2).

End Nand.

Parametricity nand.

Instance Rword_nand:
  refines (Rword ==> Rword ==> Rword)
          (nand (@andw n) (@negw n))
          (nand (@andB n) (@negB n)).
Proof. param nand_R. Qed.


(************************************************************************)
(** * Compositions of Rbitseq                                           *)
(************************************************************************)

Global Instance Rbitseq_eq:
  refines (Rbitseq ==> Rbitseq ==> param.bool_R) eq_op eq_op.
Proof. do 2 (eapply refines_trans; tc). Qed.

Global Instance Rbitseq_get:
  refines (Rbitsq ==> Rbitseq ==> param.bool_R) get_op get_op.
Proof.
  param_comp get_R.
Qed.

Global Instance Rbitseq_singleton:
  refines (Rbitsq ==> Rbitseq) singleton_op singleton_op.
Proof.
  eapply refines_trans; tc.
  rewrite refinesE => a b; rewrite /RidxI => /= Rab.
  by rewrite /Rtuple /= Rab //=.
Qed.

Global Instance Rbitseq_empty:
  refines Rbitseq empty_op empty_op.
Proof. param_comp empty_R. Qed.

Global Instance Rbitseq_full:
  refines Rbitseq full_op full_op.
Proof.
  param_comp full_R.
Qed.

Global Instance Rbitseq_insert:
  refines (Rbitsq ==> Rbitseq ==> Rbitseq) set_op set_op.
Proof.
  eapply refines_trans; tc.
  rewrite refinesE /RidxI /Rtuple => a b /= Rab x y /= Rxy.
  by rewrite Rab Rxy.
Qed.

Global Instance Rbitseq_not:
  refines (Rtuple ==> Rtuple) ~%C ~%C.
Proof.
  by rewrite refinesE /Rtuple => a b /= ->.
Qed.

Global Instance Rbitseq_remove:
  refines (Rbitseq ==> Rbitsq ==> Rbitseq) remove_op remove_op.
Proof.
  eapply refines_trans; tc.
  rewrite refinesE /Rbitseq /Rbitsq /Rtuple /RidxI.
  move => a b /= Rab x y /= Rxy. by rewrite Rab Rxy.
Qed.

Global Instance Rbitseq_compl:
  refines (Rbitseq ==> Rbitseq) compl_op compl_op.
Proof. param_comp compl_R. Qed.

Global Instance Rbitseq_union:
  refines (Rbitseq ==> Rbitseq ==> Rbitseq) union_op union_op.
Proof. param_comp union_R. Qed.

Global Instance Rbitseq_inter:
  refines (Rbitseq ==> Rbitseq ==> Rbitseq) inter_op inter_op.
Proof. param_comp inter_R. Qed.

Global Instance Rbitseq_symdiff:
  refines (Rbitseq ==> Rbitseq ==> Rbitseq) symdiff_op symdiff_op.
Proof. param_comp symdiff_R. Qed.

Global Instance Rbitseq_subset:
  refines (Rbitseq ==> Rbitseq ==> bool_R) subset_op subset_op.
Proof. param_comp subset_R. Qed.

End Make.
