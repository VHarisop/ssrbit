From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp
Require Import choice fintype finset tuple finfun.
From CoqEAL
Require Import hrel param refinements.

Require Import bitseq bitword notation.

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
Require Import bitset.

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

(** ** From sets over a finite type to machine words: *)

Definition Rfin: {set T} -> 'B_#|T| -> Type  := fun_hrel (@finB T).
Definition Rcard : 'B_#|T| -> 'B_n -> Type := (fun a b => val a =  val b).
Definition Rtuple : 'B_n -> bitseq -> Type :=  fun a b => tval a = b.

Definition Rbitseq : {set T} -> bitseq -> Type := Rfin \o Rcard \o Rtuple.

(** ** From finite type to machine words: *)

Definition Rord: T -> 'I_#| T | -> Type := fun t n => enum_rank t = n.
Definition Rord': 'I_#| T | -> 'I_n -> Type := fun t t' => val t = val t'.
Definition RidxI: 'I_n -> nat -> Type := fun k n => val k = n.

Definition Rbitsq: T -> nat -> Type :=
  Rord \o Rord' \o RidxI.

(************************************************************************)
(** * Notations                                                         *)
(************************************************************************)

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
Global Instance diff_S      : diff_of bitseq             := diff (Bits := bitseq).
Global Instance subset_S    : subset_of bitseq           := subset.
Global Instance card_S      : cardinal_of nat bitseq := cards.

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

Global Instance Rfin_diff:
  refines (Rfin ==> Rfin ==> Rfin) diff_op diff_op.
Proof.
rewrite refinesE => E1 bs1 <- E2 bs2 <- .
by rewrite /Rfin /fun_hrel Fdiff_morphL.
Qed.

Global Instance Rfin_subset:
  refines (Rfin ==> Rfin ==> bool_R) subset_op subset_op.
Proof.
rewrite refinesE => E1 bs1 <- E2 bs2 <-; apply eq_bool_R; do 2!runfold.
apply/setIidPl/eqP; rewrite -Finter_morphL; last by move->.
by move/(can_inj (@bitFK _)).
Qed.

Global Instance Rfin_cardinal:
  refines (Rfin ==> eq) (cardinal_op) cardinal_op.
Proof.
  rewrite !refinesE => A1 y1 <-.
  by rewrite /cardinal_op /cardinal_fin (card_imset _ enum_val_inj) cardbP.
Qed.

Notation RfinC := (Rfin \o Rcard) (only parsing).
Notation RordC := (Rord \o Rord') (only parsing).

Global Instance Rcard_eq:
  refines (Rcard ==> Rcard ==> param.bool_R) eq_op eq_op.
Proof.
  rewrite refinesE => E bs; rewrite /Rcard => /= HE.
  rewrite /Rcard => E2 bs2 /= HE2. apply/eq_bool_R.
  rewrite /eq_op /eq_B -2?(inj_eq val_inj) //=.
  by rewrite HE HE2.
Qed.

Global Instance Rcard_empty:
  refines Rcard empty_op empty_op.
Proof.
  rewrite refinesE; rewrite /Rcard; apply/eqP; rewrite //=.
  by rewrite T_eq_n.
Qed.

Global Instance Rcard_full:
  refines Rcard full_op full_op.
Proof.
  rewrite refinesE; rewrite /Rcard; apply/eqP; rewrite //=.
  by rewrite T_eq_n.
Qed.

Global Instance Rcard_compl :
  refines (Rcard ==> Rcard) compl_op compl_op.
Proof.
  by rewrite refinesE => bs bs'; rewrite /Rcard => /= ->.
Qed.

Global Instance Rcard_union:
  refines (Rcard ==> Rcard ==> Rcard) union_op union_op.
Proof.
  rewrite refinesE => b b'; rewrite /Rcard => /= Hb.
  move => c c'; rewrite /Rcard => /= Hc.
  by rewrite Hb Hc.
Qed.

Global Instance Rcard_insert:
  refines (Rord' ==> Rcard ==> Rcard) set_op set_op.
Proof.
  rewrite refinesE => v v'; rewrite /Rcard /Rord' => /= H.
  by move => a a' /= ->; rewrite H; rewrite T_eq_n.
Qed.

Global Instance Rcard_remove:
  refines (Rcard ==> Rord' ==> Rcard) remove_op remove_op.
Proof.
  rewrite refinesE /Rcard /Rord' => a a' /= Ha. move => v v' /= Hv.
  by rewrite Ha Hv T_eq_n.
Qed.

Global Instance Rcard_get:
  refines (Rord' ==> Rcard ==> param.bool_R) get_op get_op.
Proof.
  rewrite refinesE /Rord' /Rcard.
  move => t t' /= Ht a a' /= Ha.
  rewrite /= /get_op /get_B /get. runfold. rewrite /andB /shlB /=.
  apply/eq_bool_R. by rewrite -2?(inj_eq val_inj) /= Ht Ha T_eq_n.
Qed.

Global Instance Rcard_singleton:
    refines (Rord' ==> Rcard) singleton_op singleton_op.
Proof.
  rewrite refinesE /Rord' /Rcard.
  move => t t' /= <-. by rewrite [X in bitn X 1]T_eq_n.
Qed.

Global Instance Rcard_inter:
  refines (Rcard ==> Rcard ==> Rcard) inter_op inter_op.
Proof.
  rewrite refinesE /Rcard => a a' /= Ha b b' /= Hb.
  by rewrite Ha Hb.
Qed.

Global Instance Rcard_symdiff:
  refines (Rcard ==> Rcard ==> Rcard) symdiff_op symdiff_op.
Proof.
  rewrite refinesE /Rcard => a a' /= Ha b b' /= Hb.
  by rewrite Ha Hb.
Qed.

Global Instance Rcard_diff:
  refines (Rcard ==> Rcard ==> Rcard) diff_op diff_op.
Proof.
  rewrite refinesE /Rcard => a a' /= Ha b b' /= Hb.
  by rewrite Ha Hb.
Qed.

Global Instance Rcard_subset:
  refines (Rcard ==> Rcard ==> param.bool_R) subset_op subset_op.
Proof.
  rewrite refinesE /Rcard => a a' /= Ha b b' /= Hb.
  rewrite /= /subset_op /subset_B /subset. runfold. rewrite /andB /=.
  by rewrite -?(inj_eq val_inj) /= Ha Hb; apply/eq_bool_R.
Qed.

Global Instance Rcard_card:
  refines (Rcard ==> eq) cardinal_op cardinal_op.
Proof.
  rewrite refinesE /Rcard => x y /= Rxy.
  by rewrite /cardinal_op/cardinal_B/cardinal/cardinal_op/card_B/cardB Rxy.
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

Global Instance RfinC_diff:
  refines (RfinC ==> RfinC ==> RfinC) diff_op diff_op.
Proof. param_comp diff_R. Qed.

Global Instance RfinC_card:
  refines (RfinC ==> eq) cardinal_op cardinal_op.
Proof. param_comp cardinal_R. Qed.

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

Global Instance Rtuple_card:
  refines (Rtuple ==> eq) (@cardB _) cards.
Proof.
  rewrite !refinesE => bs w <-; by rewrite /cardB.
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
  do 2 (eapply refines_trans; tc).
- rewrite refinesE; exact: erefl.
- param (full_R (Bits_R := Rtuple)).
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

Global Instance Rbitseq_diff:
  refines (Rbitseq ==> Rbitseq ==> Rbitseq) diff_op diff_op.
Proof.
  eapply refines_trans; tc.
  param_comp diff_R; rewrite refinesE; by move => x y /= -> z w /= ->.
Qed.

Global Instance Rbitseq_card:
  refines (Rbitseq ==> eq) cardinal_op cardinal_op.
Proof. param_comp cardinal_R. Qed.

(** Refinements especially involving cardinal *)

(* Strangely enough, this instance is necessary for cardinal comparison
   to work properly *)
Global Instance eqnRefine:
  refines (eq ==> eq ==> bool_R) eqtype.eq_op eqn.
Proof.
  rewrite eqnE refinesE => _ x -> _ y ->; by case: (x == y).
Qed.

Global Instance emptyCard :
  refines eq (cardinal_op empty_op) 0%N.
Proof.
  have Hempty : forall k, count id (nseq k false) = 0 by elim.
  rewrite /cardinal_op/card_S/cards/empty_op/empty_S/empty/zero_op/zero_S.
  by rewrite refinesE Hempty.
Qed.

Lemma belast_nseq_false : forall k, belast false (nseq k false) = nseq k false.
Proof.
  elim => [//= | n Hind].
  by rewrite /belast /= -/belast Hind.
Qed.

Lemma belast_nonnil {n} :
  n > 0 -> forall b, belast b (nseq n false) = b :: (nseq (n.-1) false).
Proof.
  elim: n => [// | n Hind n_gt0 b] //=; by rewrite belast_nseq_false.
Qed.

Lemma exp_offset {k} : 2 ^ k - 1 < 2 ^ k.
Proof.
  rewrite -{2}[2^k]subn0; apply: ltn_sub2l; [ exact: expn_gt0 | done ].
Qed.

Lemma exp_offset_odd {k} : k > 0 -> odd (2 ^ k - 1).
Proof.
  have lt01 : 0 < 1 by rewrite /=. move => k_gt_0.
  rewrite odd_sub /=; last by exact: expn_gt0.
  rewrite odd_exp //=. suff -> : (k == 0) = false by [].
  by rewrite eqn0Ngt k_gt_0.
Qed.

Lemma pow2_div2 {k} : (2 ^ k.+1 - 1) %/ 2 = 2 ^ k - 1.
Proof.
  have Hform : forall k, 2 * 2^k.+1 = 2^k.+1 + 2^k.+1.
  - move => k0; by rewrite addnn -muln2 mulnC expnS.
  elim: k => //= k Hind; rewrite expnS Hform -addnBA; last by exact: expn_gt0.
  have Hmul : 2^k.+1 = 2 * 2^k by rewrite expnS.
  rewrite {1}Hmul mulnC divnMDl // Hind addnBA; last by exact: expn_gt0.
  by rewrite addnn -muln2 mulnC expnS.
Qed.

Lemma subs_nseq_true {n} : subs '0_n (bitn n 1) = nseq n true.
Proof.
  rewrite bitn_one_def //=. elim: n => [// | n Hind] //=.
  rewrite belast_nseq_false -Hind {Hind} /= /subs /val /=.
  have -> : unzip1 (zip '0_n (belast true '0_n)) = '0_n.
  - by rewrite unzip1_zip //= size_belast.
  rewrite unzip1_zip // !size_belast !minnn !nats_cons.
  have nats0 : forall k, nats '0_k = 0
    by elim => [// | ? Hi]; rewrite //= nats_cons Hi.
  rewrite nats0 //= double0 addn0 !unzip2_zip //=; last by rewrite size_belast.
  rewrite nats0 double0 addn0 -/bitn_rec !add0n.
  have Hsimpl : forall m, (2 ^ m).-1.+1 = 2^m.
  - move => m; by rewrite prednK // expn_gt0 /=.
  rewrite !Hsimpl {Hsimpl} odd_mod; last by rewrite odd_exp.
  have -> : odd (2 ^ (size '0_n).+1 - 1) by exact: exp_offset_odd.
  rewrite -/bitn //=; case/boolP: (n == 0).
  - move/eqP => ->; by rewrite bitn_nil //=.
  - rewrite -lt0n => n_gt0.
    rewrite belast_nonnil // nats_cons nats_zero double0 addn0 /=.
    have -> : ((2 ^ (size '0_n).+1 - 1) %% 2 ^ (size '0_n).+1) =
      2 ^ (size '0_n).+1 - 1.
    + rewrite modn_small //; exact: exp_offset.
    have -> : (2 ^ size '0_n - 1) %% 2 ^ size '0_n = 2 ^ size '0_n - 1.
    + rewrite modn_small //; exact: exp_offset.
    rewrite [_ %% 2 ^ size '0_n]modn_small; last first.
    + rewrite bitnK; exact: exp_offset.
    rewrite [in RHS]bitnK; last by rewrite inE; exact: exp_offset.
    rewrite bitnK; last first.
    + rewrite inE -divn2 ltn_divLR //= -expnSr; exact: exp_offset.
    rewrite -divn2 -muln2 modn_small pow2_div2.
    + rewrite {1}/bitn /= muln2 uphalf_double -muln2 //=.
      rewrite odd_mul /= andbF /=. apply/eqP; by rewrite eqseq_cons /=.
    + rewrite mulnBl mul1n -expnSr.
      have Hleq1 : (2 ^ (size '0_n).+1 - 2) < (2 ^ (size '0_n).+1 - 1).
      by rewrite ltn_sub2l //= expnS_ge2.
      have Hleq2 : 1 + (2 ^ (size '0_n).+1 - 2) < 1 + (2 ^ (size '0_n).+1 - 1).
      by rewrite ltn_add2l; exact: Hleq1.
      have Heq : 1 + (2 ^ (size '0_n).+1 - 1) = 2 ^ (size '0_n).+1.
      rewrite addnC subnK //=; exact: expn_gt0.
      rewrite -[X in _ < X]Heq; exact: Hleq2.
Qed.

Global Instance fullCard :
  refines eq (cardinal_op full_op) n.
Proof.
  have Hfull : forall k, count id (nseq k true) = k.
  - by elim => [// | k /= ->]; rewrite addnC addn1.
  rewrite refinesE /full_op/full_S/full; runfold.
  rewrite /sub_S/zero_S/one_S subs_nseq_true.
  by rewrite /cardinal_op/card_S/cards Hfull.
Qed.

End Make.
