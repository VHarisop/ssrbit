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
End FINTYPE.


Module Make (FT: FINTYPE).

Definition T := FT.T.

Module Wordsize.
  Definition wordsize := #| T |.
End Wordsize.

Module Native := MakeOps(Wordsize).

Definition n := #| T |.

(** ** From sets over a finite type to machine words: *)

Definition Rfin: {set T} -> 'B_#| T | -> Type  := fun_hrel (@finB T).
Definition Rtuple : 'B_n -> bitseq -> Type :=  fun a b => tval a = b.
Definition Rnative: bitseq -> Native.Int -> Type := fun_hrel (bitsFromInt Native.w).

Definition Rbitset: {set T} -> Native.Int -> Type := Rfin \o (Rtuple \o Rnative).

(** ** From finite type to machine words: *)

Definition Rord: T -> 'I_#| T | -> Type := fun t n => enum_rank t = n.
Definition RidxI: 'I_n -> nat -> Type := fun k n => val k = n.
CoInductive RidxN: nat -> Native.Int -> Type :=
  Ridx_spec (k: nat)(i: Native.Int)(b: bitseq) of
    Rnative b i
  & (k <= #| T |)%N
  & b = bitn #| T | k : RidxN k i.

Definition Rbits: T -> Native.Int -> Type :=
  Rord \o (RidxI \o RidxN).

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
Global Instance singleton_N : singleton_of Native.Int Native.Int := singleton.
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
Global Instance zero_S : zero_of bitseq := '0_#| T |.
Global Instance  one_S : one_of  bitseq := bitn #| T | 1.
Global Instance   or_S : or_of   bitseq := ors.
Global Instance  shl_S : shl_of  nat bitseq := shls.
Global Instance  and_S : and_of  bitseq := ands.
Global Instance  shr_S : shr_of  nat bitseq := shrs.
Global Instance  not_S : not_of  bitseq := negs.
Global Instance  xor_S : xor_of  bitseq := xors.
Global Instance  add_S : add_of  bitseq := adds.
Global Instance  sub_S : sub_of  bitseq := subs.

Global Instance get_S       : get_of nat bitseq       := get.
Global Instance singleton_S : singleton_of nat bitseq := singleton.
Global Instance compl_S     : compl_of bitseq            := compl.
Global Instance full_S      : full_of bitseq             := full (Bits := bitseq).
Global Instance empty_S     : empty_of bitseq            := empty (Bits := bitseq).
Global Instance set_S       : set_of nat bitseq       := insert.
Global Instance remove_S    : remove_of nat bitseq    := remove.
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
(** * From machine words to bit sequences                               *)
(************************************************************************)

Global Instance Rnative_eq:
  refines (Rnative ==> Rnative ==> param.bool_R)%rel (eqtype.eq_op) Native.eq.
Proof.
  rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
  suff -> : Native.eq w1 w2 = (bitsFromInt Native.w w1 == bitsFromInt Native.w w2)
    by exact: bool_Rxx.
  (* apply/eqIntP/eqP => [->//|]. *)
Admitted.

Global Instance Rnative_zero: refines Rnative '0_Native.w Native.zero.
Proof.
  rewrite refinesE.
(*  have /eqIntP -> := Tests.zero_valid.
  by rewrite /Rnative/fun_hrel Tests.bitsToIntK. *)
Admitted.

Global Instance Rnative_one: refines Rnative (bitn Native.w 1) Native.one.
Proof.
Admitted.

Global Instance Rnative_lnot:
  refines (Rnative ==> Rnative) negs ~%C.
Proof.
Admitted.

Global Instance Rnative_land:
  refines (Rnative ==> Rnative ==> Rnative) ands Native.land.
Proof.
Admitted.

Global Instance Rnative_lor:
  refines (Rnative ==> Rnative ==> Rnative) ors Native.lor.
Proof.
Admitted.

Global Instance Rnative_lxor:
  refines (Rnative ==> Rnative ==> Rnative) xors Native.lxor.
Proof.
Admitted.

Global Instance Rnative_lsr:
  refines (Rnative ==> RidxN ==> Rnative) shrs Native.lsr.
Proof.
Admitted.

Global Instance Rnative_lsl:
  refines (Rnative ==> RidxN ==> Rnative) shls Native.lsl.
Proof.
Admitted.

Global Instance Rnative_add:
  refines (Rnative ==> Rnative ==> Rnative) adds Native.add.
Proof.
Admitted.

Global Instance Rnative_sub:
  refines (Rnative ==> Rnative ==> Rnative) subs Native.sub.
Proof.
Admitted.

Global Instance Rnative_opp:
  refines (Rnative ==> Rnative) opps Native.opp.
Proof.
Admitted.

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
by rewrite (adds_relE (k := #| T |)(bv1 := bs1)(bv2 := bs2)).
Qed.

Global Instance Rtuple_sub:
  refines (Rtuple ==> Rtuple ==> Rtuple) (@subB _) subs.
Proof.
rewrite !refinesE => bs1 w1 <- bs2 w2 <-.
by rewrite (subs_relE (k := #| T |)(bv1 := bs1)(bv2 := bs2)).
Qed.

Global Instance Rtuple_opp:
  refines (Rtuple ==> Rtuple) (@oppB _) opps.
Proof.
rewrite !refinesE => bs w <- .
by rewrite (opps_relE (k := #| T |)(bv := bs)).
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
(** * Compositions                                                      *)
(************************************************************************)

Global Instance Rbitset_eq:
  refines (Rbitset ==> Rbitset ==> param.bool_R) eq_op eq_op.
Proof. by do 2 (eapply refines_trans; tc). Qed.

Global Instance Rbitset_get:
  refines (Rbits ==> Rbitset ==> param.bool_R) get_op get_op.
Proof.
  param_comp get_R; eapply refines_trans; tc.
Qed.

Global Instance Rbitset_singleton:
  refines (Rbits ==> Rbitset) singleton_op singleton_op.
Proof.
eapply refines_trans; tc.
eapply refines_trans; tc.
- param singleton_R.
- param (singleton_R (Idx_R := RidxN)(Bits_R := Rnative)).
Admitted.

Global Instance Rbitset_empty:
  refines Rbitset empty_op empty_op.
Proof.
  param_comp empty_R. eapply refines_trans; tc.
Qed.

Global Instance Rbitset_full:
  refines Rbitset full_op full_op.
Proof.
eapply refines_trans; tc.
eapply refines_trans; tc.
- by param (full_R (Bits_R := Rtuple)).
    do ?(rewrite refinesE; apply eq_bool_R).
- param (full_R (Bits_R := Rnative)).
Admitted.


Global Instance Rbitset_insert:
  refines (Rbits ==> Rbitset ==> Rbitset) set_op set_op.
Proof.
eapply refines_trans; tc.
eapply refines_trans; tc.
- param insert_R.
- param (insert_R (Idx_R := RidxN)(Bits_R := Rnative)).
Admitted.

Global Instance Rcomp_not:
  refines (Rtuple \o Rnative ==> Rtuple \o Rnative) ~%C ~%C.
Proof.
(* eapply refines_trans; tc. *)
Admitted.

Global Instance Rbitset_remove:
  refines (Rbitset ==> Rbits ==> Rbitset) remove_op remove_op.
Proof.
(*
eapply refines_trans; tc.
eapply refines_trans; tc.
- param remove_R.
- Local Opaque negs.
- param (remove_R (Idx_R := RidxN)(Bits_R := Rnative)). *)
Admitted.

Global Instance Rbitset_compl:
  refines (Rbitset ==> Rbitset) compl_op compl_op.
Proof. by eapply refines_trans; tc. Qed.

Global Instance Rbitset_union:
  refines (Rbitset ==> Rbitset ==> Rbitset) union_op union_op.
Proof. by eapply refines_trans; tc; param_comp union_R. Qed.

Global Instance Rbitset_inter:
  refines (Rbitset ==> Rbitset ==> Rbitset) inter_op inter_op.
Proof. by eapply refines_trans; tc; param_comp inter_R. Qed.

Global Instance Rbitset_symdiff:
  refines (Rbitset ==> Rbitset ==> Rbitset) symdiff_op symdiff_op.
Proof. by eapply refines_trans; tc; param_comp symdiff_R. Qed.

Global Instance Rbitset_subset:
  refines (Rbitset ==> Rbitset ==> bool_R) subset_op subset_op.
Proof.
eapply refines_trans; tc.
eapply refines_trans; tc.
- param (subset_R (Bits_R := Rtuple)).
- param (subset_R (Bits_R := Rnative)).
Qed.

End Make.
