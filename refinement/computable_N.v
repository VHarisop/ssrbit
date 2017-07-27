(******************************************************************************)
(*                                                                            *)
(* (c) 2016, ENS Lyon, LIP6, MINES ParisTech                                  *)
(* (c) 2017, INRIA / Ecole Polytechnique                                      *)
(*                                                                            *)
(* Written by Arthur Blot                                                     *)
(*            Pierre-Evariste Dagand                                          *)
(*            Emilio J. Gallego Arias                                         *)
(*                                                                            *)
(* Modified by Vasileios Charisopoulos                                        *)
(*                                                                            *)
(* LICENSE: Dual CECILL-B / Apache 2.0                                        *)
(*                                                                            *)
(******************************************************************************)


From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.

From mathcomp
Require Import tuple ssralg ssrnum zmodp.

From CoqEAL
Require Import hrel param refinements.

From ssrbit
Require Import bitseq notation.

From Coq
Require Import NArith.

Import Refinements.Op.
Import Logical.Op.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** This module should not be used directly. *)
Module Native.
  Definition Int := N.
  Definition zero : Int := 0%N.
  Definition one  : Int := 1%N.
  Definition eq   : Int -> Int -> bool  := N.eqb.
  Definition add  : Int -> Int -> Int     := N.add.
  Definition sub  : Int -> Int -> Int     := N.sub.

  (* TODO *)
  Definition opp  : Int -> Int := fun _ => 0%N.
  (* TODO *)
  Definition lnot : Int -> Int := fun _ => 0%N.

  (* Bit ops *)
  Definition lor  : Int -> Int -> Int := N.lor.
  Definition lxor : Int -> Int -> Int := N.lxor.
  Definition land : Int -> Int -> Int := N.land.
  Definition lsr  : Int -> Int -> Int := N.shiftr.
  Definition lsl  : Int -> Int -> Int := N.shiftl.

  (* Succ, pred *)
  Definition succ : Int -> Int  := N.succ.
  Definition pred : Int -> Int  := N.pred.

End Native.

Import Native.

Global Instance   eq_Native : eq_of   Int := eq.

Global Instance zero_Native : zero_of Int := zero.
Global Instance  one_Native : one_of  Int := one.
Global Instance  opp_Native : opp_of  Int := opp.
Global Instance  sub_Native : sub_of  Int := sub.
Global Instance  add_Native : add_of  Int := add.

Global Instance  not_Native : not_of  Int := lnot.
Global Instance   or_Native : or_of   Int := lor.
Global Instance  and_Native : and_of  Int := land.
Global Instance  xor_Native : xor_of  Int := lxor.
Global Instance  shl_Native : shl_of  Int Int := lsl.
Global Instance  shr_Native : shr_of  Int Int := lsr.

Section BitRepr.

Variable n : nat.
Implicit Types (s : bitseq) (b : 'B_n).

Fixpoint bitsToInt s : Int :=
  (match s with
    | [::]           => 0
    | [:: false & s] =>      bitsToInt s :<<: 1
    | [:: true  & s] => 1 || (bitsToInt s :<<: 1)
  end)%C.

Fixpoint bitsFromInt (k : nat) (n : Int) : bitseq :=
  (match k with
    | 0 => [::]
    | k.+1 =>
      let p := bitsFromInt k (n :>>: 1) in
      ((n && 1) == 1) :: p
  end)%C.

Lemma bitsFromIntP {k} (i: Int): size (bitsFromInt k i) == k.
Proof.
  elim: k i => // [k IH] i //=; rewrite eqSS //.
Qed.

Canonical bitsFromInt_tuple (i : Int): 'B_n
  := Tuple (bitsFromIntP i).

End BitRepr.

(** * Extraction  *)

(* Following CompCert's Integer module *)
Module Type WORDSIZE.
  Variable wordsize: nat.
End WORDSIZE.

Module MakeOps (WS: WORDSIZE).

Definition w := WS.wordsize.

Definition Int  := Native.Int.
Definition eq   := Native.eq.
Definition zero := Native.zero.
Definition one  := Native.one.
Definition lor  := Native.lor.
Definition land := Native.land.
Definition lsr  := Native.lsr.
Definition lxor := Native.lxor.

Definition succ := Native.succ.
Definition pred := Native.pred.

(* Definition wordsize := bitsToInt (bitn 63 WS.wordsize).

Definition bitmask := ((1 :<<: wordsize) - 1: Int)%C.

Definition mask_unop  (f : Int -> Int) x := (bitmask && f x)%C.
Definition mask_binop (f : Int -> Int -> Int) x y := (bitmask && f x y)%C. *)

Definition lnot := Native.lnot.
Definition opp  := Native.opp.

Definition lsl := Native.lsl.
Definition add := Native.add.
Definition sub := Native.sub.

End MakeOps.