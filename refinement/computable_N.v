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
  Definition t := N.
  Definition eq   : t -> t -> bool  := N.eqb.
  Definition zero : t               := 0%N.
  Definition one  : t               := 1%N.
  Definition add  : t -> t -> t     := N.add.
  Definition sub  : t -> t -> t     := N.sub.

  (* TODO *)
  Definition opp  : t -> t          := fun _ => 0%N.
  (* TODO *)
  Definition lnot : t -> t          := fun _ => 0%N.

  (* Bit ops *)
  Definition lor  : t -> t -> t     := N.lor.
  Definition lxor : t -> t -> t     := N.lxor.
  Definition land : t -> t -> t     := N.land.
  Definition lsr  : t -> t -> t     := N.shiftr.
  Definition lsl  : t -> t -> t     := N.shiftl.

End Native.

Import Native.

Global Instance   eq_Native : eq_of   t := eq.

Global Instance zero_Native : zero_of t := zero.
Global Instance  one_Native : one_of  t := one.
Global Instance  opp_Native : opp_of  t := opp.
Global Instance  sub_Native : sub_of  t := sub.
Global Instance  add_Native : add_of  t := add.

Global Instance  not_Native : not_of  t := lnot.
Global Instance   or_Native : or_of   t := lor.
Global Instance  and_Native : and_of  t := land.
Global Instance  xor_Native : xor_of  t := lxor.
Global Instance  shl_Native : shl_of  t t := lsl.
Global Instance  shr_Native : shr_of  t t := lsr.

Section BitRepr.

Variable n : nat.
Implicit Types (s : bitseq) (b : 'B_n).

Fixpoint bitsToInt s : t :=
  (match s with
    | [::]           => 0
    | [:: false & s] =>      bitsToInt s :<<: 1
    | [:: true  & s] => 1 || (bitsToInt s :<<: 1)
  end)%C.

Fixpoint bitsFromInt (k : nat) (n : t) : bitseq :=
  (match k with
    | 0 => [::]
    | k.+1 =>
      let p := bitsFromInt k (n :>>: 1) in
      ((n && 1) == 1) :: p
  end)%C.

Lemma bitsFromIntP {k} (i: t): size (bitsFromInt k i) == k.
Proof.
  elim: k i => // [k IH] i //=; rewrite eqSS //.
Qed.

Canonical bitsFromInt_tuple (i : t): 'B_n
  := Tuple (bitsFromIntP i).

End BitRepr.

(** * Extraction  *)

(* Following CompCert's Integer module *)
Module Type WORDSIZE.
  Variable wordsize: nat.
End WORDSIZE.

Module MakeOps (WS: WORDSIZE).

Definition w := WS.wordsize.

Definition Int  := Native.t.
Definition eq   := Native.eq.
Definition zero := Native.zero.
Definition one  := Native.one.
Definition lor  := Native.lor.
Definition land := Native.land.
Definition lsr  := Native.lsr.
Definition lxor := Native.lxor.

Definition wordsize := bitsToInt (bitn 63 WS.wordsize).

Definition bitmask := ((1 :<<: wordsize) - 1: Int)%C.

Definition mask_unop  (f : Int -> Int) x := (bitmask && f x)%C.
Definition mask_binop (f : Int -> Int -> Int) x y := (bitmask && f x y)%C.

Definition lnot := mask_unop Native.lnot.
Definition opp  := mask_unop Native.opp.

Definition lsl := mask_binop Native.lsl.
Definition add := mask_binop Native.add.
Definition sub := mask_binop Native.sub.

End MakeOps.

Module Wordsize_32.
  Definition wordsize := 32.
End Wordsize_32.

Module Int32 := MakeOps(Wordsize_32).

Module Wordsize_16.
  Definition wordsize := 16.
End Wordsize_16.

Module Int16 := MakeOps(Wordsize_16).

Module Wordsize_8.
  Definition wordsize := 8.
End Wordsize_8.

Module Int8 := MakeOps(Wordsize_8).
