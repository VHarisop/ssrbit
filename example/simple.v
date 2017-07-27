From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp
Require Import choice fintype finset tuple ssralg zmodp matrix bigop mxalgebra.
From CoqEAL
Require Import hrel param refinements.

Require Import bitseq bitword notation bits_computable bitset.

Import Refinements.Op.
Import Logical.Op.
Import Sets.Op.

Let n := 4.

Definition T := [finType of 'I_n].

Module Fintype : FINTYPE with Definition T := T.
  Definition T: finType := T.
End Fintype.

Module R  := Make(Fintype).


Let p : {set 'I_4} := setU (set1 ord0) (set1 (Ordinal (erefl (1 < 4)%N))).
Let q : {set 'I_4} := set0.

(* Instance refine_ord0 : refines R.Rbits ord0 R.Native.zero.
Proof. Admitted. *)

Require Import NArith.

Global Instance ord_num (m : T) :
  refines R.Rbits m (N.of_nat ( nat_of_ord m) ).
Admitted.

Set Typeclasses Debug.

Goal p != q.
Proof.
  by coqeal.
Abort.