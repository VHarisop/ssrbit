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

Let n := 4%N.

Definition T := [finType of 'I_n].

Module Fintype : FINTYPE with Definition n := 4 with Definition T := T.
  Definition T := T.
  Definition n := 4.
  Lemma card_of_T : #|T| = n.
  Proof. by rewrite card_ord. Qed.
End Fintype.

Module R  := Make(Fintype).

Eval vm_compute in R.one_S.
Eval vm_compute in (fix Ffix (x : nat) : seq bool := match x with
                                         | 0 => [::]
                                         | x0.+1 => false :: Ffix x0
                                         end) 4%N.

Let p : {set 'I_4} := setU (set1 ord0) (set1 (Ordinal (erefl (1 < 4)%N))).
Let q : {set 'I_4} := set0.
Let r : {set 'I_4} := set0.

(* Instance refine_ord0 : refines R.Rbits ord0 R.Native.zero.
Proof. Admitted. *)

Require Import NArith.

Global Instance ord_num (m : T) :
  refines R.Rbitsq m (nat_of_ord m).
Proof.
  do 2 (eapply refines_trans; tc).
Admitted.

Set Typeclasses Debug.

Goal q == r.
Proof.
  by coqeal.
Abort.