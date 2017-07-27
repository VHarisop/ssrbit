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

Let n := 100%N.

Definition T := [finType of 'I_n].

Module Fintype : FINTYPE with Definition T := T.
  Definition T: finType := T.
End Fintype.

Module R  := Make(Fintype).

Lemma foo_lemma : #|T| = n.
Admitted.
  
Ltac foo := erewrite foo_lemma; vm_compute. 

Definition RTton := 'B_#|T| -> 'B_n -> Type :=  fun a b => tval a = b.

Global Instance Rfoo :
  refines Rfin full_op full_op.

Goal R.zero_S = [:: false; false; false; false].
  cbv.
  rewrite foo_lemma.

  foo.
  
Eval foo in R.zero_S.
Eval vm_compute in (fix Ffix (x : nat) : seq bool := match x with
                                         | 0 => [::]
                                         | x0.+1 => false :: Ffix x0
                                         end) 4%N.

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