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

Eval vm_compute in R.zero_S.

Eval vm_compute in (count id [:: true; false; true; true]).

Let p : {set 'I_4} := setU (set1 ord0) (set1 (Ordinal (erefl (1 < 4)%N))).
Let q : {set 'I_4} := set0.
Let r : {set 'I_4} := set0.
Let s : {set 'I_4} := set1 ord0.

Global Instance ord_num (m : 'I_n) :
  refines R.Rbitsq m (m).
Proof.
  rewrite /R.Rbitsq /R.Rord /R.Rord' /R.RidxI /=.
  eapply refines_trans; tc.
  - eapply refines_trans; tc.
    + rewrite refinesE. exact: erefl.
    + rewrite refinesE. rewrite enum_rank_ord /=.
      suff : @nat_of_ord R.n m = m by rewrite //=. by [].
  - rewrite refinesE /=. suff : @nat_of_ord R.n m = m by rewrite //=.
    by [].
Qed.

Set Typeclasses Debug.

Goal (set1 (Ordinal (erefl (2 < 4)%N)) :|: q) != empty_op.
Proof.
  by coqeal.
Abort.

Goal empty_op != p.
Proof.
  by coqeal.
Abort.

Goal p != q.
Proof.
  by coqeal.
Abort.

(* Strangely enough, this is needed for the cardinality comparisons
   below to work properly *)
Instance EqRefine :
  refines (eq ==> eq ==> bool_R)%rel eqtype.eq_op eqn.
Proof.
  rewrite !refinesE eqnE => x1 y1 <- x2 y2 <-; by case (x1 == x2).
Qed.

Instance fullCard :
  refines eq (cardinal_op full_op) n.
Proof.
  by rewrite refinesE.
Qed.

Instance emptyCard :
  refines eq (cardinal_op empty_op) 0.
Proof.
  by rewrite !refinesE /=.
Qed.

Goal (cardinal_op p) != (cardinal_op r).
Proof.
  by coqeal.
Abort.

Goal (cardinal_op q) == (cardinal_op r).
Proof.
  by coqeal.
Abort.

Goal full_op != p.
Proof.
  by coqeal.
Abort.

Goal (cardinal_op full_op) != (cardinal_op r).
Proof.
  by coqeal.
Abort.

Goal (cardinal_op full_op) != 2.
Proof.
  by coqeal.
Abort.

Goal cardinal_op q == 0.
Proof.
  by coqeal.
Abort.

(* This case is still problematic *)
Goal cardinal_op s == 1.
Proof.
  Fail by coqeal.
Abort.