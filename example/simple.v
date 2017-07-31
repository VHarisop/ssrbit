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

Module Fintype : FINTYPE with Definition n := n with Definition T := T.
  Definition T := T.
  Definition n := n.
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

Instance fullCard :
  refines eq (cardinal_op full_op) n.
Proof.
  rewrite /R.card_S/cards/R.full_S/R.sub_S/R.zero_S/R.one_S.
  by rewrite refinesE.
Qed.

Instance card_num :
  refines (R.Rbitseq ==> nat_R)%rel cardinal_op cardinal_op.
Proof.
  eapply refines_trans; tc.
  rewrite refinesE => ? ? /= <-; exact: nat_Rxx.
Qed.

Instance eq_succn: refines (eq ==> eq)%rel succn succn.
Proof.
  by rewrite refinesE => x y ->.
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

Goal (cardinal_op full_op) != (cardinal_op p).
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

Goal #|p|%C == 2.
Proof.
  by coqeal.
Abort.