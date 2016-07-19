(******************************************************************************)
(* A bit library for Coq: sets encoded as bitseqs.                            *)
(******************************************************************************)
(*                                                                            *)
(* (c) 2016, MINES ParisTech                                                  *)
(*                                                                            *)
(* Written by Arthur Blot                                                     *)
(*            Pierre-Evariste Dagand                                          *)
(*            Emilio J. Gallego Arias                                         *)
(*                                                                            *)
(* LICENSE: CECILL-B                                                          *)
(*                                                                            *)
(******************************************************************************)
From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From mathcomp
Require Import choice fintype finset tuple path bigop.

(******************************************************************************)
(* A bit library for Coq: sets encoded as bitseqs.                            *)
(* WARNING: This library is just a proof of concept and extremely unstable.   *)
(*                                                                            *)
(* Operations:                                                                *)
(*                                                                            *)
(*   to_set b == seq of nats representing the bits set in bitseq b            *)
(* from_set s == bitseq correponding to (s : seq nat)                         *)
(*                                                                            *)
(*     seqn s == k.-bit tuple for (s : seq 'I_k)                              *)
(*     setn S == k.-bit_tuple for (S : {set 'I_k})                            *)
(*                                                                            *)
(*     seqB B ==  seq 'I_k  corresponding to (B : k.-bit_tuple)               *)
(*     setB B == {set 'I_k} corresponding to (B : k.-bit_tuple)               *)
(*                                                                            *)
(* Future:                                                                    *)
(*                                                                            *)
(*     seqF F ==  seq 'I_k  corresponding to (B : {ffun ...}                  *)
(*     setF B == {ffun 'I_k... } corresponding to (B : k.-bit_tuple)          *)
(*                                                                            *)
(* Operations are designed to cancel in the proper way, the *_morphL family   *)
(* or lemmas provide the correspondence between set and bit operations.       *)
(*                                                                            *)
(* This file uses the following suffix conventions (FIXME):                   *)
(*                                                                            *)
(*  n - operations on nat seq/seq representation.                             *)
(*  B - operations on k.-tuple bool                                           *)
(*                                                                            *)
(******************************************************************************)

(* Import bits operations. *)
Require Import bitseq notation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope bits_scope.

Hint Resolve orbb andbb.

Section MemIota.
(* Indexes *)
Implicit Types (i j : nat).
Implicit Types (s : seq nat).

(* Auxiliary results *)
Lemma memS_mask l i m j k : size m <= k ->
  (l + i \in mask m (iota (l + j) k)) =
  (    i \in mask m (iota      j  k)).
Proof.
elim: k m i j l => [|k ihk] [|b m] i j l hs; rewrite // !mem_mask_cons.
by rewrite eqn_add2l -addnS ihk.
Qed.

Lemma mem_mask_gt i j k m : i < j -> (i \in mask m (iota j k)) = false.
Proof.
elim: k i j m => [|k ihk] i j m hij; first by rewrite mask0.
by case: m => // -[] m; rewrite mem_mask_cons ihk ?(ltn_eqF hij) ?ltnS // ltnW.
Qed.

(* Main lemma relating bitmasks with their enumerations *)
Lemma mem_mask_iota k i j m : j <= i < k -> size m <= k ->
   i \in mask m (iota j k) = m`_(i - j).
Proof.
elim: k i j m => [|k ihk] i j [|b m] /andP [hji hik] hs //.
  by rewrite nth_nil.
rewrite mem_mask_cons; case: eqP => [->|/eqP/negbTE neq_ij].
  by rewrite mem_mask_gt // subnn andbT orbF.
have hj : j < i by rewrite ltn_neqAle hji eq_sym neq_ij.
case: i hji hik {neq_ij} hj => // i hji hik hj.
rewrite (memS_mask 1) // andbF (ihk i) ?subSn //.
by rewrite ltnS in hj; rewrite hj.
Qed.
End MemIota.

(* Untyped operations, useful for computing and avoid {set _} *)
Definition to_set   m := mask m (iota 0 (size m)).
(* Definition from_set k s := foldr (fun idx bs => setb bs idx true) (nseq k false) s. *)
Definition from_set s := foldr (fun idx bs => sets bs idx true) [::] s.

(* Be a bit stringent as to be commutative *)
Lemma set_bitE bs n : sets bs n true = ors bs (sets [::] n true).
Proof.
(* XXX: clean up *)
elim: bs n => [|b bs ihb] [|n] //=; first by rewrite or0s.
  by rewrite ors_cons ors0 orbT.
by rewrite ors_cons orbF ihb /sets set_nth_nil.
Qed.

Lemma size_from_set s : size (from_set s) = \max_(n <- s) n.+1.
Proof.
by elim: s => [|n s ihs]; rewrite ?big_nil ?big_cons ?size_nseq ?size_set_nth // ihs.
Qed.

Lemma from_setE s : from_set s = \big[ors/[::]]_(n <- s) sets [::] n true.
Proof.
elim: s => [|n s ihs]; rewrite ?(big_nil, big_cons) //=.
by rewrite set_bitE ?size_from_set orsC ihs.
Qed.

Lemma eq_perm_from_set s1 s2 : perm_eq s1 s2 ->
  from_set s1 = from_set s2.
Proof. rewrite !from_setE; exact: eq_big_perm. Qed.

(* TODO: We must work up to (perm_eq uniq) for the image of to_set *)
Lemma eq_from_set s1 s2 : uniq s1 -> uniq s2 -> s1 =i s2 ->
                  from_set s1 = from_set s2.
Proof. by move=> ? ? ?; apply/eq_perm_from_set/uniq_perm_eq. Qed.

Lemma from_set_tupleP k (s : seq 'I_k) : size (ors (from_set (map val s)) '0_k) == k.
Proof.
rewrite size_liftz size_nseq size_from_set big_map.
elim/big_rec: _ => [|j n _ /eqP/maxn_idPr ihj]; first by rewrite max0n.
by apply/eqP/maxn_idPr; rewrite geq_max ltn_ord.
Qed.

Definition seqn k (s : seq 'I_k)   := Tuple (from_set_tupleP s).
Definition setn k (s : {set 'I_k}) := seqn (enum s).

Definition seqB k (m : k.-tuple bool) := mask m (enum 'I_k).
Definition setB k (m : k.-tuple bool) := [set x in seqB m].

(* Alternative *)
Definition setb' k (m : k.-tuple bool) := [set i in 'I_k | m`_i].

Lemma val_mem_seq (T : eqType) (P : pred T) (sT : subType P)
      (i : sT) (s : seq sT) : (i \in s) = (val i \in [seq val x | x <- s]).
Proof. by elim: s => //= x s ihs; rewrite !inE val_eqE ihs. Qed.

(* This is interesting (and true) but a bit cumbersome to prove *)
Lemma setb_def k (m : k.-tuple bool) : setB m = [set i in 'I_k | m`_i].
Proof.
apply/setP=> i; rewrite !inE val_mem_seq map_mask val_enum_ord.
by rewrite mem_mask_iota ?subn0 ?ltn_ord ?size_tuple.
Qed.

Lemma eq_seqn k (s1 s2 : seq 'I_k) :
  uniq s1 -> uniq s2 -> s1 =i s2 -> seqn s1 = seqn s2.
Proof.
move=> u1 u2 hi; apply/val_inj; congr ors.
apply/eq_from_set; rewrite ?(map_inj_uniq val_inj) //.
by move=> u; apply/mapP/mapP=> -[v v1 ->]; exists v; rewrite ?hi // -hi.
Qed.

Lemma seqb_uniq k (s : k.-tuple bool) : uniq (seqB s).
Proof. by rewrite mask_uniq ?enum_uniq. Qed.

Lemma mem_setb k (b : k.-tuple bool) (i : 'I_k) :
  (i \in setB b) = b`_i.
Proof.
rewrite inE val_mem_seq !map_mask val_enum_ord.
by rewrite mem_mask_iota ?subn0 ?ltn_ord ?size_tuple.
Qed.

(* XXX: Needs fixing *)
(* Lemma seqn_cons k n (s : seq 'I_k) : *)
(*   seqn (n :: s) = [tuple of setb (seqn s) n true]. *)
(* Proof. exact: val_inj. Qed. *)

Lemma nth_ors0 bs i k : (ors bs '0_k)`_i = bs`_i.
Proof. by rewrite /ors nth_liftz_idem ?gets0 ?orbF. Qed.

(* Perm_eq is not enough as we also remove the dups *)
Lemma seqnK k (x : seq 'I_k) : (seqB (seqn x)) =i x.
Proof.
move=> i; rewrite val_mem_seq map_mask val_enum_ord.
rewrite mem_mask_iota ?ltn_ord ?size_tuple ?subn0 // /seqn /= nth_ors0.
elim: x => [|x s ihs]; first by rewrite nth_nil.
rewrite inE nth_set_nth /=; case: (i == x) / boolP => [/eqP->|/negbTE heq].
  by rewrite eqxx.
by rewrite val_eqE heq ihs.
Qed.

Lemma nth_from_set s i : (nth false (from_set s)) i = (i \in s).
Proof.
elim: s => [|x s ihs]; first by rewrite nth_nil.
by rewrite nth_set_nth /= !inE; case: eqP.
Qed.

Lemma seqbK k : cancel (@seqB k) (@seqn _).
Proof.
move=> b; apply: eq_from_tnth => i.
rewrite !(tnth_nth false) /seqn /setB /= nth_ors0 nth_from_set ?ltn_ord //.
by rewrite map_mask val_enum_ord mem_mask_iota ?subn0 ?ltn_ord ?size_tuple.
Qed.

Lemma setnK k : cancel (@setn k) (@setB _).
Proof. by move=> x; apply/setP=> i; rewrite inE seqnK mem_enum. Qed.

Lemma setbK k : cancel (@setB k) (@setn _).
Proof.
move=> t; rewrite -{2}[t]seqbK; apply/eq_seqn; rewrite ?mask_uniq ?enum_uniq //.
by move => i; rewrite mem_enum inE.
Qed.

Prenex Implicits setnK setbK.

(* Example property: union *)
(* XXX: move to use {morph ...} notation *)
Lemma union_morphL k (b1 b2 : k.-tuple bool) :
  setB (orB b1 b2) = (setB b1 :|: setB b2).
Proof.
by apply/setP=> i; rewrite !mem_setb inE !mem_setb nth_liftz ?size_tuple.
Qed.

(* Example of derived property *)
Lemma union_morphR k (s1 s2 : {set 'I_k}) :
  orB (setn s1) (setn s2) = setn (s1 :|: s2).
Proof. by apply: (can_inj setbK); rewrite union_morphL !setnK. Qed.

(* Basically the same proof. *)
Lemma inter_morphL k (b1 b2 : k.-tuple bool) :
  setB (andB b1 b2) = (setB b1 :&: setB b2).
Proof.
by apply/setP=> i; rewrite !mem_setb inE !mem_setb nth_liftz ?size_tuple.
Qed.

Lemma neg_morphL k (b : k.-tuple bool) :
  setB (negB b) = ~: (setB b).
Proof.
by apply/setP=> i; rewrite !mem_setb inE !mem_setb (nth_map false) ?size_tuple.
Qed.

Lemma symdiff_morphL k (b1 b2 : k.-tuple bool) :
  setB (xorB b1 b2) = (setB b1 :\: setB b2 :|: setB b2 :\: setB b1).
Proof.
apply/setP=> i.
rewrite !mem_setb 2!inE !mem_setb inE !mem_setb nth_liftz ?size_tuple //.
case: b1`_i b2`_i=> -[] // .
Qed.

(* More properties: singleton *)
(* XXX: This should be one liner as you can see with the mismatches *)
Lemma setB1 k (n : 'I_k.+1) :
  setB [tuple of setlB [tuple of '0_k.+1] n true] = [set n].
Proof.
apply/setP=> i; rewrite mem_setb /= inE /setls size_tuple ltn_ord.
rewrite nth_set_nth /=; case: eqP => [/eqP|] heq.
  by rewrite -val_eqE heq.
by rewrite -val_eqE (gets0 k.+1); apply/esym/eqP.
Qed.

(* Operations to do *)
(* remove. *)
(* inter. *)
(* symdiff. *)
(* insert. *)
(* union. *)
(* compl. *)
(* shift. *)
(* get. *)

(* Cardinality *)
Definition cardb k (s : k.-tuple bool) := count id s.

(* ss is a partition of S then *)
(*  "cardb S = \sum(s <- ss) cardb s" *)

Arguments seqb_uniq [k s].

(* This follows directly from the library *)
Lemma cardbP k (s : k.-tuple bool) : #| setB s | = cardb s.
Proof.
by rewrite cardsE (card_uniqP seqb_uniq) size_mask // size_tuple size_enum_ord.
Qed.

(* Optimized cardinality *)
Definition bit_tmp k o := [tuple of bitn k o]. (* XXX: Emilio? *)

(* XXX: Factor out k of the recursion *)
Definition pop_table {n} (k: nat) : seq 'B_n :=
  mkseq (fun i => bit_tmp n (count_mem true (bitn k i))) (2^k).

Eval compute in (map val (@pop_table 4 2)).

Definition pop_elem {n}(k: nat)(bs: 'B_n)(i: nat): 'B_n
  := let x :=
         andB (shrB bs (i * k))
              (decB (shlB [bits of bitn n 1] k)) in
     nth '0 (pop_table k) (nats x).

Eval compute in (val (@pop_elem 3 1 [tuple true; false; true] 0)).

Fixpoint popAux {n}(k: nat) (bs: 'B_n) (i: nat): 'B_n :=
  match i with
  | 0     => '0
  | i'.+1 => addB (pop_elem k bs i') (popAux k bs i')
  end.

Definition cardinal {n} (k: nat)(bs: 'B_n): 'B_n
  := popAux k bs (n %/ k).

Eval compute in (map val (@pop_table 4 2)).

Eval compute in (val (cardinal 1 [tuple true; false])).

(* cardbP might be used in the proof here *)
Lemma cardinalP k (s : 'B_k) i (div_i: i %| k) (ltz_i: i > 0): #| setB s | = nats (cardinal k s).
Proof.
Admitted.

(* Set containing only the minimum *)
Definition keep_min {n} (bs: 'B_n): 'B_n
  := andB bs (oppB bs).

Lemma keep_min_repr:
  forall n (bs: 'B_n) x y, x \in setB bs ->
    setB (keep_min bs) = [set [arg min_(k < y in setB bs) k]].
(* XXX: maybe ripple_repr could be useful here, as neg is (inv + 1) *)
Admitted.

(* Value of the minimum (ie number of trailing zeroes) *)
Definition ntz n (k: nat) (bs: 'B_n) : 'B_n := subB (bit_tmp n n) (cardinal k (orB bs (oppB bs))).

Lemma ntz_repr k (bs : 'B_k) i (div_i : i %| k) (ltz_i : i > 0) x y : x \in setB bs ->
    ntz i bs = bit_tmp k [arg min_(k < y in setB bs) k].
Admitted.

(* Create an empty / full set *)
Definition createB {n} (b: bool): 'B_n := if b then decB B0 else B0.

Lemma create_repr n (b : bool) (n_gt0 : 0 < n) :
    setB (createB b) = if b then [set : 'I_n] else set0.
Admitted.

(* XXX: Emilio: move? *)
Definition ord_iota k m n : seq 'I_k := pmap insub (iota m n).
Definition set_iota k m n : {set 'I_k} := [set x in ord_iota k m n].

(* Initial segment (ie set containing element orders 0, ..., k) *)
(* XXX: Emilio? *)
(*
Definition initseg k i := @decB k (shlB (bito 1%R) i).

Lemma initseg_repr k i : setB (initseg k i) = set_iota k 0 i.
Admitted.
*)

(* Add a bitset with 1 bit to true to any bitset *)
Definition set_isNext_g {n} (S: {set 'I_n.+1}) y x := (y \notin S) && (y >= x).

Definition set_next_g {n} (S: {set 'I_n.+1}) x := [arg min_(y < ord0 | set_isNext_g S y x) y].

Lemma ripple_repr_1 k (bs: 'B_k.+1) (x: 'I_k.+1) f (isNext_f: set_isNext_g (setB bs) f x) :
  setB (addB (setn [set x]) bs) = (set_next_g (setB bs) x) |: [set y in (setB bs) | y < x] :|: [set y in (setB bs) | y > set_next_g (setB bs) x].
(* XXX: Arthur *)
Admitted.

(******************************************************************************)
(* Bijection to any set of cardinality n, from an idea by Arthur Blot.        *)
(******************************************************************************)
Section FinSet.

Variable T : finType.
Implicit Types (A B : {set T}).
Implicit Types (b : #|T|.-tuple bool).

(* From a finite set to tuple *)
Definition bitF A := setn [set enum_rank x | x in A].

(* From a tuple to a finite set *)
Definition finB b := [set enum_val x | x in setB b].

(* Aux Lemma to avoid using prenex implicits *)
Let can_enum D := can2_imset_pre D (@enum_valK T) (@enum_rankK _).
Let enum_can D := can2_imset_pre D (@enum_rankK T) (@enum_valK _).

Lemma preimsetK (U V : finType) (A : {set U}) (f : U -> V)
                (f_inj : injective f) :
  f @^-1: (f @: A) = A.
Proof.
apply/setP=> x; rewrite inE; apply/imsetP/idP; last by move=> x_in; exists x.
by case=> y y_in /f_inj->.
Qed.

Lemma finBK : cancel bitF finB.
Proof.
by move=> A; rewrite /finB can_enum setnK (preimsetK _ enum_rank_inj).
(* move=> A; rewrite /finB /bitF setnK -imset_comp (eq_imset _ (@enum_rankK _)). *)
(* exact: imset_id. *)
Qed.

Lemma bitFK : cancel finB bitF.
Proof.
by move=> A; rewrite /finB /bitF enum_can (preimsetK _ enum_val_inj) setbK.
(* move=> b; rewrite /finB /bitF -imset_comp (eq_imset _ (@enum_valK _)) imset_id. *)
(* exact: setbK. *)
Qed.

Definition f_repr b A := A = [set x : T | b`_(enum_rank x)].

Lemma f_repr_uniq b E : f_repr b E -> E = finB b.
Proof.
by move->; rewrite /finB can_enum; apply/setP=> ?; rewrite !inE -mem_setb inE.
Qed.

Lemma setDB (b: 'B_#| T |):
  [set enum_val x | x in ~: setB b] =  ~: [set enum_val x | x in setB b].
Proof. by apply/setP=> t; rewrite in_setC !can_enum !inE. Qed.

Lemma Fcompl_morphL (b : 'B_#|T|) :
  finB (negB b) = ~: (finB b).
Proof. by rewrite /finB neg_morphL setDB. Qed.

Lemma Funion_morphL (b1 b2 : 'B_#|T|) :
  finB (orB b1 b2) = (finB b1 :|: finB b2).
Proof. by rewrite /finB -imsetU union_morphL. Qed.

Lemma Finter_morphL (b1 b2 : 'B_#|T|) :
  finB (andB b1 b2) = (finB b1 :&: finB b2).
Proof. 
rewrite /finB inter_morphL imsetI //.
move=> x y _ _; apply: enum_val_inj.
Qed.

Lemma Fsymdiff_morphL (b1 b2 : 'B_#|T|) :
  finB (xorB b1 b2) = (finB b1 :\: finB b2 :|: finB b2 :\: finB b1).
Proof.
rewrite !setDE /finB symdiff_morphL imsetU !setDE !imsetI;
  first by rewrite !setDB.
- move=> x y _ _; apply: enum_val_inj.
- move=> x y _ _; apply: enum_val_inj.
Qed.

End FinSet.

(******************************************************************************)
(* Taken from the paper, we see indeed that there exists a unique repr which  *)
(* is the one given by setB.                                                  *)
(******************************************************************************)

Section ReprUniq.
Definition s_repr k (bs : k.-tuple bool) E :=
  E = [set x : 'I_k | bs`_x].

Lemma s_repr_uniq k (bs : k.-tuple bool) E : s_repr bs E -> E = setB bs.
Proof. by move ->; rewrite setb_def. Qed.

Lemma count_repr k (bs : k.-tuple bool) E : s_repr bs E -> count_mem true bs = #|E|.
Proof. by move -> ; rewrite -setb_def cardbP; apply: eq_count; case. Qed.
End ReprUniq.


(** * Generic set-theoretic operations *)

(**

  The following operations are defined parametrically wrt. the
  underlying implementation of bitvectors. This means that we can
  instantiate them to [BITS n] and later to, say, Int32. This also
  means that we can use domain-specific notations for defining them.

 *)

From CoqEAL Require Import hrel param refinements.

Import Refinements.Op.
Import Logical.Op.

Section Operations.

Variables (Bits : Type).

Context `{eq_of Bits}.
Context `{sub_of Bits}.
Context `{zero_of Bits}.
Context `{one_of Bits}.

Context `{not_of Bits}.
Context `{or_of Bits}.
Context `{and_of Bits}.
Context `{xor_of Bits}.
Context `{shl_of Bits}.
Context `{shr_of Bits}.

Definition get (k: Bits)(bs: Bits): bool
  := ((bs >>> k) && 1 == 1)%C.

Definition singleton (n: Bits): Bits 
  := (1 <<< n)%C.

Definition compl (n: Bits): Bits 
  := (~ n)%C.

Definition create (b: bool): Bits
  := (if b then 0 - 1 else 0)%C.

Definition inter (bs bs': Bits): Bits 
  := (bs && bs')%C.

Definition union (bs bs': Bits): Bits
  := (bs || bs')%C.

Definition min (bs: Bits): Bits
  := (bs && ~ bs)%C.

Definition insert (k bs: Bits): Bits
  := (bs || (1 <<< k))%C.

Definition remove (bs k: Bits): Bits
  := (bs && (~ (1 <<< k)))%C.

Definition symdiff (bs1 bs2: Bits): Bits
  := (bs1 ^^ bs2)%C.

Definition subset (bs1 bs2: Bits): bool
  := ((bs1 && bs2) == bs1)%C.

End Operations.

Arguments get {_}{_}{_}{_}{_} k bs.
Arguments singleton {_}{_}{_} n.
Arguments compl {_}{_} n.
Arguments create {_}{_}{_}{_} b.
Arguments inter {_}{_} bs bs'.
Arguments union {_}{_} bs bs'.
Arguments min {_}{_}{_} bs.
Arguments insert {_}{_}{_}{_} k bs.
Arguments remove {_}{_}{_}{_}{_} bs k.
Arguments symdiff {_}{_} bs1 bs2.
Arguments subset {_}{_}{_} bs1 bs2.

Parametricity get.
Parametricity singleton.
Parametricity compl.
Parametricity create.
Parametricity inter.
Parametricity union.
Parametricity min.
Parametricity insert.
Parametricity remove.
Parametricity symdiff.
Parametricity subset.

(******************************************************************************)
(* Typeclass notations                                                        *)
(******************************************************************************)

From CoqEAL
     Require Import refinements.
Require Import notation.

Import Refinements.Op.
Import Logical.Op.
Import Sets.Op.

(* For finset: *)

Section OpFin.

Variable T: finType.

Global Instance eq_fin: eq_of {set T} 
  := fun x y => x == y.

Global Instance get_fin: get_of T {set T} 
  := fun k E => k \in E.
Global Instance singleton_fin: singleton_of T {set T}
  := fun k => [set k].
Global Instance compl_fin: compl_of {set T} 
  := @setC _.
Global Instance full_fin: full_of {set T}
  := [set : T ].
Global Instance empty_fin: empty_of {set T} 
  := set0.
Global Instance set_fin: set_of T {set T} 
  := fun k E => k |: E.
Global Instance remove_fin: remove_of T {set T}
  := fun A a => A :\ a.
Global Instance inter_fin: inter_of {set T} 
  := @setI _.
Global Instance union_fin: union_of {set T} 
  := @setU _.
Global Instance symdiff_fin: symdiff_of {set T} 
  := fun E E' =>  ((E :\: E') :|: (E' :\: E)).
Global Instance subset_fin: subset_of {set T} 
  := fun E E' => E \subset E'.

End OpFin.

(* For bit vectors: *)

Section OpB.

Variable n: nat.

Global Instance get_B       : get_of 'B_n 'B_n       := get.
Global Instance singleton_B : singleton_of 'B_n 'B_n := singleton.
Global Instance compl_B     : compl_of 'B_n          := compl.
Global Instance full_B      : full_of 'B_n           := create (Bits := 'B_n) true.
Global Instance empty_B     : empty_of 'B_n          := create (Bits := 'B_n) false.
Global Instance set_B       : set_of 'B_n 'B_n       := insert.
Global Instance remove_B    : remove_of 'B_n 'B_n    := remove.
Global Instance inter_B     : inter_of 'B_n          := inter.
Global Instance union_B     : union_of 'B_n          := union.
Global Instance symdiff_B   : symdiff_of 'B_n        := symdiff.
Global Instance subset_B    : subset_of 'B_n         := subset.

End OpB.
