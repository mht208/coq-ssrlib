
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq fintype tuple.

Lemma mapCons {n A B} (f: A -> B) b (p: n.-tuple A) :
  map_tuple f [tuple of b :: p] = [tuple of f b :: map_tuple f p].
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth (f b)). Qed.

Lemma mapNil {A B} (f:A -> B) :
  map_tuple f [tuple] = [tuple].
Proof. exact: val_inj. Qed.

Lemma theadCons : forall {n A} (a:A) (aa: n.-tuple A), thead [tuple of a::aa] = a.
Proof. done. Qed.

Lemma beheadCons {n A} a (aa: n.-tuple A) : behead_tuple [tuple of a::aa] = aa.
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth a). Qed.

Lemma zipCons {n A B} a (aa: n.-tuple A) b (bb: n.-tuple B) :
  zip_tuple [tuple of a::aa] [tuple of b::bb] = [tuple of (a,b) :: zip_tuple aa bb].
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth (a,b)). Qed.

Lemma nseqCons {n A} (a:A) : nseq_tuple (S n) a = [tuple of a::nseq_tuple n a].
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth a). Qed.

Lemma catCons {n1 n2 A} (a:A) (aa:n1.-tuple A) (bb:n2.-tuple A) :
  cat_tuple [tuple of a::aa] bb = [tuple of a::cat_tuple aa bb].
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth a). Qed.

Lemma catNil {n A} (aa:n.-tuple A) :
  cat_tuple [tuple] aa = aa.
Proof. exact: val_inj. Qed.

Lemma mapId T n (t: n.-tuple T) : map_tuple id t = t.
Proof.
  induction n.
  + by rewrite (tuple0 t) mapNil.
  + case : t / tupleP => h t.
    by rewrite mapCons IHn.
Qed.

Hint Rewrite @mapCons @mapNil @theadCons @ beheadCons @zipCons @nseqCons @catCons @catNil @mapId : tuple.

Lemma behead_nseq {n A} (a:A) : behead_tuple (nseq_tuple n.+1 a) = nseq_tuple n a.
Proof. by apply: eq_from_tnth=> i; rewrite !(tnth_nth a). Qed.

Lemma splitTuple {X n} {a b:X} {c d:n.-tuple X} : cons_tuple a c = cons_tuple b d -> a = b /\ c = d.
Proof. move => H. split. by inversion H. apply val_inj. by inversion H. Qed.

(* The last n elements *)
Fixpoint lastn {T} n {n2} : (n2+n).-tuple T -> n.-tuple T :=
  if n2 is _.+1 return (n2+n).-tuple T -> n.-tuple T
  then fun p => lastn _ (behead_tuple p) else fun p => p.

(* The first n elements *)
Fixpoint firstn {T} {n1} n : (n+n1).-tuple T -> n.-tuple T :=
  if n is _.+1 return (n+n1).-tuple T -> n.-tuple T
  then fun p => cons_tuple (thead p) (firstn _ (behead_tuple p)) else fun p => nil_tuple _.

Lemma cons_tuple_neq_case :
  forall {w} {A : eqType} (hd1 : A) (tl1 : w.-tuple A) hd2 tl2,
    (cons_tuple hd1 tl1 != cons_tuple hd2 tl2) = (hd1 != hd2) || (tl1 != tl2).
Proof.
  move=> w A hd1 tl1 hd2 tl2. case H: ((hd1 != hd2) || (tl1 != tl2)).
  - case/orP: H.
    + move/negP=> Hhd. apply/negP => Hcons. apply: Hhd.
      move: (splitTuple (eqP Hcons)). move=> [-> _]. exact: eqxx.
    + move/negP=> Htl. apply/negP => Hcons. apply: Htl.
      move: (splitTuple (eqP Hcons)). move=> [_ ->]. exact: eqxx.
  - apply/eqP. move: H. case Hhd: (hd1 == hd2) => /=; last by discriminate.
    case Htl: (tl1 == tl2) => /=; last by discriminate.
    by rewrite (eqP Hhd) (eqP Htl).
Qed.

Lemma ite_cons :
  forall {A w} (bc : bool) hd1 (tl1 : w.-tuple A) hd2 (tl2 : w.-tuple A),
  (if bc then cons_tuple hd1 tl1 else cons_tuple hd2 tl2) =
  cons_tuple (if bc then hd1 else hd2) (if bc then tl1 else tl2).
Proof.
  move=> A w bc hd1 tl1 hd2 tl2. by case bc.
Qed.

Lemma tval_eq :
  forall {A w} {t1 t2 : w.-tuple A}, tval t1 = tval t2 -> t1 = t2.
Proof.
  move=> A w t1 t2 H. apply: val_inj. exact: H.
Qed.
