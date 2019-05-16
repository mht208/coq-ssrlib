
From mathcomp Require Import ssreflect ssrbool eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma and_true_l :
  forall a b : bool, a && b = true -> a = true.
Proof.
  move=>a; by elim: a.
Qed.

Lemma and_true_r :
  forall a b : bool, a && b = true -> b = true.
Proof.
  move=>a; by elim: a.
Qed.

Lemma and_true :
  forall a b : bool, a && b = true -> a = true /\ b = true.
Proof.
  move=>a; by elim: a.
Qed.

Lemma and_false :
  forall a b : bool, a && b = false -> a = false \/ b = false.
Proof.
  move=> a b /nandP H.
  case: H => H.
  - left; exact: (negbTE H).
  - right; exact: (negbTE H).
Qed.

Lemma neq_sym : forall (T : eqType) (x y : T), (x != y) = (y != x).
Proof.
  move=> T x y. case H: (x == y) => /=.
  - rewrite eq_sym in H. rewrite H. reflexivity.
  - rewrite eq_sym in H. rewrite H. reflexivity.
Qed.

Lemma expand_eq :
  forall (b1 b2 : bool), (b1 == b2) = ((b1 || ~~ b2) && (~~ b1 || b2)).
Proof.
  move=> b1 b2. by case: b1; case: b2.
Qed.

Lemma expand_neq :
  forall (b1 b2 : bool), (b1 != b2) = ((b1 || b2) && (~~ b1 || ~~ b2)).
Proof.
  move=> b1 b2. by case: b1; case: b2.
Qed.
