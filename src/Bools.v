
(** * Some lemmas about bool *)

From mathcomp Require Import ssreflect ssrbool eqtype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma and_true_l (a b : bool) : a && b = true -> a = true.
Proof. by case: a. Qed.

Lemma and_true_r (a b : bool) : a && b = true -> b = true.
Proof. by case: a. Qed.

Lemma and_true (a b : bool) : a && b = true -> a = true /\ b = true.
Proof. by case: a. Qed.

Lemma and_false (a b : bool) : a && b = false -> a = false \/ b = false.
Proof.
  case/nandP => H.
  - left; exact: (negbTE H).
  - right; exact: (negbTE H).
Qed.

Lemma neq_sym (T : eqType) (x y : T) : (x != y) = (y != x).
Proof.
  case H: (x == y) => /=.
  - rewrite eq_sym in H. rewrite H. reflexivity.
  - rewrite eq_sym in H. rewrite H. reflexivity.
Qed.

Lemma expand_eq (b1 b2 : bool) : (b1 == b2) = ((b1 || ~~ b2) && (~~ b1 || b2)).
Proof. by case: b1; case: b2. Qed.

Lemma expand_neq (b1 b2 : bool) : (b1 != b2) = ((b1 || b2) && (~~ b1 || ~~ b2)).
Proof. by case: b1; case: b2. Qed.

Lemma neg_eq (b1 b2 : bool) : (~~ b1 == ~~ b2) = (b1 == b2).
Proof. by case: b1; case: b2. Qed.
