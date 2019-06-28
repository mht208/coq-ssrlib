
From Coq Require Import OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype.
From ssrlib Require Import SsrOrdered.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma singleton_seq A (l : seq A) :
  size l = 1%N -> exists x : A, l = x :: nil.
Proof.
  elim: l => //=.
  move=> hd tl; elim tl => //=.
  move=> _ _; exists hd.
  reflexivity.
Qed.

Lemma last_decomp A (l : seq A) (n : nat) :
  size l = (n + 1)%N -> exists s x, l = rcons s x.
Proof.
  move: l n. apply: last_ind => /=.
  - by case.
  - move=> l x IH n H. exists l; exists x; reflexivity.
Qed.

Lemma last_default_irrelevant A (l : seq A) (n : nat) b1 b2 :
  size l = (n + 1)%N -> last b1 l = last b2 l.
Proof.
  move: l n b1 b2. apply: last_ind => /=.
  - move=> n b1 b2; by case n.
  - move=> l lst IH n b1 b2 H. rewrite !last_rcons. reflexivity.
Qed.

Lemma seq_neq_split (A : eqType) (x y : A) (xs ys : seq A) :
  (x::xs != y::ys) = ((x != y) || (xs != ys)).
Proof.
  rewrite negb_and -/eqseq. case Hxy: (x == y) => /=; by trivial.
Qed.

Module SeqOrderedMinimal (X : SsrOrderedType) <: SsrOrderedTypeMinimal.
  Definition t := seq_eqType X.T.
  Definition eq (x y : t) : bool := x == y.
  Fixpoint lt (x y : t) : bool :=
    match x, y with
    | _, [::] => false
    | [::], hd::_ => true
    | hd1::tl1, hd2::tl2 => (X.ltb hd1 hd2) || ((hd1 == hd2) && (lt tl1 tl2))
    end.
  Lemma lt_trans : forall (x y z : t), lt x y -> lt y z -> lt x z.
  Proof.
    elim.
    - case; first by trivial.
      move=> hdy tly. elim; by trivial.
    - move=> hdx tlx IHx. case; first by trivial.
      move=> hdy tly. case; first by trivial.
      move=> hdz tlz /= /orP H1 /orP H2. case: H1; case: H2.
      + move=> Hyz Hxy. by rewrite (X.lt_trans Hxy Hyz).
      + move=> /andP [Hyz_hd Hyz_tl] Hxy_hd. by rewrite -(eqP Hyz_hd) Hxy_hd.
      + move=> Hyz_hd /andP [Hxy_hd Hxy_tl]. by rewrite (eqP Hxy_hd) Hyz_hd.
      + move=> /andP [Hyz_hd Hyz_tl] /andP [Hxy_hd Hxy_tl].
        by rewrite (eqP Hxy_hd) (eqP Hyz_hd) eqxx (IHx _ _ Hxy_tl Hyz_tl) orbT.
  Qed.
  Lemma lt_not_eq : forall (x y : t), lt x y -> x != y.
  Proof.
    elim.
    - case; by trivial.
    - move=> hdx tlx IHx. case; first by trivial.
      move=> hdy tly /=. rewrite seq_neq_split. case/orP.
      + move=> Hhd. move/negP: (X.lt_not_eq Hhd). by move=> ->.
      + move/andP=> [Hhd Htl]. by rewrite (IHx _ Htl) orbT.
  Qed.
  Definition compare (x y : t) : Compare lt eq x y.
    elim: x y.
    - case.
      + by apply: EQ.
      + move=> hdy tly. by apply: LT.
    - move=> hdx tlx IHx. case.
      + by apply: GT.
      + move=> hdy tly. case (X.compare hdx hdy) => Hhd.
        * apply: LT. by rewrite /= Hhd.
        * case: (IHx tly) => Htl.
          -- apply: LT. by rewrite /= Hhd Htl orbT.
          -- apply: EQ. apply/andP; rewrite -/eqseq. split; first assumption.
             rewrite /eq in Htl. apply/eqP. exact: (eqP Htl).
          -- apply: GT. by rewrite /= eq_sym Hhd Htl orbT.
        * apply: GT. by rewrite /= Hhd.
  Defined.
End SeqOrderedMinimal.

Module SeqOrdered (X : SsrOrderedType) <: SsrOrderedType.
  Module Y := SeqOrderedMinimal X.
  Module M := MakeSsrOrderedType Y.
  Include M.
End SeqOrdered.
