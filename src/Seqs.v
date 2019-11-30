
From Coq Require Import OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype.
From ssrlib Require Import SsrOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section SeqLemmas.

  Variable A : Type.

  Variable default : A.

  Lemma singleton_seq (l : seq A) :
    size l = 1%N -> exists x : A, l = x :: nil.
  Proof.
    elim: l => //=.
    move=> hd tl; elim tl => //=.
    move=> _ _; exists hd.
    reflexivity.
  Qed.

  Lemma last_decomp (l : seq A) (n : nat) :
    size l = (n + 1)%N -> exists s x, l = rcons s x.
  Proof.
    move: l n. apply: last_ind => /=.
    - by case.
    - move=> l x IH n H. exists l; exists x; reflexivity.
  Qed.

  Lemma last_default_irrelevant (l : seq A) (n : nat) b1 b2 :
    size l = (n + 1)%N -> last b1 l = last b2 l.
  Proof.
    move: l n b1 b2. apply: last_ind => /=.
    - move=> n b1 b2; by case n.
    - move=> l lst IH n b1 b2 H. rewrite !last_rcons. reflexivity.
  Qed.

  Lemma nth_cons (x : A) (l : list A) (n : nat) :
    0 < n -> nth default (x::l) n = nth default l (n - 1).
  Proof. case: n => //=. move=> n _. by rewrite subn1 -pred_Sn. Qed.

  Lemma nth_tl (l : list A) (n : nat) : nth default (tl l) n = nth default l (n + 1).
  Proof.
    case: l => [| x l] //=.
    - by rewrite 2!nth_nil.
    - rewrite nth_cons; last by rewrite addn_gt0 orbT. by rewrite addn1 subn1 -pred_Sn.
  Qed.

End SeqLemmas.

Section EqSeqLemmas.

  Variable A : eqType.

  Variable B : eqType.

  Lemma singleton_eq (x y : A) : ([::x] == [::y]) = (x == y).
  Proof.
    case H: (x == y).
    - by rewrite (eqP H) eqxx.
    - apply/negP => /eqP [] Heq. by rewrite Heq eqxx in H.
  Qed.

  Lemma map_l_nil (f : A -> B) (l : seq A) :
    (map f l == [::]) = (l == [::]).
  Proof. by case: l. Qed.

  Lemma seq_neq_split (x y : A) (xs ys : seq A) :
    (x::xs != y::ys) = ((x != y) || (xs != ys)).
  Proof.
    rewrite negb_and -/eqseq. case Hxy: (x == y) => /=; by trivial.
  Qed.

  Lemma has_catrev p (l1 l2 : seq A) : has p (catrev l1 l2) = has p l1 || has p l2.
  Proof.
    elim: l1 l2 => [| hd tl IH] l2 //=. rewrite -cat1s catrev_catr has_cat IH /=.
    rewrite orbF (Bool.orb_comm (has p tl)). reflexivity.
  Qed.

  Lemma all_catrev p (l1 l2 : seq A) : all p (catrev l1 l2) = all p l1 && all p l2.
  Proof.
    elim: l1 l2 => [| hd tl IH] l2 //=. rewrite -cat1s catrev_catr all_cat IH /=.
    rewrite andbT (Bool.andb_comm (all p tl)). reflexivity.
  Qed.

End EqSeqLemmas.

Section UnzipLemmas.

  Variable A : eqType.

  Variable B : eqType.

  Lemma unzip1_l_nil (pairs : seq (A * B)) :
    (unzip1 pairs == [::]) = (pairs == [::]).
  Proof. by rewrite /unzip1 map_l_nil. Qed.

  Lemma unzip2_l_nil (pairs : seq (A * B)) :
    (unzip2 pairs == [::]) = (pairs == [::]).
  Proof. by rewrite /unzip2 map_l_nil. Qed.

End UnzipLemmas.

Section PrefixOf.

  Variable A : eqType.

  Implicit Type s : seq A.

  Fixpoint prefix_of (s1 s2 : seq A) : bool :=
    match s1 with
    | [::] => true
    | x1::s1 => match s2 with
                | [::] => false
                | x2::s2 => (x1 == x2) && (prefix_of s1 s2)
                end
    end.

  Lemma prefix_of_nil s : prefix_of nil s.
  Proof. done. Qed.

  Lemma prefix_of_is_nil s : prefix_of s nil = (s == nil).
  Proof. by case: s. Qed.

  Lemma prefix_of_take s1 s2 :
    prefix_of s1 s2 = (s1 == take (size s1) s2).
  Proof.
    elim: s1 s2 => [|x1 s1 IH1] /=.
    - by move=> ?; rewrite take0 eqxx.
    - case => //=. move=> x2 s2. rewrite eqseq_cons IH1. reflexivity.
  Qed.

  Lemma prefix_of_size s1 s2 : prefix_of s1 s2 -> size s1 <= size s2.
  Proof.
    rewrite prefix_of_take. move=> /eqP ->. rewrite size_take.
    case H: (size s1 < size s2) => //=. by apply: ltnW.
  Qed.

  Lemma prefix_of_cons x1 s1 x2 s2 :
    prefix_of (x1::s1) (x2::s2) = ((x1 == x2) && prefix_of s1 s2).
  Proof. reflexivity. Qed.

  Lemma prefix_of_rcons s1 s2 x :
    prefix_of s1 s2 -> prefix_of s1 (rcons s2 x).
  Proof.
    elim: s1 s2 x => [| hd1 tl1 IH1] [| hd2 tl2] x //=.
    move=> /andP [/eqP -> Htl]. by rewrite eqxx (IH1 _ _ Htl).
  Qed.

  Lemma prefix_of_belast x s1 s2 :
    prefix_of (x::s1) s2 -> prefix_of (belast x s1) s2.
  Proof.
    elim: s1 s2 x => [| hd1 tl1 IH1] [| hd2 [| tl2_hd tl2_tl]] x //=.
    - by rewrite andbF.
    - move=> /andP [/eqP -> /andP [/eqP -> H]]. rewrite eqxx andTb. apply: IH1.
      by rewrite prefix_of_cons eqxx H.
  Qed.

  Lemma prefix_of_refl s : prefix_of s s.
  Proof. elim: s => //=. move=> ? ? ->; by rewrite eqxx. Qed.

  Lemma prefix_of_antisym s1 s2 : (prefix_of s1 s2 && prefix_of s2 s1) = (s1 == s2).
  Proof.
    elim: s1 s2 => [| hd1 tl1 IH1] /=.
    - move=> s2. rewrite prefix_of_is_nil eq_sym. reflexivity.
    - case=> [|hd2 tl2] => //=. rewrite (andbA ((hd1 == hd2) && prefix_of tl1 tl2)).
      rewrite -(andbA (hd1 == hd2)). rewrite (andbC (prefix_of tl1 tl2)).
      rewrite andbA. rewrite (eq_sym hd2). rewrite Bool.andb_diag. rewrite -andbA.
      rewrite IH1. reflexivity.
  Qed.

  Lemma prefix_of_trans s1 s2 s3 :
    prefix_of s1 s2 -> prefix_of s2 s3 -> prefix_of s1 s3.
  Proof.
    elim: s1 s2 s3 => [| hd1 tl1 IH1] [| hd2 tl2] [| hd3 tl3] //=.
    move=> /andP [/eqP -> H12] /andP [/eqP -> H23].
      by rewrite eqxx (IH1 _ _ H12 H23).
  Qed.

  Lemma prefix_of_cons_ident x s1 s2 :
    prefix_of (x::s1) s2 -> prefix_of s1 s2 -> constant (x::s1).
  Proof.
    elim: s1 s2 x => [| hd1 tl1 IH1] [| hd2 [| tl2_hd tl2_tl]] x //=.
    - by rewrite andbF.
    - move=> /andP [/eqP <- /andP [/eqP <- H1]]. move=> /andP [/eqP -> H2].
      rewrite eqxx andTb. apply: (IH1 _ _ _ H2).
      by rewrite prefix_of_cons eqxx andTb H1.
  Qed.

  Variable default : A.

  Lemma prefix_of_nth s1 s2 i :
    prefix_of s1 s2 -> i < size s1 -> nth default s1 i = nth default s2 i.
  Proof.
    rewrite prefix_of_take. move=> /eqP Hs Hi. rewrite Hs (nth_take _ Hi).
    reflexivity.
  Qed.

End PrefixOf.

Section Fold.

  Context {A : Type} {B : Type} {R : relation B} {E : Equivalence R}.

  Context {f : B -> A -> B}.

  Context {Rf_swap : forall (a1 a2 : A) (b : B),
              R (f (f b a1) a2) (f (f b a2) a1)}.

  Context {R_foldl : forall (b1 b2 : B) (ls : seq A),
              R b1 b2 -> R (foldl f b1 ls) (foldl f b2 ls)}.

  Lemma foldl_cons (hd : A) (tl : seq A) (r : B) :
    R (foldl f r (hd::tl)) (f (foldl f r tl) hd).
  Proof.
    elim: tl hd r => /=.
    - move=> hd r. reflexivity.
    - move=> tl_hd tl_tl IH hd r. rewrite -(IH hd (f r tl_hd)).
      move: (Rf_swap tl_hd hd r) => H. rewrite (R_foldl _ H). reflexivity.
  Qed.

End Fold.

Module SeqOrderMinimal (X : SsrOrder) <: SsrOrderMinimal.
  Definition t := seq_eqType X.T.
  Definition eqn (x y : t) : bool := x == y.
  Fixpoint ltn (x y : t) : bool :=
    match x, y with
    | _, [::] => false
    | [::], hd::_ => true
    | hd1::tl1, hd2::tl2 => (X.ltn hd1 hd2) || ((hd1 == hd2) && (ltn tl1 tl2))
    end.
  Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
  Proof.
    elim: x y z.
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
  Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
  Proof.
    elim: x y.
    - case; by trivial.
    - move=> hdx tlx IHx. case; first by trivial.
      move=> hdy tly /=. rewrite seq_neq_split. case/orP.
      + move=> Hhd. move/negP: (X.lt_not_eq Hhd). by move=> ->.
      + move/andP=> [Hhd Htl]. by rewrite (IHx _ Htl) orbT.
  Qed.
  Definition compare (x y : t) : Compare ltn eqn x y.
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
End SeqOrderMinimal.

Module SeqOrder (X : SsrOrder) <: SsrOrder.
  Module Y := SeqOrderMinimal X.
  Module M := MakeSsrOrder Y.
  Include M.
End SeqOrder.
