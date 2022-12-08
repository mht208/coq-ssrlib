
From Coq Require Import List.
From mathcomp Require Import ssreflect.
From ssrlib Require Import Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Inductive nonempty_list A : Type :=
| NonemptyList : forall (hd : A) (tl : list A), nonempty_list A.

Definition nonempty_list_to_list A (l : nonempty_list A) : list A :=
  match l with
  | NonemptyList hd tl => hd::tl
  end.

Coercion nonempty_list_to_list : nonempty_list >-> list.

Definition nonempty_hd A (l : nonempty_list A) : A :=
  match l with
  | NonemptyList hd tl => hd
  end.


From Coq Require Import SetoidList.
From mathcomp Require Import eqtype ssrbool seq.

Section INA.

  Variable S : eqType.

  Lemma in_inA (x : S) (l : seq S) :
    (x \in l) -> (SetoidList.InA (fun x y => x == y) x l).
  Proof.
    elim: l x => /=.
    - move=> x Hin.
      rewrite in_nil in Hin.
      discriminate.
    - move=> hd tl IH x Hin.
      case Hx: (x == hd).
      + apply: InA_cons_hd.
        assumption.
      + rewrite in_cons Hx /= in Hin.
        apply: InA_cons_tl.
        exact: (IH _ Hin).
  Qed.

  Lemma inA_in (x : S) (l : seq S) :
    (SetoidList.InA (fun x y => x == y) x l) -> (x \in l).
  Proof.
    elim: l x => /=.
    - move=> x Hin; by inversion_clear Hin.
    - move=> hd tl IH x Hin.
      rewrite in_cons.
      inversion_clear Hin.
      + by rewrite H.
      + apply/orP; right; apply: IH.
        assumption.
  Qed.

  Lemma InAP (x : S) (l : seq S) : reflect (SetoidList.InA (fun x y => x == y) x l) (x \in l).
  Proof.
    case Hin: (x \in l).
    - apply: ReflectT.
      exact: (in_inA Hin).
    - apply: ReflectF.
      move=> HinA.
      move/negP: Hin; apply.
      exact: (inA_in HinA).
  Qed.

End INA.

Section ListLemmas.

  Variable A : Type.

  Variable B : Type.

  Lemma split_cons :
    forall (hd : A * B) (tl : list (A * B)),
      split (hd::tl) = ((fst hd)::(fst (split tl)), (snd hd)::(snd (split tl))).
  Proof.
    move=> [hd1 hd2] tl /=. dcase (split tl). move=> [ls1 ls2] Hspl /=.
    reflexivity.
  Qed.

  Lemma split_append :
    forall (ls1 ls2 : list (A * B)),
      split (ls1 ++ ls2) = ((fst (split ls1)) ++ (fst (split ls2)), (snd (split ls1)) ++ (snd (split ls2))).
  Proof.
    elim.
    - move=> ls2 /=. exact: surjective_pairing.
    - move=> [l1_hd1 l1_hd2] l1_tl IH ls2 /=. rewrite IH.
      dcase (split l1_tl). move=> [l1_tl1 l1_tl2] Hspl1. reflexivity.
  Qed.

  Lemma existsb_rcons (f : A -> bool) s x :
    existsb f (rcons s x) = existsb f s || f x.
  Proof.
    elim: s x => [| a s IH] x /=.
    - by rewrite orbF.
    - rewrite IH orbA. reflexivity.
  Qed.

  Section InA.

    Variable eqA eqB : A -> A -> Prop.

    Definition is_eq (eqA : A -> A -> Prop) : Prop :=
      forall x y, eqA x y -> x = y.

    Variable eqA_is_eq : is_eq eqA.

    Lemma InA_eqB x s :
      (forall x y, eqA x y -> eqB x y) ->
      InA eqA x s -> InA eqB x s.
    Proof.
      move=> H. elim: s x => [| a s IH] x Hin //=.
      - by inversion_clear Hin.
      - case/InA_cons : Hin => Hin.
        + left. exact: (H _ _ Hin).
        + right. exact: (IH _ Hin).
    Qed.

    Lemma InA_eq_In x (s : seq A) : InA Logic.eq x s -> In x s.
    Proof.
      elim: s x => [| a s IH] x Hin //=.
      - by inversion_clear Hin.
      - case/InA_cons : Hin => Hin.
        + rewrite Hin; by left.
        + right; exact: (IH _ Hin).
    Qed.

    Lemma InA_In x (s : seq A) : InA eqA x s -> In x s.
    Proof.
      elim: s x => [| a s IH] x Hin //=.
      - by inversion_clear Hin.
      - case/InA_cons : Hin => Hin.
        + rewrite (eqA_is_eq Hin); by left.
        + right; exact: (IH _ Hin).
    Qed.

  End InA.

End ListLemmas.
