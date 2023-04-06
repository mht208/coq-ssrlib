
(** * Extra lemmas for list *)

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

    Context `{HeqA: Equivalence A eqA}.

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

    Lemma InA_eq_In x (s : seq A) : InA Logic.eq x s <-> In x s.
    Proof.
      elim: s x => [| a s IH] x; split; move=> Hin //=.
      - by inversion_clear Hin.
      - case/InA_cons : Hin => Hin.
        + rewrite Hin; by left.
        + right. apply/IH. assumption.
      - case: (in_inv Hin) => {}Hin.
        + subst. left. reflexivity.
        + right. apply/IH. assumption.
    Qed.

    Lemma InA_In x (s : seq A) : InA eqA x s <-> In x s.
    Proof.
      elim: s x => [| a s IH] x; split; move=> Hin //=.
      - by inversion_clear Hin.
      - case/InA_cons : Hin => Hin.
        + rewrite (eqA_is_eq Hin); by left.
        + right. apply/IH. assumption.
      - case: (in_inv Hin) => {}Hin.
        + subst. left. reflexivity.
        + right. apply/IH. assumption.
    Qed.

  End InA.

  Lemma List_rev_rev (s : seq A) : List.rev s = rev s.
  Proof. elim: s => [| x s IH] //=. rewrite rev_cons -cats1. by rewrite IH. Qed.

  Lemma List_rev_rcons (s : seq A) (a : A) :
    List.rev (rcons s a) = a::(List.rev s).
  Proof.
    elim: s a => [| x s IH] a //=. rewrite IH.
    rewrite -cat_cons. reflexivity.
  Qed.

  Lemma List_rev_cat (s1 s2 : seq A) :
    List.rev (s1 ++ s2) = List.rev s2 ++ List.rev s1.
  Proof.
    elim: s1 s2 => [| x1 s1 IH1] s2 //=.
    - rewrite cats0. reflexivity.
    - rewrite IH1. rewrite catA. reflexivity.
  Qed.

  Lemma Exists_rcons (P : A -> Prop) (s : seq A) (a : A) :
    Exists P (rcons s a) <-> Exists P s \/ P a.
  Proof.
    elim: s => [| x s IH] //=.
    - split => H.
      + by case/Exists_cons: H => H; tauto.
      + case: H => H.
        * by inversion H.
        * exact: Exists_cons_hd.
    - move: IH => [IH1 IH2]. split => H.
      + case/Exists_cons: H => H.
        * left; exact: Exists_cons_hd.
        * case: (IH1 H) => {}H.
          -- left; exact: Exists_cons_tl.
          -- by right.
      + have H': P x \/ Exists P s \/ P a.
        { case: H; [ move=> H | tauto ]. move/Exists_cons: H => {}H; by tauto. }
        case: H' => H'.
        * exact: Exists_cons_hd.
        * apply: Exists_cons_tl. exact: IH2.
  Qed.

  Lemma Forall_rcons_iff (P : A -> Prop) (s : seq A) (a : A) :
    Forall P (rcons s a) <-> Forall P s /\ P a.
  Proof.
    elim: s => [| x s IH] //=.
    - split => H.
      + move/Forall_cons_iff: H => [H1 H2]; tauto.
      + apply: Forall_cons; tauto.
    - move: IH => [IH1 IH2]. split => H.
      + move/Forall_cons_iff: H => [H1 H2].
        split; [ apply: Forall_cons |]; tauto.
      + move: H => [H1 H2]. move/Forall_cons_iff: H1 => [H1 H3].
        apply: Forall_cons; tauto.
  Qed.

  Lemma Forall_rcons (P : A -> Prop) (s : seq A) (a : A) :
    Forall P s -> P a -> Forall P (rcons s a).
  Proof. move=> ? ?; apply/Forall_rcons_iff; done. Qed.

  Lemma Forall_rcons_hd (P : A -> Prop) (s : seq A) (a : A) :
    Forall P (rcons s a) -> Forall P s.
  Proof. by move/Forall_rcons_iff => [H1 H2]. Qed.

  Lemma Forall_rcons_tl (P : A -> Prop) (s : seq A) (a : A) :
    Forall P (rcons s a) -> P a.
  Proof. by move/Forall_rcons_iff => [H1 H2]. Qed.

  Lemma Exists_cat (P : A -> Prop) (s1 s2 : seq A) :
    Exists P (s1 ++ s2) <-> Exists P s1 \/ Exists P s2.
  Proof.
    elim: s1 s2 => [| x1 s1 IH1] s2 //=.
    - split => H; first tauto. case: H; last tauto. by inversion 1.
    - split => H.
      + case/Exists_cons: H => H.
        * by left; apply: Exists_cons_hd.
        * case/(IH1 _): H => H.
          -- by left; apply: Exists_cons_tl.
          -- by right.
      + have H': P x1 \/ Exists P s1 \/ Exists P s2.
        { case: H; [ move=> H | tauto ]. move/Exists_cons: H => {}H; by tauto. }
        case: H' => H'.
        * by apply: Exists_cons_hd.
        * apply: Exists_cons_tl. apply/IH1. assumption.
  Qed.

  Lemma Forall_cat_iff (P : A -> Prop) (s1 s2 : seq A) :
    Forall P (s1 ++ s2) <-> Forall P s1 /\ Forall P s2.
  Proof. exact: Forall_app. Qed.

  Lemma Forall_cat_l (P : A -> Prop) (s1 s2 : seq A) :
    Forall P (s1 ++ s2) -> Forall P s1.
  Proof. by move/Forall_cat_iff => [H1 H2]. Qed.

  Lemma Forall_cat_r (P : A -> Prop) (s1 s2 : seq A) :
    Forall P (s1 ++ s2) -> Forall P s2.
  Proof. by move/Forall_cat_iff => [H1 H2]. Qed.

  Lemma Forall_cat (P : A -> Prop) (s1 s2 : seq A) :
    Forall P s1 -> Forall P s2 -> Forall P (s1 ++ s2).
  Proof. by move=> H1 H2; apply/Forall_cat_iff. Qed.

  Lemma Exists_rev (P : A -> Prop) (s : seq A) :
    List.Exists P (rev s) <-> List.Exists P s.
  Proof.
    elim: s => [| x s IH] //=. move: IH => [IH1 IH2].
    rewrite rev_cons. split.
    - move/Exists_rcons => [] H.
      + apply: Exists_cons_tl. exact: IH1.
      + apply: Exists_cons_hd; assumption.
    - move=> H. apply/Exists_rcons. case/Exists_cons: H => H.
      + by right.
      + by left; apply: IH2.
  Qed.

  Lemma Forall_rev (P : A -> Prop) (s : seq A) :
    List.Forall P (rev s) <-> List.Forall P s.
  Proof.
    split => H.
    - move: (Forall_rev H). rewrite List_rev_rev revK. by apply.
    - move: (Forall_rev H). rewrite List_rev_rev. by apply.
  Qed.


  Section InA.

    Variable eqA : A -> A -> Prop.
    Variable eqB : B -> B -> Prop.

    Context `{HeqA: Equivalence A eqA}.
    Context `{HeqB: Equivalence B eqB}.

    Lemma inA_map f s x :
      InA eqB x (map f s) -> exists y, InA eqA y s /\ eqB x (f y).
    Proof.
      elim: s => [| a s IH] //=.
      - move=> H. by inversion_clear H.
      - inversion_clear 1.
        + exists a. split.
          * apply: InA_cons_hd. reflexivity.
          * assumption.
        + move: (IH H0) => [y [Hin Heq]]. exists y. split.
          * apply: InA_cons_tl. assumption.
          * assumption.
    Qed.

    Lemma map_inA f s x :
      Proper (eqA ==> eqB) f ->
      InA eqA x s -> InA eqB (f x) (map f s).
    Proof.
      move=> Hs. elim: s => [| a s IH] //=.
      - by inversion 1.
      - inversion_clear 1.
        + apply: InA_cons_hd. exact: (Hs _ _ H0).
        + apply: InA_cons_tl. exact: (IH H0).
    Qed.

  End InA.

  Section Equivlist.

    Variable eqA : A -> A -> Prop.
    Variable eqB : B -> B -> Prop.

    Context `{HeqA: Equivalence A eqA}.
    Context `{HeqB: Equivalence B eqB}.

    Lemma map_equivlistA (s1 s2 : seq A) (f : A -> B) :
      Proper (eqA ==> eqB) f ->
      equivlistA eqA s1 s2 -> equivlistA eqB (map f s1) (map f s2).
    Proof.
      move=> Hf Heq x; split; move=> H.
      - move: (@inA_map eqA eqB HeqA f s1 x H) => [y [Hin Heqx]].
        symmetry in Heqx. apply: (InA_eqA HeqB Heqx). apply: map_inA.
        apply/(Heq y). assumption.
      - move: (@inA_map eqA eqB HeqA f s2 x H) => [y [Hin Heqx]].
        symmetry in Heqx. apply: (InA_eqA HeqB Heqx). apply: map_inA.
        apply/(Heq y). assumption.
    Qed.

    Lemma map2_equivlistA (s1 s2 : seq A) (f : A -> B) (g : A -> B) :
      Proper (eqA ==> eqB) f ->
      Proper (eqA ==> eqB) g ->
      (forall x : A, eqB (f x) (g x)) ->
      equivlistA eqA s1 s2 -> equivlistA eqB (map f s1) (map g s2).
    Proof.
      move=> Hf Hg Hfg Heq x; split; move=> H.
      - move: (@inA_map eqA eqB HeqA f s1 x H) => [y [Hin Heqx]].
        symmetry in Heqx. rewrite (Hfg y) in Heqx.
        apply: (InA_eqA HeqB Heqx). apply: map_inA.
        apply/(Heq y). assumption.
      - move: (@inA_map eqA eqB HeqA g s2 x H) => [y [Hin Heqx]].
        symmetry in Heqx. rewrite -(Hfg y) in Heqx.
        apply: (InA_eqA HeqB Heqx). apply: map_inA.
        apply/(Heq y). assumption.
    Qed.

    Lemma equivlistA_inclA_iff (s1 s2 : seq A) :
      equivlistA eqA s1 s2 <-> inclA eqA s1 s2 /\ inclA eqA s2 s1.
    Proof.
      elim: s1 s2 => [| x1 s1 IH1] s2 //=.
      - split.
        + move=> Heq; split.
          * move=> x. by inversion 1.
          * move=> x Hin. apply/Heq. assumption.
        + move=> [H1 H2] x. by intuition.
      - split.
        + move=> Heq. split.
          * move=> x Hin1. apply/Heq. assumption.
          * move=> x Hin2. apply/Heq. assumption.
        + move=> [H1 H2]. move=> x; split.
          * move=> Hin1. apply: H1. assumption.
          * move=> Hin2. apply: H2. assumption.
    Qed.

    Lemma inclA_equivlistA (s1 s2 : seq A) :
      inclA eqA s1 s2 -> inclA eqA s2 s1 ->
      equivlistA eqA s1 s2.
    Proof. move=> H1 H2. apply/equivlistA_inclA_iff. tauto. Qed.

  End Equivlist.

End ListLemmas.
