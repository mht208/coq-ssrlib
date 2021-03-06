
(** * Some auxiliary lemmas for FSets. *)

From Coq Require Import FSets OrderedType.
From mathcomp Require Import ssreflect ssrbool eqtype seq.
From ssrlib Require Import SsrOrder Lists Seqs.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* Finite sets of elements with decidable equality. *)

Module Type SsrFSet <: FSetInterface.S.
  Declare Module SE : SsrOrder.
  Module E : OrderedType.OrderedType
      with Definition t := SE.t
      with Definition eq := SE.eq
      with Definition lt := SE.lt
      with Definition eq_refl := SE.eq_refl
      with Definition eq_sym := SE.eq_sym
      with Definition eq_trans := SE.eq_trans
      with Definition lt_trans := SE.lt_trans
      with Definition lt_not_eq := SE.lt_not_eq
      with Definition compare := SE.compare
      with Definition eq_dec := SE.eq_dec
    := SE.
  Include Sfun E.
End SsrFSet.



(* Extra lemmas for Coq finite sets *)

Module FSetLemmas (S : FSetInterface.S).

  Module F := Facts S.
  Module OP := OrdProperties S.
  Include F.
  Include OP.

  Lemma eqb_eq x y : eqb x y -> S.E.eq x y.
  Proof.
    rewrite /eqb. by case: (S.E.eq_dec x y).
  Qed.

  Lemma eq_eqb x y : S.E.eq x y -> eqb x y.
  Proof.
    rewrite /eqb. by case: (S.E.eq_dec x y).
  Qed.

  Lemma memP x (s : S.t) : reflect (S.In x s) (S.mem x s).
  Proof.
    case H: (S.mem x s).
    - apply: ReflectT.
      exact: (S.mem_2 H).
    - apply: ReflectF.
      move=> Hin; move: (S.mem_1 Hin).
      rewrite H; discriminate.
  Qed.

  Lemma mem_singleton1 :
    forall x y,
      S.mem x (S.singleton y) -> S.E.eq x y.
  Proof.
    move=> x y /memP Hin.
    move: (S.singleton_1 Hin) => Heq.
    exact: (S.E.eq_sym Heq).
  Qed.

  Lemma mem_singleton2 :
    forall x y,
      S.E.eq x y -> S.mem x (S.singleton y).
  Proof.
    move=> x y Heq.
    apply/memP.
    move: (S.E.eq_sym Heq) => {Heq} Heq.
    exact: (S.singleton_2 Heq).
  Qed.

  Lemma not_mem_singleton1 :
    forall x y,
      ~~ S.mem x (S.singleton y) ->
      ~ S.E.eq x y.
  Proof.
    move=> x y /negP Hmem.
    move=> Heq; apply: Hmem.
    apply/memP.
    move: (S.E.eq_sym Heq) => {Heq} Heq.
    exact: (S.singleton_2 Heq).
  Qed.

  Lemma not_mem_singleton2 :
    forall x y,
      ~ S.E.eq x y ->
      ~~ S.mem x (S.singleton y).
  Proof.
    move=> x y Heq.
    apply/negP => Hmem; apply: Heq.
    exact: mem_singleton1.
  Qed.

  Lemma mem_add1 :
    forall x y s,
      S.mem x (S.add y s) ->
      S.E.eq x y \/ S.mem x s.
  Proof.
    move=> x y s /memP Hin.
    move: (F.add_iff s y x) => [H _].
    move: (H Hin); case => {Hin H}.
    - move=> Heq; left.
      exact: S.E.eq_sym.
    - move=> Hin; right.
      apply/memP; assumption.
  Qed.

  Lemma mem_add2 :
    forall x y s,
      S.E.eq x y ->
      S.mem x (S.add y s).
  Proof.
    move=> x y s H; apply/memP.
    move: (S.E.eq_sym H) => {H} H.
    exact: (S.add_1 _ H).
  Qed.

  Lemma mem_add3 :
    forall x y s,
      S.mem x s ->
      S.mem x (S.add y s).
  Proof.
    move=> x y s H; apply/memP.
    move/memP: H => H.
    exact: (S.add_2 _ H).
  Qed.

  Lemma mem_add_eq {x y s} : S.E.eq x y -> S.mem x (S.add y s).
  Proof.
    move=> Heq. apply: S.mem_1. apply: S.add_1. apply: S.E.eq_sym. assumption.
  Qed.

  Lemma mem_add_neq {x y s} : ~ (S.E.eq x y) -> S.mem x (S.add y s) = S.mem x s.
  Proof.
    move=> Hne. apply: add_neq_b. move=> Heq. apply: Hne. apply: S.E.eq_sym.
    assumption.
  Qed.

  Lemma not_mem_add1 :
    forall x y s,
      ~~ S.mem x (S.add y s) ->
      ~ S.E.eq x y /\ ~~ S.mem x s.
  Proof.
    move=> x y s /negP Hmem; split.
    - move=> Heq; apply: Hmem.
      exact: mem_add2.
    - apply/negP => H; apply: Hmem.
      exact: mem_add3.
  Qed.

  Lemma not_mem_add2 :
    forall x y s,
      ~ S.E.eq x y /\ ~~ S.mem x s ->
      ~~ S.mem x (S.add y s).
  Proof.
    move=> x y s [] Heq /negP Hmem.
    apply/negP => H; apply: Hmem.
    rewrite -(mem_add_neq Heq).
    assumption.
  Qed.

  Lemma mem_union v s1 s2 : S.mem v (S.union s1 s2) = S.mem v s1 || S.mem v s2.
  Proof.
    case H1: (S.mem v s1).
    - move/memP: H1 => H1. move: (S.union_2 s2 H1) => /memP ->. reflexivity.
    - case H2: (S.mem v s2) => /=.
      + move/memP: H2 => H2. move: (S.union_3 s1 H2) => /memP ->. reflexivity.
      + apply/negP => /memP H12. move: (S.union_1 H12).
        case; move=> /memP H; [by rewrite H1 in H | by rewrite H2 in H].
  Qed.

  Lemma mem_union1 v s1 s2 : S.mem v (S.union s1 s2) -> S.mem v s1 \/ S.mem v s2.
  Proof. rewrite mem_union. by move/orP. Qed.

  Lemma mem_union2 v s1 s2 : S.mem v s1 -> S.mem v (S.union s1 s2).
  Proof. by rewrite mem_union; move=> ->. Qed.

  Lemma mem_union3 v s1 s2 : S.mem v s2 -> S.mem v (S.union s1 s2).
  Proof. by rewrite mem_union; move=> ->; rewrite orbT. Qed.

  Lemma not_mem_union1 :
    forall v s1 s2,
      ~~ S.mem v (S.union s1 s2) ->
      ~~ S.mem v s1 /\ ~~ S.mem v s2.
  Proof.
    move=> v s1 s2 /negP H; split; apply/negP => Hmem; apply: H.
    - exact: (mem_union2 _ Hmem).
    - exact: (mem_union3 _ Hmem).
  Qed.

  Lemma not_mem_union2 :
    forall v s1 s2,
      ~~ S.mem v s1 -> ~~ S.mem v s2 ->
      ~~ S.mem v (S.union s1 s2).
  Proof.
    move=> v s1 s2 /negP H1 /negP H2; apply/negP => Hmem.
    case: (mem_union1 Hmem) => H3.
    - apply: H1; assumption.
    - apply: H2; assumption.
  Qed.

  Lemma mem_subset :
    forall v s1 s2,
      S.mem v s1 ->
      S.subset s1 s2 ->
      S.mem v s2.
  Proof.
    move=> v s1 s2 /memP Hin Hsub; apply/memP.
    move: (S.subset_2 Hsub) => {Hsub} Hsub.
    exact: (Hsub _ Hin).
  Qed.

  Lemma not_mem_subset v s1 s2 :
    ~~ S.mem v s2 -> S.subset s1 s2 -> ~~ S.mem v s1.
  Proof.
    move=> Hmem2 Hsub. apply/negP=> Hmem1. move/negP: Hmem2; apply.
    exact: (mem_subset Hmem1 Hsub).
  Qed.

  Lemma mem_equal v s1 s2 : S.mem v s1 -> S.Equal s1 s2 -> S.mem v s2.
  Proof. move/memP=> Hin Heq. move: (Heq v) => H. apply/memP. tauto. Qed.

  Lemma add_equal x s : S.mem x s -> S.Equal (S.add x s) s.
  Proof.
    move/memP=> Hin. exact: (OP.P.add_equal Hin).
  Qed.

  Lemma union_emptyl s : S.Equal (S.union S.empty s) s.
  Proof.
    move=> v; split => Hin.
    - case: (S.union_1 Hin) => {Hin} Hin.
      + apply: False_ind. apply: S.empty_1. exact: Hin.
      + assumption.
    - apply: S.union_3. assumption.
  Qed.

  Lemma union_emptyr s : S.Equal (S.union s S.empty) s.
  Proof. rewrite OP.P.union_sym. exact: union_emptyl. Qed.

  Lemma union_add1 x s1 s2 :
    S.Equal (S.union (S.add x s1) s2) (S.add x (S.union s1 s2)).
  Proof.
    exact: OP.P.union_add.
  Qed.

  Lemma union_add2 x s1 s2 :
    S.Equal (S.union s1 (S.add x s2)) (S.add x (S.union s1 s2)).
  Proof.
    rewrite (OP.P.union_sym s1 (S.add _ _)) (OP.P.union_sym s1 s2).
    exact: union_add1.
  Qed.

  Lemma add_union_singleton1 x s : S.Equal (S.add x s) (S.union (S.singleton x) s).
  Proof.
    exact: OP.P.add_union_singleton.
  Qed.

  Lemma add_union_singleton2 x s : S.Equal (S.add x s) (S.union s (S.singleton x)).
  Proof.
    rewrite OP.P.union_sym. exact: OP.P.add_union_singleton.
  Qed.

  Lemma union_subsets sa1 sa2 sb1 sb2 :
    S.subset sa1 sb1 ->
    S.subset sa2 sb2 ->
    S.subset (S.union sa1 sa2) (S.union sb1 sb2).
  Proof.
    move=> Hsub1 Hsub2.
    apply/S.subset_1 => x /memP Hmemx.
    apply/memP.
    move: (mem_union1 Hmemx) => {Hmemx} [] Hmemx.
    - apply: mem_union2.
      exact: (mem_subset Hmemx Hsub1).
    - apply: mem_union3.
      exact: (mem_subset Hmemx Hsub2).
  Qed.

  Lemma union_subset_equal s1 s2 :
    S.subset s1 s2 ->
    S.Equal (S.union s1 s2) s2.
  Proof.
    move=> /S.subset_2 Hsub.
    exact: (OP.P.union_subset_equal Hsub).
  Qed.

  Lemma union_subset_1 s1 s2 : S.subset s1 (S.union s1 s2).
  Proof.
    apply/S.subset_1.
    exact: OP.P.union_subset_1.
  Qed.

  Lemma union_subset_2 s1 s2 : S.subset s1 (S.union s2 s1).
  Proof.
    apply/S.subset_1.
    exact: OP.P.union_subset_2.
  Qed.

  Lemma subset_empty s :
    S.subset S.empty s.
  Proof.
    apply/S.subset_1.
    exact: OP.P.subset_empty.
  Qed.

  Lemma subset_singleton1 x s :
    S.subset (S.singleton x) s ->
    S.mem x s.
  Proof.
    move=> H.
    apply/memP.
    move: (S.subset_2 H) => {H} H.
    apply: (H x).
    apply: S.singleton_2.
    reflexivity.
  Qed.

  Lemma subset_singleton2 x s :
    S.mem x s ->
    S.subset (S.singleton x) s.
  Proof.
    move/memP=> H.
    apply: S.subset_1 => y Hy.
    move: (S.singleton_1 Hy) => {Hy} Hxy.
    exact: (S.In_1 Hxy H).
  Qed.

  Lemma subset_singleton x s :
    S.subset (S.singleton x) s = S.mem x s.
  Proof.
    case Hmem: (S.mem x s).
    - exact: subset_singleton2.
    - apply/negP => Hsub.
      move/negP: Hmem; apply.
      exact: subset_singleton1.
  Qed.

  Lemma subset_union1 s1 s2 s3 :
    S.subset s1 s2 ->
    S.subset s1 (S.union s2 s3).
  Proof.
    move=> Hsub.
    apply: S.subset_1 => x /memP Hx.
    apply/memP.
    apply/mem_union2.
    exact: (mem_subset Hx Hsub).
  Qed.

  Lemma subset_union2 s1 s2 s3 :
    S.subset s1 s3 ->
    S.subset s1 (S.union s2 s3).
  Proof.
    rewrite OP.P.union_sym.
    exact: subset_union1.
  Qed.

  Lemma subset_union3 s1 s2 s3 :
    S.subset s1 s3 ->
    S.subset s2 s3 ->
    S.subset (S.union s1 s2) s3.
  Proof.
    move=> H13 H23.
    apply: S.subset_1.
    apply: OP.P.union_subset_3.
    - exact: (S.subset_2 H13).
    - exact: (S.subset_2 H23).
  Qed.

  Lemma subset_union4 s1 s2 s3 :
    S.subset (S.union s1 s2) s3 ->
    S.subset s1 s3.
  Proof.
    move=> Hsub.
    move: (S.subset_2 Hsub) => {Hsub} Hsub.
    apply: S.subset_1 => x Hinx.
    apply: (Hsub x).
    exact: (S.union_2 _ Hinx).
  Qed.

  Lemma subset_union5 s1 s2 s3 :
    S.subset (S.union s1 s2) s3 ->
    S.subset s2 s3.
  Proof.
    rewrite OP.P.union_sym.
    exact: subset_union4.
  Qed.

  Lemma subset_union6 s1 s2 s3 :
    S.subset (S.union s1 s2) s3 = S.subset s1 s3 && S.subset s2 s3.
  Proof.
    case H: (S.subset s1 s3 && S.subset s2 s3).
    - move/andP: H => [H13 H23].
      apply: subset_union3; assumption.
    - apply/negP => H123.
      move/negP: H; apply.
      move: (subset_union4 H123) (subset_union5 H123) => {H123} H13 H23.
      by rewrite H13 H23.
  Qed.

  Lemma elements_singleton x : eqlistA S.E.eq (S.elements (S.singleton x)) [:: x].
  Proof.
    rewrite (@OP.elements_Add_Above (S.empty) (S.singleton x) x).
    - rewrite P.elements_empty /=. apply: eqlistA_cons.
      + exact: S.E.eq_refl.
      + exact: eqlistA_nil.
    - move=> y Hin. apply: False_ind. move/F.empty_iff: Hin. by apply.
    - move=> y. split.
      + move=> Hin. left. exact: (S.singleton_1 Hin).
      + case=> Hin.
        * apply: S.singleton_2. assumption.
        * apply: False_ind. move/F.empty_iff: Hin. by apply.
  Qed.

  Lemma mem_inA_elements :
    forall x s,
      S.mem x s ->
      InA S.E.eq x (S.elements s).
  Proof.
    move=> x s Hmem.
    apply: S.elements_1.
    apply/memP.
    assumption.
  Qed.

  Lemma inA_elements_mem :
    forall x s,
      InA S.E.eq x (S.elements s) ->
      S.mem x s.
  Proof.
    move=> x s Hin.
    apply/memP.
    apply: S.elements_2.
    assumption.
  Qed.

  Lemma subset_refl :
    forall s, S.subset s s.
  Proof.
    move=> s; apply: S.subset_1.
    exact: OP.P.subset_refl.
  Qed.

  Lemma subset_trans :
    forall s1 s2 s3, S.subset s1 s2 -> S.subset s2 s3 -> S.subset s1 s3.
  Proof.
    move=> s1 s2 s3 H12 H23.
    move: (S.subset_2 H12) => {H12} H12.
    move: (S.subset_2 H23) => {H23} H23.
    apply: S.subset_1.
    exact: (OP.P.subset_trans H12 H23).
  Qed.

  Lemma subset_add :
    forall v s1 s2,
      S.subset s1 s2 ->
      S.subset s1 (S.add v s2).
  Proof.
    move=> v s1 s2 Hsub.
    move: (S.subset_2 Hsub) => {Hsub} Hsub.
    apply: S.subset_1 => x Hin.
    move: (Hsub x Hin) => {Hin} Hin.
    exact: (S.add_2 _ Hin).
  Qed.

  Lemma subset_add2 x s1 s2 :
    S.subset s1 s2 -> S.subset s1 (S.add x s2).
  Proof.
    move=> Hsub.
    move: (S.subset_2 Hsub) => {Hsub} Hsub.
    apply/S.subset_1.
    exact: OP.P.subset_add_2.
  Qed.

  Lemma subset_add3 x s1 s2 :
    S.mem x s2 -> S.subset s1 s2 -> S.subset (S.add x s1) s2.
  Proof.
    move=> /memP Hin Hsub.
    move: (S.subset_2 Hsub) => {Hsub} Hsub.
    apply/S.subset_1.
    exact: OP.P.subset_add_3.
  Qed.

  Lemma subset_add4 x s1 s2 :
    S.subset (S.add x s1) s2 -> S.mem x s2.
  Proof.
    rewrite OP.P.add_union_singleton. move=> H.
    move: (subset_union4 H) => {H} H. exact: (subset_singleton1 H).
  Qed.

  Lemma subset_add5 x s1 s2 :
    S.subset (S.add x s1) s2 -> S.subset s1 s2.
  Proof.
    rewrite OP.P.add_union_singleton. move=> H. exact: (subset_union5 H).
  Qed.

  Lemma subset_add6 x s1 s2 :
  S.subset (S.add x s1) s2 = S.mem x s2 && S.subset s1 s2.
  Proof.
    case H: (S.mem x s2 && S.subset s1 s2).
    - move/andP: H => [H1 H2]. exact: (subset_add3 H1 H2).
    - apply/negP => Hsub. move/negP: H; apply.
      by rewrite (subset_add4 Hsub) (subset_add5 Hsub).
  Qed.

  Lemma mem_empty :
    forall v,
      S.mem v S.empty = false.
  Proof.
    move=> v.
    apply/memP => Hin.
    move: (S.empty_1) => Hemp.
    move: (Hemp v); apply.
    assumption.
  Qed.

  Lemma is_empty_mem v s : S.is_empty s -> ~~ S.mem v s.
  Proof.
    move=> H. apply/negP => /memP Hmem. apply: (S.is_empty_2 H).
    exact: Hmem.
  Qed.

  Lemma is_empty_not_mem s : (forall x, ~~ S.mem x s) -> S.is_empty s.
  Proof.
    move=> H. apply: S.is_empty_1. move=> x /memP Hmem.
    move: (H x) => /negP; apply. exact: Hmem.
  Qed.

  Lemma Empty_mem :
    forall v s,
      S.Empty s ->
      S.mem v s = false.
  Proof.
    move=> v s Hemp.
    apply/memP => Hin.
    exact: (Hemp v Hin).
  Qed.

  Lemma in_of_list1 x s :
    S.In x (OP.P.of_list s) -> InA S.E.eq x s.
  Proof.
    move=> Hin.
    move: (OP.P.of_list_1 s x) => [H1 H2].
    exact: (H1 Hin).
  Qed.

  Lemma in_of_list2 x s :
    InA S.E.eq x s -> S.In x (OP.P.of_list s).
  Proof.
    move=> Hin.
    move: (OP.P.of_list_1 s x) => [H1 H2].
    exact: (H2 Hin).
  Qed.

  Lemma mem_of_list1 x s :
    S.mem x (OP.P.of_list s) -> InA S.E.eq x s.
  Proof.
    move=> /memP Hin.
    exact: in_of_list1.
  Qed.

  Lemma mem_of_list2 x s :
    InA S.E.eq x s -> S.mem x (OP.P.of_list s).
  Proof.
    move=> Hin; apply/memP.
    exact: in_of_list2.
  Qed.

  Lemma mem_remove1 x y s :
    S.mem x (S.remove y s) ->
    ~ S.E.eq x y /\ S.mem x s.
  Proof.
    move=> Hmem; split.
    - move=> Heq.
      move: (S.E.eq_sym Heq) => {Heq} Heq.
      apply: (@S.remove_1 s y x Heq).
      apply/memP.
      assumption.
    - apply/memP; apply: (@S.remove_3 s y x); apply/memP; assumption.
  Qed.

  Lemma mem_remove2 x y s :
    S.E.eq x y ->
    ~~ S.mem x (S.remove y s).
  Proof.
    move=> Heq.
    apply/negP => Hmem.
    move: (mem_remove1 Hmem) => {Hmem} [Hne Hmem].
    apply: Hne; assumption.
  Qed.

  Lemma mem_remove3 x y s :
    ~ S.E.eq x y ->
    S.mem x s ->
    S.mem x (S.remove y s).
  Proof.
    move=> Hne Hmem.
    apply/memP; apply: S.remove_2.
    - move=> Heq; apply: Hne; apply: S.E.eq_sym; assumption.
    - apply/memP; assumption.
  Qed.

  Lemma in_remove_ne x y s :
    S.In x (S.remove y s) -> ~ S.E.eq x y.
  Proof.
    move=> Hin Heq.
    move: (S.E.eq_sym Heq) => {Heq} Heq.
    exact: (S.remove_1 Heq Hin).
  Qed.

  Lemma diff_add x s1 s2 :
    S.Equal (S.diff s1 (S.add x s2)) (S.remove x (S.diff s1 s2)).
  Proof.
    split => Hin.
    - apply: S.remove_2.
      + move=> Heq; apply: (S.diff_2 Hin).
        exact: (S.add_1 _ Heq).
      + apply: (S.diff_3 (S.diff_1 Hin)).
        move=> H; apply: (S.diff_2 Hin).
        exact: (S.add_2 _ H).
    - apply: S.diff_3.
      + exact: (S.diff_1 (S.remove_3 Hin)).
      + move: (OP.P.Add_add s2 x a).
        move=> [H _].
        move=> H1; case: (H H1) => {H H1}.
        * move=> Heq.
          move: (S.E.eq_sym Heq) => {Heq} Heq.
          exact: (in_remove_ne Hin Heq).
        * move=> Hins2.
          exact: (S.diff_2 (S.remove_3 Hin) Hins2).
  Qed.

  Lemma subset_union_diff1 s1 s2 s3 :
    S.subset s1 (S.union s2 s3) ->
    S.subset (S.diff s1 s2) s3.
  Proof.
    move=> H.
    apply: S.subset_1 => x Hin_diff.
    move: (S.subset_2 H) => {H} H.
    move: (H x (S.diff_1 Hin_diff)) => Hin_union.
    case: (S.union_1 Hin_union).
    - move=> Hin2.
      apply: False_ind; exact: (S.diff_2 Hin_diff Hin2).
    - by apply.
  Qed.

  Lemma subset_union_diff2 s1 s2 s3 :
    S.subset s1 (S.union s2 s3) ->
    S.subset (S.diff s1 s3) s2.
  Proof.
    rewrite OP.P.union_sym.
    move=> H.
    exact: (subset_union_diff1 H).
  Qed.

  Lemma subset_union_diff3 s1 s2 :
    S.subset s1 (S.union (S.diff s1 s2) s2).
  Proof.
    apply: S.subset_1 => x Hinx.
    case Hmem: (S.mem x s2).
    - apply: S.union_3.
      apply/memP; assumption.
    - apply: S.union_2.
      apply: (S.diff_3 Hinx).
      apply/memP.
      by rewrite Hmem.
  Qed.

  Lemma subset_union_diff4 s1 s2 s3 :
    S.subset (S.diff s1 s2) s3 ->
    S.subset s1 (S.union s2 s3).
  Proof.
    move=> H.
    move: (S.subset_2 H) => {H} H.
    apply/S.subset_1 => x Hinx.
    case H2: (S.mem x s2).
    - apply: S.union_2.
      apply/memP; assumption.
    - apply: S.union_3.
      apply: (H x).
      apply: (S.diff_3 Hinx).
      apply/memP.
      by rewrite H2.
  Qed.

  Lemma mem_inter1 x s1 s2 :
    S.mem x (S.inter s1 s2) -> S.mem x s1.
  Proof.
    move=> /memP H.
    apply/memP.
    exact: (S.inter_1 H).
  Qed.

  Lemma mem_inter2 x s1 s2 :
    S.mem x (S.inter s1 s2) -> S.mem x s2.
  Proof.
    move=> /memP H.
    apply/memP.
    exact: (S.inter_2 H).
  Qed.

  Lemma mem_inter3 x s1 s2 :
    S.mem x s1 -> S.mem x s2 ->
    S.mem x (S.inter s1 s2).
  Proof.
    move=> /memP H1 /memP H2.
    apply/memP.
    exact: (S.inter_3 H1 H2).
  Qed.



  Definition disjoint s1 s2 : bool :=
    S.is_empty (S.inter s1 s2).

  Lemma disjoint_sym s1 s2 :
    disjoint s1 s2 = disjoint s2 s1.
  Proof.
    rewrite /disjoint OP.P.inter_sym.
    reflexivity.
  Qed.

  Lemma disjoint_nonempty_anti_refl s : ~~ S.is_empty s -> ~~ disjoint s s.
  Proof.
    move=> Hemp.
    apply/negP => H.
    move/negP: Hemp; apply.
    move: H.
    by rewrite /disjoint OP.P.inter_subset_equal.
  Qed.

  Lemma mem_disjoint1 x s1 s2 :
    disjoint s1 s2 ->
    S.mem x s1 -> ~~ S.mem x s2.
  Proof.
    move=> Hd Hm1.
    apply/negP => Hm2.
    move: (S.is_empty_2 Hd) => {Hd} Hd.
    apply: (Hd x).
    apply/memP.
    exact: (mem_inter3 Hm1 Hm2).
  Qed.

  Lemma mem_disjoint2 x s1 s2 :
    disjoint s1 s2 ->
    S.mem x s2 -> ~~ S.mem x s1.
  Proof.
    rewrite disjoint_sym.
    exact: mem_disjoint1.
  Qed.

  Lemma mem_disjoint3 s1 s2 :
    (forall x, S.mem x s1 -> ~~ S.mem x s2) -> disjoint s1 s2.
  Proof.
    move=> H. apply: is_empty_not_mem. move=> x. apply/negP => Hmem.
    move: (H x (mem_inter1 Hmem)). move/negP; apply. exact: (mem_inter2 Hmem).
  Qed.

  Lemma disjoint_singleton x s :
    disjoint s (S.singleton x) = ~~ S.mem x s.
  Proof.
    case H: (S.mem x s) => /=.
    - apply/negP => Hd.
      move: (S.is_empty_2 Hd) => Hemp.
      apply: (Hemp x).
      apply/memP.
      apply: (mem_inter3 H).
      apply: mem_singleton2.
      exact: S.E.eq_refl.
    - move/negP: H => H.
      apply: S.is_empty_1 => v /memP Hv.
      apply: H.
      rewrite -(mem_singleton1 (mem_inter2 Hv)).
      exact: (mem_inter1 Hv).
  Qed.

  Lemma disjoint_add x s1 s2 :
    disjoint s1 (S.add x s2) = ~~ S.mem x s1 && disjoint s1 s2.
  Proof.
    case Hx: (S.mem x s1) => /=.
    - apply/negP => Hd.
      move: (S.is_empty_2 Hd) => Hemp.
      apply: (Hemp x).
      apply/memP.
      apply: (mem_inter3 Hx).
      apply: mem_add2.
      exact: S.E.eq_refl.
    - case Hd12: (disjoint s1 s2) => /=.
      + apply: S.is_empty_1 => v /memP Hv.
        move: (mem_inter1 Hv) (mem_inter2 Hv) => {Hv} Hv1 Hv2.
        move: (S.is_empty_2 Hd12) => {Hd12} Hemp.
        apply: (Hemp v) => {Hemp}.
        apply/memP.
        apply: (mem_inter3 Hv1).
        case: (mem_add1 Hv2); last by apply.
        move=> H.
        apply: False_ind.
        move/negP: Hx; apply.
        rewrite -H; assumption.
      + apply/negP => Hd.
        move/negP: Hd12; apply.
        apply: S.is_empty_1 => v /memP Hv.
        move: (S.is_empty_2 Hd) => {Hd} Hemp.
        apply: (Hemp v).
        apply/memP.
        apply: (mem_inter3 (mem_inter1 Hv)).
        apply: mem_add3.
        exact: (mem_inter2 Hv).
  Qed.

  Lemma disjoint_union s1 s2 s3 :
    disjoint s1 (S.union s2 s3) = disjoint s1 s2 && disjoint s1 s3.
  Proof.
    case H12: (disjoint s1 s2); case H13: (disjoint s1 s3) => /=.
    - apply: mem_disjoint3 => x Hmem1. apply/negP => Hmem23.
      case: (mem_union1 Hmem23) => Hmem.
      + move: (mem_disjoint1 H12 Hmem1). move/negP; apply. exact: Hmem.
      + move: (mem_disjoint1 H13 Hmem1). move/negP; apply. exact: Hmem.
    - apply/negP => H123. move/negP: H13; apply. apply: mem_disjoint3 => x Hmem1.
      apply/negP => Hmem3. move: (mem_disjoint1 H123 Hmem1). move/negP; apply.
      apply: mem_union3. exact: Hmem3.
    - apply/negP => H123. move/negP: H12; apply. apply: mem_disjoint3 => x Hmem1.
      apply/negP => Hmem2. move: (mem_disjoint1 H123 Hmem1). move/negP; apply.
      apply: mem_union2. exact: Hmem2.
    - apply/negP => H123. move/negP: H13; apply. apply: mem_disjoint3 => x Hmem1.
      apply/negP => Hmem3. move: (mem_disjoint1 H123 Hmem1). move/negP; apply.
      apply: mem_union3. exact: Hmem3.
  Qed.

  Lemma disjoint_diff s1 s2 : disjoint (S.diff s1 s2) s2.
  Proof.
    rewrite /disjoint. apply: S.is_empty_1. move=> x Hin.
    move: (S.inter_1 Hin) (S.inter_2 Hin) => Hin1 Hin2.
    apply: (S.diff_2 Hin1). exact: Hin2.
  Qed.

  Lemma subset_union_disjoint1 s1 s2 s3 :
    S.subset s1 (S.union s2 s3) ->
    disjoint s1 s3 ->
    S.subset s1 s2.
  Proof.
    move=> Hsub Hd.
    apply: S.subset_1 => x /memP Hmem1.
    apply/memP.
    case: (mem_union1 (@mem_subset x _ _ Hmem1 Hsub)).
    - done.
    - move=> Hmem3.
      apply: False_ind.
      apply/negP/negPn: (mem_disjoint1 Hd Hmem1).
      assumption.
  Qed.

  Lemma subset_union_disjoint2 s1 s2 s3 :
    S.subset s1 (S.union s2 s3) ->
    disjoint s1 s2 ->
    S.subset s1 s3.
  Proof.
    rewrite OP.P.union_sym.
    exact: subset_union_disjoint1.
  Qed.

  Lemma max_elt1 s x : S.max_elt s = Some x -> S.mem x s.
  Proof.
    move=> H; apply/memP; exact: S.max_elt_1.
  Qed.

  Lemma max_elt2 s x y : S.max_elt s = Some x -> S.mem y s -> ~ S.E.lt x y.
  Proof.
    move=> H1 /memP H2; exact: (S.max_elt_2 H1 H2).
  Qed.

  Lemma max_elt3 s : S.max_elt s = None -> S.is_empty s.
  Proof.
    move=> H; apply: S.is_empty_1; exact: S.max_elt_3 H.
  Qed.

  Lemma union_same s : S.Equal (S.union s s) s.
  Proof.
    apply: union_subset_equal. exact: subset_refl.
  Qed.

  Lemma union2_same1 s1 s2 s3 :
    S.Equal (S.union (S.union s1 s2) (S.union s1 s3))
            (S.union s1 (S.union s2 s3)).
  Proof.
    rewrite -OP.P.union_assoc (OP.P.union_sym _ s1) -OP.P.union_assoc
            union_same OP.P.union_assoc. reflexivity.
  Qed.

  Lemma union2_same2 s1 s2 s3 :
    S.Equal (S.union (S.union s1 s3) (S.union s2 s3))
            (S.union (S.union s1 s2) s3).
  Proof.
    rewrite OP.P.union_assoc (OP.P.union_sym s3) OP.P.union_assoc
            union_same OP.P.union_assoc. reflexivity.
  Qed.

  Lemma add2_same x s1 s2 :
    S.Equal (S.union (S.add x s1) (S.add x s2))
            (S.add x (S.union s1 s2)).
  Proof.
    have Heq: S.E.eq x x by reflexivity.
    move: (@mem_add2 x x (S.union s1 s2) Heq) => Hx.
    rewrite -(add_equal Hx). rewrite -(@union_add2 x s1 s2).
    rewrite -OP.P.union_add. reflexivity.
  Qed.


  Section ForAll.

    Variable f : S.elt -> bool.
    Variable compat : compat_bool S.E.eq f.

    Lemma for_all_union vs1 vs2 :
      S.for_all f (S.union vs1 vs2) = (S.for_all f vs1 && S.for_all f vs2).
    Proof.
      case Hall1: (S.for_all f vs1) => /=.
      - move: (S.for_all_2 compat Hall1) => {Hall1} Hall1.
        case Hall2: (S.for_all f vs2).
        + apply: (S.for_all_1 compat).
          move=> x Hin. case: (S.union_1 Hin) => {Hin} Hin.
          * exact: (Hall1 x Hin).
          * move: (S.for_all_2 compat Hall2) => {Hall2} Hall2. exact: (Hall2 x Hin).
        + apply/negP => Hunion. move/negP: Hall2. apply.
          move: (S.for_all_2 compat Hunion) => {Hunion} Hunion.
          apply: (S.for_all_1 compat). move=> x Hin2.
          exact: (Hunion x (S.union_3 vs1 Hin2)).
      - apply/negP=> Hunion. move/negP: Hall1. apply.
        move: (S.for_all_2 compat Hunion) => {Hunion} Hunion.
        apply: (S.for_all_1 compat). move=> x Hin1.
        exact: (Hunion x (S.union_2 vs2 Hin1)).
    Qed.

    Lemma for_all_subset vs1 vs2 :
      S.subset vs1 vs2 -> S.for_all f vs2 -> S.for_all f vs1.
    Proof.
      move=> Hsub Hall2. move: (S.for_all_2 compat Hall2) => {Hall2} Hall2.
      apply: (S.for_all_1 compat). move=> x Hin1.
      move: (S.subset_2 Hsub) => {Hsub} Hsub. move: (Hsub x Hin1) => Hin2.
      exact: (Hall2 x Hin2).
    Qed.

    Lemma for_all_singleton v : S.for_all f (S.singleton v) = f v.
    Proof.
      case H: (f v).
      - apply: (S.for_all_1 compat). move=> y /memP Hiny.
        move: (mem_singleton1 Hiny) => Heqy. rewrite (compat Heqy). assumption.
      - apply/negP=> Hall. move/negP: H; apply.
        move: (S.for_all_2 compat Hall) => {Hall} Hall.
        move: (mem_singleton2 (S.E.eq_refl v)) => /memP Hin. exact: (Hall v Hin).
    Qed.

    Lemma for_all_Add v vs1 vs2 :
      P.Add v vs1 vs2 ->
      S.for_all f vs2 = f v && S.for_all f vs1.
    Proof.
      move=> Hadd. case H: (f v && S.for_all f vs1).
      - move/andP: H => [Hfv Hall]. move: (S.for_all_2 compat Hall) => {Hall} Hall.
        apply: (S.for_all_1 compat) => y /(Hadd y) Hiny. case: Hiny => Hiny.
        + rewrite -(compat Hiny). assumption.
        + exact: (Hall y Hiny).
      - apply/negP=> Hall. move/negP: H; apply.
        move: (S.for_all_2 compat Hall) => {Hall} Hall. apply/andP; split.
        + move: (Hadd v) => [H1 H2]. exact: (Hall v (H2 (or_introl (S.E.eq_refl v)))).
        + apply: (S.for_all_1 compat) => y Hiny. move: (Hadd y) => [H1 H2].
          exact: (Hall y (H2 (or_intror Hiny))).
    Qed.

    Lemma for_all_add v vs : S.for_all f (S.add v vs) = f v && S.for_all f vs.
    Proof. exact: (for_all_Add (P.Add_add _ _)). Qed.

    Lemma for_all_inter vs1 vs2 :
      S.for_all f vs1 -> S.for_all f vs2 -> S.for_all f (S.inter vs1 vs2).
    Proof.
      move=> H1 H2. move: (S.for_all_2 compat H1) (S.for_all_2 compat H2) =>
                    {H1 H2} H1 H2. apply: (S.for_all_1 compat) => x Hin.
      exact: (H1 x (S.inter_1 Hin)).
    Qed.

    Lemma for_all_mem v vs : S.for_all f vs -> S.mem v vs -> f v.
    Proof.
      move/(S.for_all_2 compat)=> Hall /memP Hin. exact: (Hall v Hin).
    Qed.

  End ForAll.


  Section FoldUnion.

    Variable T : Type.

    Variable f : T -> S.t.

    Lemma mem_foldl_union t r ts :
      S.mem t (foldl (fun res a => S.union (f a) res) r ts) =
      S.mem t r || S.mem t (foldl (fun res a => S.union (f a) res) S.empty ts).
    Proof.
      elim: ts r => /=.
      - move=> r. rewrite mem_empty orbF. reflexivity.
      - move=> ts_hd tl_tl IH r. rewrite (IH (S.union (f ts_hd) r)).
        rewrite mem_union. rewrite (orb_comm (S.mem t (f ts_hd))). rewrite -orb_assoc.
        rewrite -{1}(union_emptyr (f ts_hd)). rewrite -IH. reflexivity.
    Qed.

    Lemma foldl_union_swap (r1 r2 : S.t) (ts : seq T) :
      S.Equal r1 r2 ->
      S.Equal (foldl (fun res a => S.union (f a) res) r1 ts)
              (foldl (fun res a => S.union (f a) res) r2 ts).
    Proof.
      move=> Hr t. move: (Hr t) => [H1 H2]. split => /memP Hf.
      - apply/memP. rewrite mem_foldl_union. rewrite mem_foldl_union in Hf.
        case/orP: Hf => H.
        + by move/memP: H => H; move: (H1 H) => {H} /memP ->.
        + by rewrite H orbT.
      - apply/memP. rewrite mem_foldl_union. rewrite mem_foldl_union in Hf.
        case/orP: Hf => H.
        + by move/memP: H => H; move: (H2 H) => {H} /memP ->.
        + by rewrite H orbT.
    Qed.

    Lemma foldl_union_cons (hd : T) (tl : seq T) (r : S.t) :
      S.Equal
        (foldl (fun res a => S.union (f a) res) r (hd::tl))
        (S.union (f hd) (foldl (fun res a => S.union (f a) res) r tl)).
    Proof.
      apply: (foldl_cons (R := S.Equal)).
      - move=> a1 a2 b. rewrite -OP.P.union_assoc. rewrite (OP.P.union_sym (f a2)).
        rewrite OP.P.union_assoc. reflexivity.
      - exact: foldl_union_swap.
    Qed.

  End FoldUnion.

  Ltac dp_mem :=
    match goal with
    | |- S.mem _ _ = true => apply/idP; dp_mem
    (* *)
    | H : is_true (S.mem ?x ?s) |- is_true (S.mem ?x ?s) => exact: H
    | H : ?x = ?y |- ?x = ?y => exact: H
    | H : ?x = ?y |- is_true (?x == ?y) => apply/eqP; exact: H
    | H : is_true (?x == ?y) |- ?x = ?y => exact: (eqP H)
    | H : is_true (?x == ?y) |- is_true (?x == ?y) => exact: H
    | H : S.E.eq ?x ?y |- S.E.eq ?x ?y => exact: H
    | |- ?x = ?x => reflexivity
    | |- is_true (?x == ?x) => exact: eqxx
    | |- S.E.eq ?x ?x => exact: S.E.eq_refl
    | H1 : is_true (S.mem ?x ?s1), H2 : is_true (S.subset ?s1 ?s2) |-
      is_true (S.mem ?x ?s2) =>
      exact: (mem_subset H1 H2)
    (* *)
    | H : is_true (S.mem ?x (S.singleton ?y)) |- is_true (S.mem ?x _) =>
      move: (mem_singleton1 H) => {H} H; dp_mem
    | H : is_true (S.mem ?x (S.add ?y ?s)) |- is_true (S.mem ?x _) =>
      move: (mem_add1 H) => {H} [] H; dp_mem
    | H : is_true (S.mem ?x (S.union ?s1 ?s2)) |- is_true (S.mem ?x _) =>
      move: (mem_union1 H) => {H} [] H; dp_mem
    (* *)
    | |- is_true (S.mem ?x (S.singleton ?y)) =>
      apply: mem_singleton2; dp_mem
    | |- is_true (S.mem ?x (S.add ?y ?s)) =>
      first [ apply: mem_add2; by dp_mem | apply: mem_add3; by dp_mem ]
    | |- is_true (S.mem ?x (S.union ?s1 ?s2)) =>
      first [ apply: mem_union2; by dp_mem | apply: mem_union3; by dp_mem ]
    (* *)
    | H : is_true (S.subset (S.singleton _) _) |- _ =>
      move: (subset_singleton1 H) => {H} H; dp_mem
    | H : is_true (S.subset (S.add _ _) _) |- _ =>
      let H1 := fresh in let H2 := fresh in
      move: (subset_add4 H) (subset_add5 H) => {H} H1 H2; dp_mem
    | H : is_true (S.subset (S.union _ _) _) |- _ =>
      let H1 := fresh in let H2 := fresh in
      move: (subset_union4 H) (subset_union5 H) => {H} H1 H2; dp_mem
    (* *)
    | H : is_true (_ && _) |- _ =>
      let H1 := fresh in let H2 := fresh in
      move/andP: H => [H1 H2]; dp_mem
    | H : _ /\ _ |- _ =>
      let H1 := fresh in let H2 := fresh in
      move: H => [H1 H2]; dp_mem
    (* *)
    | H : is_true (_ || _) |- _ =>
      move/orP: H => [] H; dp_mem
    | H : _ \/ _ |- _ =>
      move: H => [] H; dp_mem
    end.

  Ltac dp_subset :=
    match goal with
    (* *)
    | |- S.subset _ _ = true => apply/idP; dp_subset
    | |- is_true (S.subset S.empty _) => exact: subset_empty
    | H : is_true (S.subset ?x ?y) |- is_true (S.subset ?x ?y) => exact: H
    | |- is_true (S.subset ?x ?x) => exact: subset_refl
    | H1 : is_true (S.subset ?s1 ?s2), H2 : is_true (S.subset ?s2 ?s3) |-
      is_true (S.subset ?s1 ?s3) =>
      exact: (subset_trans H1 H2)
    (* *)
    | H : is_true (S.subset (S.singleton _) _) |- _ =>
      move: (subset_singleton1 H) => {H} H; dp_subset
    | H : is_true (S.subset (S.add _ _) _) |- _ =>
      let H1 := fresh in let H2 := fresh in
      move: (subset_add4 H) (subset_add5 H) => {H} H1 H2; dp_subset
    | H : is_true (S.subset (S.union _ _) _) |- _ =>
      let H1 := fresh in let H2 := fresh in
      move: (subset_union4 H) (subset_union5 H) => {H} H1 H2; dp_subset
    (* *)
    | |- is_true (S.subset (S.singleton _) _) =>
      apply: subset_singleton2; dp_mem
    | |- is_true (S.subset (S.add _ _) _) =>
      apply: subset_add3; [ dp_mem | dp_subset ]
    | |- is_true (S.subset (S.union _ _) _) =>
      apply: subset_union3; dp_subset
    (* *)
    | |- is_true (S.subset _ (S.add _ _)) =>
      apply: subset_add2; dp_subset
    | |- is_true (S.subset _ (S.union _ _)) =>
      first [ apply: subset_union1; by dp_subset |
              apply: subset_union2; by dp_subset ]
    (* *)
    | H : is_true (_ && _) |- _ =>
      let H1 := fresh in let H2 := fresh in
      move/andP: H => [H1 H2]; dp_subset
    | H : _ /\ _ |- _ =>
      let H1 := fresh in let H2 := fresh in
      move: H => [H1 H2]; dp_subset
    (* *)
    | H : is_true (_ || _) |- _ =>
      move/orP: H => [] H; dp_subset
    | H : _ \/ _ |- _ =>
      move: H => [] H; dp_subset
    end.

  Ltac dp_Equal :=
    apply: OP.P.subset_antisym; apply: S.subset_2; dp_subset.

End FSetLemmas.



(* Extra lemmas for SsrFSet *)

Module SsrFSetLemmas (S : SsrFSet).

  Include FSetLemmas S.

  Lemma mem_in_elements :
    forall x s,
      S.mem x s ->
      x \in (S.elements s).
  Proof.
    move=> x s H. apply: Lists.inA_in. exact: (mem_inA_elements H).
  Qed.

  Lemma in_elements_mem :
    forall x s,
      x \in (S.elements s) ->
      S.mem x s.
  Proof.
    move=> x s H. apply: inA_elements_mem. apply: Lists.in_inA. exact: H.
  Qed.

  Lemma mem_in x s :
    (S.mem x s) = (x \in (S.elements s)).
  Proof.
    case Hin: (x \in (S.elements s)).
    - exact: (in_elements_mem Hin).
    - apply/negP=> Hmem. move/negP: Hin; apply. exact: (mem_in_elements Hmem).
  Qed.

  Lemma mem_of_list_in x s :
    S.mem x (OP.P.of_list s) -> x \in s.
  Proof.
    move=> H. apply: Lists.inA_in. exact: (mem_of_list1 H).
  Qed.

  Lemma in_mem_of_list x s :
    x \in s -> S.mem x (OP.P.of_list s).
  Proof.
    move=> H. apply: mem_of_list2. apply: Lists.in_inA. exact: H.
  Qed.

  Lemma in_mem x s :
    (x \in s) = (S.mem x (OP.P.of_list s)).
  Proof.
    case Hmem: (S.mem x (OP.P.of_list s)).
    - exact: (mem_of_list_in Hmem).
    - apply/negP=> Hin. move/negP: Hmem; apply. exact: (in_mem_of_list Hin).
  Qed.

  Lemma In_elements_mem x s :
    In x (S.elements s) <-> S.mem x s.
  Proof.
    split=> H.
    - apply: inA_elements_mem. move: H. move: (S.elements s).
      elim => [| y ys IH] //=. case => Hin.
      + apply: SetoidList.InA_cons_hd. rewrite Hin. exact: eqxx.
      + apply: SetoidList.InA_cons_tl. exact: (IH Hin).
    - move: (mem_inA_elements H) => {H}. move: (S.elements s).
      elim => [| y ys IH] //=.
      + move=> H. by inversion H.
      + move=> H. inversion_clear H.
        * left. rewrite (eqP H0). reflexivity.
        * right. exact: (IH H0).
  Qed.

  Lemma Subset_incl s1 s2 :
    S.Subset s1 s2 -> incl (S.elements s1) (S.elements s2).
  Proof.
    move=> Hsub. move=> x Hinx1.
    move/In_elements_mem: Hinx1 => Hmem1. apply/In_elements_mem.
    move/memP: Hmem1 => Hin1. apply/memP. exact: (Hsub x Hin1).
  Qed.

  Lemma Equal_incl s1 s2 :
    S.Equal s1 s2 ->
    incl (S.elements s1) (S.elements s2).
  Proof.
    move=> Heq x Hin1. apply/In_elements_mem. apply/memP.
    apply/(Heq x). apply/memP. apply/In_elements_mem. exact: Hin1.
  Qed.

End SsrFSetLemmas.



(* Functors for making SsrFSet *)

Module MakeListSet' (X : SsrOrder) <: SsrFSet with Module SE := X.
  Module SE := X.
  Include FSetList.Make X.
End MakeListSet'.

Module MakeListSet (X : SsrOrder) <: SsrFSet with Module SE := X.
  Module LS := MakeListSet' X.
  Module Lemmas := SsrFSetLemmas LS.
  Include LS.
End MakeListSet.

Module MakeTreeSet' (X : SsrOrder) <: SsrFSet with Module SE := X.
  Module SE := X.
  Include FSetAVL.Make X.
End MakeTreeSet'.

Module MakeTreeSet (X : SsrOrder) <: SsrFSet with Module SE := X.
  Module TS := MakeTreeSet' X.
  Module Lemmas := SsrFSetLemmas TS.
  Include TS.
End MakeTreeSet.

Module Make (X : SsrOrder) <: SsrFSet with Module SE := X := MakeListSet X.



(* Sets that can generate new elements. *)

Module MakeElementGenerator (X : SsrFSet) (D : Types.HasDefault X.SE) (S : HasSucc X.SE) (L : HasLtnSucc X.SE X.SE S).

  Definition new_elt (s : X.t) : X.elt :=
    match X.max_elt s with
    | Some v => S.succ v
    | None => D.default
    end.

  Lemma new_elt_is_new :
    forall (s : X.t), ~~ X.mem (new_elt s) s.
  Proof.
    move=> s. apply/negP => Hmem. move/X.mem_2: Hmem.
    rewrite /new_elt. case H: (X.max_elt s) => Hin.
    - apply: (X.max_elt_2 H Hin). exact: L.ltn_succ.
    - move: (X.max_elt_3 H) => {H} H. apply: (H D.default). assumption.
  Qed.

End MakeElementGenerator.

Module Type SsrFSetWithNew <: SsrFSet.
  Include SsrFSet.
  Parameter new_elt : t -> elt.
  Parameter new_elt_is_new : forall (s : t), ~~ mem (new_elt s) s.
End SsrFSetWithNew.

Module MakeListSetWithNew (X : SsrOrderWithDefaultSucc) <: SsrFSetWithNew.
  Module S := MakeListSet X.
  Include S.
  Module G := MakeElementGenerator S X X X.
  Include G.
End MakeListSetWithNew.

Module MakeTreeSetWithNew (X : SsrOrderWithDefaultSucc) <: SsrFSetWithNew.
  Module S := MakeTreeSet X.
  Include S.
  Module G := MakeElementGenerator S X X X.
  Include G.
End MakeTreeSetWithNew.



(* Map a set of type A to another set of type B *)

Module Map2 (S1 S2 : SsrFSet).

  Module Lemmas1 := FSetLemmas(S1).
  Module Lemmas2 := FSetLemmas(S2).

  Notation of_list := Lemmas2.OP.P.of_list.

  Definition preserve f : Prop :=
    forall x y, S1.E.eq x y -> S2.E.eq (f x) (f y).

  Definition injective f : Prop :=
    forall x y, S2.E.eq (f x) (f y) -> S1.E.eq x y.

  Record well_map2 f : Prop :=
    mkWellMap2 { f_preserve : preserve f;
                 f_injective : injective f }.

  Section Map2.

    Variable f : S1.elt -> S2.elt.

    Variable well : well_map2 f.

    Definition map2 s :=
      of_list (map f (S1.elements s)).

    Lemma inA_map1 x s :
      InA S1.E.eq x s ->
      InA S2.E.eq (f x) (map f s).
    Proof.
      elim: s x => /=.
      - move=> x H; by inversion H.
      - move=> hd tl IH x Hin.
        inversion_clear Hin.
        + apply: InA_cons_hd.
          exact: (f_preserve well).
        + apply: InA_cons_tl.
          exact: (IH _ H).
    Qed.

    Lemma inA_map2 x s :
      InA S2.E.eq (f x) (map f s) ->
      InA S1.E.eq x s.
    Proof.
      elim: s x => /=.
      - move=> x H; by inversion H.
      - move=> hd tl IH x Hin.
        inversion_clear Hin.
        + apply: InA_cons_hd.
          exact: (f_injective well H).
        + apply: InA_cons_tl.
          exact: (IH _ H).
    Qed.

    Lemma inA_map3 x s :
      InA S2.E.eq x (map f s) ->
      exists y, S2.E.eq x (f y) /\ InA S1.E.eq y s.
    Proof.
      elim: s x => /=.
      - move=> x H; by inversion H.
      - move=> hd tl IH x Hin.
        inversion_clear Hin.
        + exists hd; split.
          * assumption.
          * apply: InA_cons_hd.
            exact: S1.E.eq_refl.
        + move: (IH _ H) => [y [Heq HinA]].
          exists y; split.
          * assumption.
          * exact: InA_cons_tl.
    Qed.

    Lemma map2_Empty1 s :
      S1.Empty s ->
      S2.Empty (map2 s).
    Proof.
      move=> Hemp1.
      rewrite /map2.
      move=> x Hin.
      move: (Lemmas1.OP.P.elements_Empty s) => [H _].
      rewrite (H Hemp1) /= in Hin => {H}.
      move: (Lemmas2.empty_iff x) => [H _].
      apply: H; assumption.
    Qed.

    Lemma map2_Empty2 s :
      S2.Empty (map2 s) ->
      S1.Empty s.
    Proof.
      move=> Hemp1.
      rewrite /map2 in Hemp1.
      move=> x Hmem.
      apply: (Hemp1 (f x)).
      apply: Lemmas2.in_of_list2.
      apply: inA_map1.
      exact: (S1.elements_1 Hmem).
    Qed.

    Lemma map2_mem1 x xs :
      S2.mem (f x) (map2 xs) = S1.mem x xs.
    Proof.
      rewrite /map2.
      case Hmem1: (S1.mem x xs).
      - apply: Lemmas2.mem_of_list2.
        apply: inA_map1.
        move/Lemmas1.memP: Hmem1 => Hin1.
        exact: (S1.elements_1 Hin1).
      - apply/negP => Hmem2.
        move/negP: Hmem1; apply.
        move: (Lemmas2.mem_of_list1 Hmem2) => HinA.
        move: (inA_map2 HinA) => {HinA} HinA.
        apply/Lemmas1.memP.
        exact: (S1.elements_2 HinA).
    Qed.

    Lemma map2_mem2 x xs :
      S2.mem x (map2 xs) ->
      exists y, S2.E.eq x (f y) /\ S1.mem y xs.
    Proof.
      rewrite /map2 => Hmem.
      move: (Lemmas2.mem_of_list1 Hmem) => {Hmem} HinA.
      move: (inA_map3 HinA) => {HinA} [y [Heq HinA]].
      exists y; split.
      - assumption.
      - apply/Lemmas1.memP.
        exact: S1.elements_2.
    Qed.

    Lemma map2_singleton x :
      S2.Equal (map2 (S1.singleton x)) (S2.singleton (f x)).
    Proof.
      move=> v; split => /Lemmas2.memP Hmem; apply: Lemmas2.memP.
      - move: (map2_mem2 Hmem) => [y [Hy Hmemy]].
        apply: Lemmas2.mem_singleton2. rewrite (eqP Hy).
        exact: (f_preserve _ (Lemmas1.mem_singleton1 Hmemy)).
      - rewrite (eqP (Lemmas2.mem_singleton1 Hmem)) map2_mem1.
        apply: Lemmas1.mem_singleton2. exact: S1.E.eq_refl.
    Qed.

    Lemma map2_add v s :
      S2.Equal (map2 (S1.add v s)) (S2.add (f v) (map2 s)).
    Proof.
      move=> x; split; move=> /Lemmas2.memP Hmem; apply/Lemmas2.memP.
      - move: (map2_mem2 Hmem) => [y [Hfy Hmemy]].
        case: (Lemmas1.mem_add1 Hmemy) => {Hmemy} Hy.
        + rewrite Hfy. apply: Lemmas2.mem_add2. exact: (f_preserve _ Hy).
        + apply: Lemmas2.mem_add3. rewrite Hfy map2_mem1. assumption.
      - case: (Lemmas2.mem_add1 Hmem) => {Hmem} Hx.
        + rewrite (eqP Hx) map2_mem1. apply: Lemmas1.mem_add2. exact: S1.E.eq_refl.
        + move: (map2_mem2 Hx) => [y [Hfy Hmemy]]. rewrite Hfy map2_mem1.
          apply: Lemmas1.mem_add3. assumption.
    Qed.

    Lemma map2_union s1 s2 :
      S2.Equal (map2 (S1.union s1 s2))
               (S2.union (map2 s1) (map2 s2)).
    Proof.
      move=> x; split; move=> /Lemmas2.memP Hmem; apply/Lemmas2.memP.
      - move: (map2_mem2 Hmem) => [y [Hy Hmemy]].
        case: (Lemmas1.mem_union1 Hmemy) => {Hmemy} Hmemy.
        + apply: Lemmas2.mem_union2. rewrite Hy map2_mem1. assumption.
        + apply: Lemmas2.mem_union3. rewrite Hy map2_mem1. assumption.
      - case: (Lemmas2.mem_union1 Hmem) => {Hmem} Hmemx.
        + move: (map2_mem2 Hmemx) => [y [Hy Hmemy]]. rewrite Hy map2_mem1.
          apply/Lemmas1.mem_union2; assumption.
        + move: (map2_mem2 Hmemx) => [y [Hy Hmemy]]. rewrite Hy map2_mem1.
          apply/Lemmas1.mem_union3; assumption.
    Qed.

    Lemma mem_map2_union x s1 s2 :
      S2.mem x (map2 (S1.union s1 s2)) =
      (S2.mem x (map2 s1)) || (S2.mem x (map2 s2)).
    Proof.
      rewrite map2_union. rewrite Lemmas2.F.union_b. reflexivity.
    Qed.

    Lemma map2_union1 x s1 s2 :
      S2.mem x (map2 (S1.union s1 s2)) ->
      S2.mem x (map2 s1) \/ S2.mem x (map2 s2).
    Proof.
      rewrite map2_union => Hmem. case: (Lemmas2.mem_union1 Hmem); [by left | by right].
    Qed.

    Lemma map2_union2 x s1 s2 :
      S2.mem x (map2 s1) ->
      S2.mem x (map2 (S1.union s1 s2)).
    Proof.
      rewrite map2_union => Hmem. apply: Lemmas2.mem_union2; assumption.
    Qed.

    Lemma map2_union3 x s1 s2 :
      S2.mem x (map2 s2) ->
      S2.mem x (map2 (S1.union s1 s2)).
    Proof.
      rewrite map2_union => Hmem. apply: Lemmas2.mem_union3; assumption.
    Qed.

    Lemma map2_subset s1 s2 :
      S2.subset (map2 s1) (map2 s2) = S1.subset s1 s2.
    Proof.
      case H: (S1.subset s1 s2).
      - apply: S2.subset_1 => x /Lemmas2.memP Hmem. apply/Lemmas2.memP.
        move: (map2_mem2 Hmem) => {Hmem} [fx [Heq Hmem]].
        rewrite Heq map2_mem1. exact: (Lemmas1.mem_subset Hmem H).
      - apply/negP => Hsubset. move/negP: H; apply.
        apply: S1.subset_1 => x /Lemmas1.memP Hmem. apply/Lemmas1.memP.
        rewrite -map2_mem1. apply: (Lemmas2.mem_subset _ Hsubset).
        rewrite map2_mem1. assumption.
    Qed.

  End Map2.

End Map2.
