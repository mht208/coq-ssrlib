
(** * Variables *)

From Coq Require Import FMaps FSets FMapAVL ZArith OrderedType String Morphisms.
From mathcomp Require Import ssreflect ssrbool eqtype.
From ssrlib Require Import Orders Sets Maps ZAriths Strings.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(** ** Variables using Logic.eq as equality *)

Module V.

  Import O Orders.N FS FM.

  Module VarOrder := NOrdered.

  Definition var := VarOrder.t.

  Module VarOrderPrinter <: Printer with Definition t := var.
    Definition t := VarOrder.t.
    Definition to_string (v : VarOrder.t) :=
      ("v" ++ string_of_N v)%string.
  End VarOrderPrinter.

  Module VSBase := FSetAVL.Make VarOrder.
  Module VS := FSetInterface_as_FS_WDS VarOrder VSBase.
  Module VMBase := FMapAVL.Make VarOrder.
  Module VM := FMapInterface_as_FM_WDS VarOrder VMBase.


  (** ** Variables in SSA form - product of a variable and an index *)

  Module SSAVarOrder := ProdEqOrderedWithDefaultSucc VarOrder NOrdered.

  Module SSAVarOrderPrinter <: Printer with Definition t := SSAVarOrder.t.
    Definition t := SSAVarOrder.t.
    Definition to_string (v : SSAVarOrder.t) : string :=
      ("v" ++ string_of_N (fst v) ++ "_" ++ string_of_N (snd v))%string.
  End SSAVarOrderPrinter.

  Definition ssavar := SSAVarOrder.t.

  Module SSAVSBase := FSetAVL.Make SSAVarOrder.
  Module SSAVS := FSetInterface_as_FS_WDS SSAVarOrder SSAVSBase.
  Module SSAVMBase := FMapAVL.Make SSAVarOrder.
  Module SSAVM := FMapInterface_as_FM_WDS SSAVarOrder SSAVMBase.

  Definition svar (x : ssavar) : var := fst x.
  Definition sidx (x : ssavar) : N := snd x.

  #[global]
   Hint Unfold svar sidx : core.


  (** ** Membership of SSA variables in a set ignoring indices *)

  Definition svar_notin (v : var) (vs : SSAVS.t) : Prop := forall i : var, ~~ FS.mem (v, i) vs.


  Ltac oeq_fst :=
    match goal with
    | H : ?a == ?b |- (?a, ?c) == (?b, ?c) => split; [ assumption | reflexivity ]
    | H : ?b == ?a |- (?a, ?c) == (?b, ?c) => split; [ symmetry; assumption | reflexivity ]
    end.

  #[global]
   Add Morphism svar_notin with signature oeq ==> FS.Equal ==> iff as svar_notin_m.
  Proof.
    move=> v1 v2 Hv s1 s2 Hs. split.
    - move=> Hnotin x. rewrite -Hs. (* rewrite -Hv is pretty slow *)
      move/oeq_eq: Hv => <-. exact: (Hnotin x).
    - move=> Hnotin x. rewrite Hs. move/oeq_eq: Hv => ->.
      exact: (Hnotin x).
  Qed.


  Lemma svar_notin_empty avn : svar_notin avn FS.empty.
  Proof. move=> x. rewrite L.mem_empty. by trivial. Qed.

  Lemma svar_notin_singleton_neq v x :
    svar_notin v (singleton x) -> (v ~= svar x)%OT.
  Proof.
    destruct x as [x i]. move=> /= H; move: (L.not_mem_singleton_neq (H i)).
    move=> Hne Heq. apply: Hne. by split.
  Qed.

  Lemma neq_svar_notin_singleton v x :
    (v ~= svar x)%OT -> svar_notin v (singleton x).
  Proof.
    move=> Hne i. apply/negP => Heq; apply: Hne.
    move: (L.mem_singleton_eq Heq) => {Heq}.
    case: x => [x j] => [] [Hv Hi] /=. exact: Hv.
  Qed.

  Lemma svar_notin_singleton_iff v x :
    svar_notin v (singleton x) <-> (v ~= svar x)%OT.
  Proof. split; [exact: svar_notin_singleton_neq | exact: neq_svar_notin_singleton]. Qed.

  Lemma svar_notin_union_l v vs1 vs2 :
    svar_notin v (union vs1 vs2) -> svar_notin v vs1.
  Proof. move=> H i. move: (H i) => {} H. exact: (L.not_mem_union_l H). Qed.

  Lemma svar_notin_union_r v vs1 vs2 :
    svar_notin v (union vs1 vs2) -> svar_notin v vs2.
  Proof. move=> H i. move: (H i) => {} H. exact: (L.not_mem_union_r H). Qed.

  Lemma svar_notin_union v vs1 vs2 :
    svar_notin v vs1 -> svar_notin v vs2 ->
    svar_notin v (union vs1 vs2).
  Proof.
    move=> H1 H2 i. move: (H1 i) (H2 i) => {H2} H1 H2.
    exact: (L.not_mem_union H1 H2).
  Qed.

  Lemma svar_notin_union_iff v vs1 vs2 :
    svar_notin v (union vs1 vs2) <-> (svar_notin v vs1 /\ svar_notin v vs2).
  Proof.
    split=> H.
    - exact: (conj (svar_notin_union_l H) (svar_notin_union_r H)).
    - case: H => H1 H2. exact: (svar_notin_union H1 H2).
  Qed.

  Lemma svar_notin_add_neq v x vs :
    svar_notin v (FS.add x vs) -> (v ~= svar x)%OT.
  Proof.
    destruct x as [x i] => /= H. move: (H i) => {} H.
    move/L.not_mem_add_iff: H => [H _]. move=> Hvx; apply: H.
    by split.
  Qed.

  Lemma svar_notin_add_notin v x vs :
    svar_notin v (FS.add x vs) -> svar_notin v vs.
  Proof.
    move=> H i. move: (H i) => {} H.
    move/L.not_mem_add_iff: H => [_ H]. exact: H.
  Qed.

  Lemma svar_notin_add_iff v x vs :
    svar_notin v (FS.add x vs) <-> (v ~= svar x /\ svar_notin v vs)%OT.
  Proof.
    split.
    - move=> H; exact: (conj (svar_notin_add_neq H) (svar_notin_add_notin H)).
    - move=> [H1 H2]. move=> i. apply/negP=> H. case/L.mem_add_or: H.
      + case: x H1 => /= xn vi H1 [] Hv Hi. apply: H1. assumption.
      + apply/negP. exact: (H2 i).
  Qed.

  #[global]
   Add Morphism svar_notin with signature oeq ==> Subset --> impl as svar_notin_S_m.
  Proof.
    move=> v1 v2 Hv s1 s2 Hs. move=> Hnotin x. apply/negP => /Sets.L.memP H.
    rewrite -> Hs in H. move/oeq_eq: Hv => Hv. subst.
    move/Sets.L.memP: H. apply/negP. exact: Hnotin.
  Qed.

  #[global]
   Add Morphism svar_notin with signature oeq ==> subset --> impl as svar_notin_s_m.
  Proof.
    move=> v1 v2 Hv s1 s2 /L.subsetP Hs.
    exact: (svar_notin_S_m Hv Hs).
  Qed.

  Lemma svar_notin_subset v vs1 vs2 :
    subset vs1 vs2 -> svar_notin v vs2 -> svar_notin v vs1.
  Proof.
    move=> Hsub Hnotin. exact: (svar_notin_s_m (O.eq_refl _) Hsub Hnotin).
  Qed.

  Ltac simpl_svar_notin :=
    repeat
      match goal with
      | H : svar_notin _ (add _ _) |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          move/svar_notin_add: H => [H1 H2]
      | H : svar_notin _ (union _ _) |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          move/svar_notin_union: H => [H1 H2]
      end.

  Ltac dp_svar_notin :=
    repeat
      match goal with
      | H : ?e |- ?e => assumption
      | |- svar_notin _ empty =>
          exact: svar_notin_empty
      | H : svar_notin _ (singleton _) |- _ =>
          move/svar_notin_singleton: H => H
      | H : svar_notin _ (add _ _) |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          move/svar_notin_add: H => [H1 H2]
      | H : svar_notin _ (union _ _) |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          move/svar_notin_union: H => [H1 H2]
      | |- svar_notin _ (singleton _) =>
          apply/svar_notin_singleton_iff
      | |- svar_notin _ (add _ _) =>
          apply/svar_notin_add_iff; split
      | |- svar_notin _ (union _ _) =>
          apply/svar_notin_union; split
      | H1 : is_true (subset ?s1 ?s2), H2 : svar_notin ?v ?s2 |-
          svar_notin ?v ?s1 =>
          exact: (svar_notin_subset H1 H2)
      end.


  (** ** Generation of new SSA variables *)

  Definition max_svar (vs : SSAVS.t) : var :=
    match max_elt vs with
    | Some v => svar v
    | None => 0%N
    end.

  Definition new_svar (vs : SSAVS.t) : var :=
    N.succ (max_svar vs).

  Lemma V_ltb_succ v i j : SSAVarOrder.lt (v, j) ((N.succ v), i).
  Proof. left. exact: N.lt_succ_diag_r. Qed.

  Lemma new_svar_notin vs : svar_notin (new_svar vs) vs.
  Proof.
    rewrite /new_svar /max_svar. set x := max_elt vs.
    have: max_elt vs = x by reflexivity. case x.
    - move=> [v j] /= Hmax i. apply/negP => Hmem.
      apply: (L.max_elt_nlt (t:=SSAVS.t) Hmax Hmem).
      exact: V_ltb_succ.
    - move=> Hnone i. apply/negPf. apply: L.is_empty_mem.
      exact: (L.max_elt_empty Hnone).
  Qed.

End V.


(** ** Variables using eq_op as equality *)

Module EV.

  Import O Orders.EN FS FM.

  Module VarOrder := NOrdered.

  Definition var := VarOrder.t.

  Module VarOrderPrinter <: Printer with Definition t := var.
    Definition t := VarOrder.t.
    Definition to_string (v : VarOrder.t) :=
      ("v" ++ string_of_N v)%string.
  End VarOrderPrinter.

  Module VSBase := FSetAVL.Make VarOrder.
  Module VS := FSetInterface_as_FS_WDS VarOrder VSBase.
  Module VMBase := FMapAVL.Make VarOrder.
  Module VM := FMapInterface_as_FM_WDS VarOrder VMBase.


  (** ** Variables in SSA form - product of a variable and an index *)

  Module SSAVarOrder := ProdEqOrderedWithDefaultSucc VarOrder NOrdered.

  Module SSAVarOrderPrinter <: Printer with Definition t := SSAVarOrder.t.
    Definition t := SSAVarOrder.t.
    Definition to_string (v : SSAVarOrder.t) : string :=
      ("v" ++ string_of_N (fst v) ++ "_" ++ string_of_N (snd v))%string.
  End SSAVarOrderPrinter.

  Definition ssavar := SSAVarOrder.t.

  Module SSAVSBase := FSetAVL.Make SSAVarOrder.
  Module SSAVS := FSetInterface_as_FS_WDS SSAVarOrder SSAVSBase.
  Module SSAVMBase := FMapAVL.Make SSAVarOrder.
  Module SSAVM := FMapInterface_as_FM_WDS SSAVarOrder SSAVMBase.

  Definition svar (x : ssavar) : var := fst x.
  Definition sidx (x : ssavar) : N := snd x.

  #[global]
   Hint Unfold svar sidx : core.


  (** ** Membership of SSA variables in a set ignoring indices *)

  Definition svar_notin (v : var) (vs : SSAVS.t) : Prop := forall i : var, ~~ FS.mem (v, i) vs.


  #[global]
   Add Morphism svar_notin with signature oeq ==> FS.Equal ==> iff as svar_notin_m.
  Proof.
    move=> v1 v2 Hv s1 s2 Hs. split.
    - move=> Hnotin x. rewrite -Hs. rewrite -(eqP Hv). exact: (Hnotin x).
    - move=> Hnotin x. rewrite Hs. rewrite (eqP Hv). exact: (Hnotin x).
  Qed.


  Lemma svar_notin_empty avn : svar_notin avn FS.empty.
  Proof. move=> x. rewrite L.mem_empty. by trivial. Qed.

  Lemma svar_notin_singleton_neq v x :
    svar_notin v (singleton x) -> (v ~= svar x)%OT.
  Proof.
    destruct x as [x i]. move=> /= H; move: (L.not_mem_singleton_neq (H i)).
    move=> Hne Heq. apply: Hne. by split.
  Qed.

  Lemma neq_svar_notin_singleton v x :
    (v ~= svar x)%OT -> svar_notin v (singleton x).
  Proof.
    move=> Hne i. apply/negP => Heq; apply: Hne.
    move: (L.mem_singleton_eq Heq) => {Heq}.
    case: x => [x j] => [] [Hv Hi] /=. exact: Hv.
  Qed.

  Lemma svar_notin_singleton_iff v x :
    svar_notin v (singleton x) <-> (v ~= svar x)%OT.
  Proof. split; [exact: svar_notin_singleton_neq | exact: neq_svar_notin_singleton]. Qed.

  Lemma svar_notin_union_l v vs1 vs2 :
    svar_notin v (union vs1 vs2) -> svar_notin v vs1.
  Proof. move=> H i. move: (H i) => {} H. exact: (L.not_mem_union_l H). Qed.

  Lemma svar_notin_union_r v vs1 vs2 :
    svar_notin v (union vs1 vs2) -> svar_notin v vs2.
  Proof. move=> H i. move: (H i) => {} H. exact: (L.not_mem_union_r H). Qed.

  Lemma svar_notin_union v vs1 vs2 :
    svar_notin v vs1 -> svar_notin v vs2 ->
    svar_notin v (union vs1 vs2).
  Proof.
    move=> H1 H2 i. move: (H1 i) (H2 i) => {H2} H1 H2.
    exact: (L.not_mem_union H1 H2).
  Qed.

  Lemma svar_notin_union_iff v vs1 vs2 :
    svar_notin v (union vs1 vs2) <-> (svar_notin v vs1 /\ svar_notin v vs2).
  Proof.
    split=> H.
    - exact: (conj (svar_notin_union_l H) (svar_notin_union_r H)).
    - case: H => H1 H2. exact: (svar_notin_union H1 H2).
  Qed.

  Lemma svar_notin_add_neq v x vs :
    svar_notin v (FS.add x vs) -> (v ~= svar x)%OT.
  Proof.
    destruct x as [x i] => /= H. move: (H i) => {} H.
    move/L.not_mem_add_iff: H => [H _]. move=> Hvx; apply: H.
    by split.
  Qed.

  Lemma svar_notin_add_notin v x vs :
    svar_notin v (FS.add x vs) -> svar_notin v vs.
  Proof.
    move=> H i. move: (H i) => {} H.
    move/L.not_mem_add_iff: H => [_ H]. exact: H.
  Qed.

  Lemma svar_notin_add_iff v x vs :
    svar_notin v (FS.add x vs) <-> (v ~= svar x /\ svar_notin v vs)%OT.
  Proof.
    split.
    - move=> H; exact: (conj (svar_notin_add_neq H) (svar_notin_add_notin H)).
    - move=> [H1 H2]. move=> i. apply/negP=> H. case/L.mem_add_or: H.
      + case: x H1 => /= xn vi H1 [] Hv Hi. apply: H1. assumption.
      + apply/negP. exact: (H2 i).
  Qed.

  #[global]
   Add Morphism svar_notin with signature oeq ==> Subset --> impl as svar_notin_S_m.
  Proof.
    move=> v1 v2 Hv s1 s2 Hs. move=> Hnotin x. apply/negP => /Sets.L.memP H.
    rewrite -> Hs in H. rewrite -(eqP Hv) in H. move/Sets.L.memP: H. apply/negP. exact: Hnotin.
  Qed.

  #[global]
   Add Morphism svar_notin with signature oeq ==> subset --> impl as svar_notin_s_m.
  Proof.
    move=> v1 v2 Hv s1 s2 /L.subsetP Hs.
    exact: (svar_notin_S_m Hv Hs).
  Qed.

  Lemma svar_notin_subset v vs1 vs2 :
    subset vs1 vs2 -> svar_notin v vs2 -> svar_notin v vs1.
  Proof.
    move=> Hsub Hnotin. exact: (svar_notin_s_m (O.eq_refl _) Hsub Hnotin).
  Qed.

  Ltac simpl_svar_notin :=
    repeat
      match goal with
      | H : svar_notin _ (add _ _) |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          move/svar_notin_add: H => [H1 H2]
      | H : svar_notin _ (union _ _) |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          move/svar_notin_union: H => [H1 H2]
      end.

  Ltac dp_svar_notin :=
    repeat
      match goal with
      | H : ?e |- ?e => assumption
      | |- svar_notin _ empty =>
          exact: svar_notin_empty
      | H : svar_notin _ (singleton _) |- _ =>
          move/svar_notin_singleton: H => H
      | H : svar_notin _ (add _ _) |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          move/svar_notin_add: H => [H1 H2]
      | H : svar_notin _ (union _ _) |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          move/svar_notin_union: H => [H1 H2]
      | |- svar_notin _ (singleton _) =>
          apply/svar_notin_singleton_iff
      | |- svar_notin _ (add _ _) =>
          apply/svar_notin_add_iff; split
      | |- svar_notin _ (union _ _) =>
          apply/svar_notin_union; split
      | H1 : is_true (subset ?s1 ?s2), H2 : svar_notin ?v ?s2 |-
          svar_notin ?v ?s1 =>
          exact: (svar_notin_subset H1 H2)
      end.


  (** ** Generation of new SSA variables *)

  Definition max_svar (vs : SSAVS.t) : var :=
    match max_elt vs with
    | Some v => svar v
    | None => 0%N
    end.

  Definition new_svar (vs : SSAVS.t) : var :=
    N.succ (max_svar vs).

  Lemma V_ltb_succ v i j : SSAVarOrder.lt (v, j) ((N.succ v), i).
  Proof. left. apply/N_ltP. exact: N.lt_succ_diag_r. Qed.

  Lemma new_svar_notin vs : svar_notin (new_svar vs) vs.
  Proof.
    rewrite /new_svar /max_svar. set x := max_elt vs.
    have: max_elt vs = x by reflexivity. case x.
    - move=> [v j] /= Hmax i. apply/negP => Hmem.
      apply: (L.max_elt_nlt (t:=SSAVS.t) Hmax Hmem).
      exact: V_ltb_succ.
    - move=> Hnone i. apply/negPf. apply: L.is_empty_mem.
      exact: (L.max_elt_empty Hnone).
  Qed.

End EV.
