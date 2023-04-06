
(** * Variables *)

From Coq Require Import FMaps FSets ZArith OrderedType String.
From mathcomp Require Import ssreflect ssrbool eqtype.
From ssrlib Require Import EqOrder EqFMaps EqFSets ZAriths Strings.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Definition var : Set := N.

Module VarOrder <: EqOrderWithDefaultSucc.
  Include NOrder.
  Definition succ : t -> t := N.succ.
  Lemma ltn_succ : forall (x : t), ltn x (succ x).
  Proof.
    move=> x. apply/N.ltb_lt. exact: N.lt_succ_diag_r.
  Qed.
  Definition default : t := N0.
End VarOrder.

Module VarOrderPrinter <: Printer with Definition t := var.
  Definition t := VarOrder.t.
  Definition to_string (v : VarOrder.t) :=
    ("v" ++ string_of_N v)%string.
End VarOrderPrinter.



(* Variable sets and maps. *)

Module VS <: EqFSetWithNew := EqFSets.MakeTreeSetWithNew VarOrder.
Module VM <: EqFMapWithNew := EqFMaps.MakeTreeMapWithNew VarOrder.



(** Variables for SSA *)

From ssrlib Require Import EqOrder.

Module SSAVarOrder := MakeProdOrderWithDefaultSucc VarOrder VarOrder.

Module SSAVarOrderPrinter <: Printer with Definition t := SSAVarOrder.t.
  Definition t := SSAVarOrder.t.
  Definition to_string (v : SSAVarOrder.t) : string :=
    ("v" ++ string_of_N (fst v) ++ "_" ++ string_of_N (snd v))%string.
End SSAVarOrderPrinter.

Definition ssavar := SSAVarOrder.t.

Module SSAVS <: EqFSetWithNew := EqFSets.MakeTreeSetWithNew SSAVarOrder.
Module SSAVM <: EqFMapWithNew := EqFMaps.MakeTreeMapWithNew SSAVarOrder.

Definition svar (x : SSAVarOrder.t) := fst x.
Definition sidx (x : SSAVarOrder.t) := snd x.

Global Hint Unfold svar sidx : core.

Definition svar_notin v vs : Prop := forall i, ~~ SSAVS.mem (v, i) vs.

Global Instance add_proper_svar_notin :
  Proper (eq ==> SSAVS.Equal ==> iff) svar_notin.
Proof.
  move=> v1 v2 ?; subst. move=> s1 s2 Heq. split.
  - move=> Hnotin x. rewrite -Heq. exact: (Hnotin x).
  - move=> Hnotin x. rewrite Heq. exact: (Hnotin x).
Qed.

Lemma svar_notin_empty avn : svar_notin avn SSAVS.empty.
Proof. move=> x. rewrite SSAVS.Lemmas.mem_empty. by trivial. Qed.

Lemma svar_notin_singleton1 v x :
  svar_notin v (SSAVS.singleton x) -> v != svar x.
Proof.
  destruct x as [x i]. move=> /= H; move: (SSAVS.Lemmas.not_mem_singleton1 (H i)).
  move=> Hne; apply/negP => Heq; apply: Hne. rewrite (eqP Heq).
  exact: SSAVS.E.eq_refl.
Qed.

Lemma svar_notin_singleton2 v x :
  v != svar x -> svar_notin v (SSAVS.singleton x).
Proof.
  move/negP=> Hne i. apply/negP => Heq; apply: Hne.
  move: (SSAVS.Lemmas.mem_singleton1 Heq) => {Heq}. destruct x as [x j] => /=.
  move/eqP => [Hv Hi]. by rewrite Hv.
Qed.

Lemma svar_notin_singleton v x :
  svar_notin v (SSAVS.singleton x) <-> v != svar x.
Proof. split; [exact: svar_notin_singleton1 | exact: svar_notin_singleton2]. Qed.

Lemma svar_notin_union1 v vs1 vs2 :
  svar_notin v (SSAVS.union vs1 vs2) -> svar_notin v vs1.
Proof.
  move=> H i. move: (H i) => {H} H. exact: (proj1 (SSAVS.Lemmas.not_mem_union1 H)).
Qed.

Lemma svar_notin_union2 v vs1 vs2 :
  svar_notin v (SSAVS.union vs1 vs2) -> svar_notin v vs2.
Proof.
  move=> H i. move: (H i) => {H} H. exact: (proj2 (SSAVS.Lemmas.not_mem_union1 H)).
Qed.

Lemma svar_notin_union3 v vs1 vs2 :
  svar_notin v vs1 -> svar_notin v vs2 ->
  svar_notin v (SSAVS.union vs1 vs2).
Proof.
  move=> H1 H2 i. move: (H1 i) (H2 i) => {H1 H2} H1 H2.
  exact: (SSAVS.Lemmas.not_mem_union2 H1 H2).
Qed.

Lemma svar_notin_union v vs1 vs2 :
  svar_notin v (SSAVS.union vs1 vs2) <-> (svar_notin v vs1 /\ svar_notin v vs2).
Proof.
  split=> H.
  - exact: (conj (svar_notin_union1 H) (svar_notin_union2 H)).
  - case: H => H1 H2. exact: (svar_notin_union3 H1 H2).
Qed.

Lemma svar_notin_add1 v x vs :
  svar_notin v (SSAVS.add x vs) -> v != svar x.
Proof.
  destruct x as [x i] => /= H. move: (H i) => {H} H.
  move: (SSAVS.Lemmas.not_mem_add1 H) => {H}. move=> [H _]; apply/negP => Heq.
  apply: H. rewrite (eqP Heq); exact: eqxx.
Qed.

Lemma svar_notin_add2 v x vs :
  svar_notin v (SSAVS.add x vs) -> svar_notin v vs.
Proof.
  move=> H i. move: (H i) => {H} H. move: (SSAVS.Lemmas.not_mem_add1 H) => {H}.
  move=> [_ H]; exact: H.
Qed.

Lemma svar_notin_add v x vs :
  svar_notin v (SSAVS.add x vs) <-> (v != svar x /\ svar_notin v vs).
Proof.
  split.
  - move=> H; exact: (conj (svar_notin_add1 H) (svar_notin_add2 H)).
  - move=> [H1 H2]. move=> i. apply/negP=> H. case/SSAVS.Lemmas.mem_add1: H.
    + case: x H1 => /= xn vi H1 /eqP [] Hv Hi. subst. rewrite eqxx in H1.
      discriminate.
    + apply/negP. exact: (H2 i).
Qed.

Lemma svar_notin_replace v vs1 vs2 :
  SSAVS.Equal vs1 vs2 -> svar_notin v vs1 -> svar_notin v vs2.
Proof.
  move=> H H1 x. rewrite -H. exact: H1.
Qed.

Lemma svar_notin_subset v vs1 vs2 :
  SSAVS.subset vs1 vs2 -> svar_notin v vs2 -> svar_notin v vs1.
Proof.
  move=> H H2 x. apply/negP => H1. move: (SSAVS.Lemmas.mem_subset H1 H) => Hmem.
  move/negP: (H2 x). apply. exact: Hmem.
Qed.

Ltac simpl_svar_notin :=
  repeat
    match goal with
    | H : svar_notin _ (SSAVS.add _ _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        move/svar_notin_add: H => [H1 H2]
    | H : svar_notin _ (SSAVS.union _ _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        move/svar_notin_union: H => [H1 H2]
    end.

Ltac dp_svar_notin :=
  repeat
    match goal with
    | H : ?e |- ?e => assumption
    | |- svar_notin _ SSAVS.empty =>
        exact: svar_notin_empty
    | H : svar_notin _ (SSAVS.singleton _) |- _ =>
        move/svar_notin_singleton: H => H
    | H : svar_notin _ (SSAVS.add _ _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        move/svar_notin_add: H => [H1 H2]
    | H : svar_notin _ (SSAVS.union _ _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        move/svar_notin_union: H => [H1 H2]
    | |- svar_notin _ (SSAVS.singleton _) =>
        apply/svar_notin_singleton
    | |- svar_notin _ (SSAVS.add _ _) =>
        apply/svar_notin_add; split
    | |- svar_notin _ (SSAVS.union _ _) =>
        apply/svar_notin_union; split
    | H1 : is_true (SSAVS.subset ?s1 ?s2), H2 : svar_notin ?v ?s2 |-
        svar_notin ?v ?s1 =>
        exact: (svar_notin_subset H1 H2)
    end.


(** Generate new SSA variables *)

From ssrlib Require Import Nats.

Definition max_svar (vs : SSAVS.t) : VarOrder.t :=
  match SSAVS.max_elt vs with
  | Some v => svar v
  | None => 0%N
  end.

Definition new_svar (vs : SSAVS.t) : VarOrder.t :=
  N.succ (max_svar vs).

Lemma N_ltb_succ v : (v <? N.succ v)%N.
Proof.
  apply: (proj2 (N.ltb_lt v (N.succ v))). exact: N.lt_succ_diag_r.
Qed.

Lemma V_ltb_succ v i j : SSAVarOrder.ltn (v, j) ((N.succ v), i).
Proof.
  rewrite /SSAVarOrder.ltn /SSAVarOrder.M.ltn /VarOrder.ltn /NOrderMinimal.ltn /=.
  rewrite N_ltb_succ. exact: is_true_true.
Qed.

Lemma new_svar_notin vs : svar_notin (new_svar vs) vs.
Proof.
  rewrite /new_svar /max_svar. set x := SSAVS.max_elt vs.
  have: SSAVS.max_elt vs = x by reflexivity. case x.
  - move=> v Hmax i. apply/negP => Hmem. apply: (SSAVS.Lemmas.max_elt2 Hmax Hmem).
    exact: V_ltb_succ.
  - move=> Hnone i. apply: SSAVS.Lemmas.is_empty_mem.
    exact: (SSAVS.Lemmas.max_elt3 Hnone).
Qed.
