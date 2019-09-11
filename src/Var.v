
(** * Variables *)

From Coq Require Import FMaps FSets ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype.
From ssrlib Require Import SsrOrdered FMaps FSets ZAriths.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Definition var : Set := N.

Module VarOrder <: SsrOrderedWithDefaultSucc.
  Include NOrder.
  Definition succ := N.succ.
  Lemma ltn_succ : forall (x : t), ltn x (succ x).
  Proof.
    move=> x. apply/N.ltb_lt. exact: N.lt_succ_diag_r.
  Qed.
  Definition default := N0.
End VarOrder.



(* Variable sets and maps. *)

Module VS := FSets.MakeTreeSetWithNew VarOrder.

Module VM := FMaps.MakeTreeMapWithNew VarOrder.



(** Variables for SSA *)

From ssrlib Require Import SsrOrdered.

Module SSAVarOrder := MakeProdOrdered VarOrder NOrder.

Module SSAVS := FSets.MakeTreeSet SSAVarOrder.

Module SSAVSLemmas := FSetLemmas SSAVS.

Definition svar (x : SSAVarOrder.t) := fst x.

Definition sidx (x : SSAVarOrder.t) := snd x.

Hint Unfold svar sidx.

Definition svar_notin v vs : Prop := forall i, ~~ SSAVS.mem (v, i) vs.

Lemma svar_notin_singleton1 v x :
  svar_notin v (SSAVS.singleton x) -> v != svar x.
Proof.
  destruct x as [x i]. move=> /= H; move: (SSAVSLemmas.not_mem_singleton1 (H i)).
  move=> Hne; apply/negP => Heq; apply: Hne. rewrite (eqP Heq).
  exact: SSAVS.E.eq_refl.
Qed.

Lemma svar_notin_singleton2 v x :
  v != svar x -> svar_notin v (SSAVS.singleton x).
Proof.
  move/negP=> Hne i. apply/negP => Heq; apply: Hne.
  move: (SSAVSLemmas.mem_singleton1 Heq) => {Heq}. destruct x as [x j] => /=.
  move/eqP => [Hv Hi]. by rewrite Hv.
Qed.

Lemma svar_notin_union1 v vs1 vs2 :
  svar_notin v (SSAVS.union vs1 vs2) -> svar_notin v vs1.
Proof.
  move=> H i. move: (H i) => {H} H. exact: (proj1 (SSAVSLemmas.not_mem_union1 H)).
Qed.

Lemma svar_notin_union2 v vs1 vs2 :
  svar_notin v (SSAVS.union vs1 vs2) -> svar_notin v vs2.
Proof.
  move=> H i. move: (H i) => {H} H. exact: (proj2 (SSAVSLemmas.not_mem_union1 H)).
Qed.

Lemma svar_notin_union3 v vs1 vs2 :
  svar_notin v vs1 -> svar_notin v vs2 ->
  svar_notin v (SSAVS.union vs1 vs2).
Proof.
  move=> H1 H2 i. move: (H1 i) (H2 i) => {H1 H2} H1 H2.
  exact: (SSAVSLemmas.not_mem_union2 H1 H2).
Qed.

Lemma svar_notin_add1 v x vs :
  svar_notin v (SSAVS.add x vs) -> v != svar x.
Proof.
  destruct x as [x i] => /= H. move: (H i) => {H} H.
  move: (SSAVSLemmas.not_mem_add1 H) => {H}. move=> [H _]; apply/negP => Heq.
  apply: H. rewrite (eqP Heq); exact: eqxx.
Qed.

Lemma svar_notin_add2 v x vs :
  svar_notin v (SSAVS.add x vs) -> svar_notin v vs.
Proof.
  move=> H i. move: (H i) => {H} H. move: (SSAVSLemmas.not_mem_add1 H) => {H}.
  move=> [_ H]; exact: H.
Qed.

Lemma svar_notin_replace v vs1 vs2 :
  SSAVS.Equal vs1 vs2 -> svar_notin v vs1 -> svar_notin v vs2.
Proof.
  move=> H H1 x. rewrite -H. exact: H1.
Qed.

Lemma svar_notin_subset v vs1 vs2 :
  SSAVS.subset vs1 vs2 -> svar_notin v vs2 -> svar_notin v vs1.
Proof.
  move=> H H2 x. apply/negP => H1. move: (SSAVSLemmas.mem_subset H1 H) => Hmem.
  move/negP: (H2 x). apply. exact: Hmem.
Qed.



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
  - move=> v Hmax i. apply/negP => Hmem. apply: (SSAVSLemmas.max_elt2 Hmax Hmem).
    exact: V_ltb_succ.
  - move=> Hnone i. apply: SSAVSLemmas.is_empty_mem.
    exact: (SSAVSLemmas.max_elt3 Hnone).
Qed.
