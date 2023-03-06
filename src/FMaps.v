
(** * Some auxiliary lemmas for FMaps. *)

(** These lemmas can be proven by facts in Coq.FSets.FMapFacts. *)

From Coq Require Import FunInd FMaps FMapAVL OrderedType.
From mathcomp Require Import ssreflect ssrbool eqtype seq.
From ssrlib Require Import Types SsrOrder Lists FSets Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* Finite maps of elements with decidable equality *)

Module Type SsrFMap <: FMapInterface.S.
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
End SsrFMap.



(* Extra lemmas for Coq finite maps *)

Module FMapLemmas (M : FMapInterface.S).

  Module F := Facts(M).
  Module OP := OrdProperties(M).
  Include F.
  Include OP.

  Section FMapLemmas.

    Variable elt elt' : Type.

    Lemma memP k (m : M.t elt) : reflect (M.In k m) (M.mem k m).
    Proof.
      case H: (M.mem k m).
      - apply: ReflectT. exact: (M.mem_2 H).
      - apply: ReflectF. move=> Hin; move: (M.mem_1 Hin). rewrite H; discriminate.
    Qed.

    Lemma find_some_mapsto (m : M.t elt) x e : M.find x m = Some e -> M.MapsTo x e m.
    Proof.
      exact: (proj2 (F.find_mapsto_iff m x e)).
    Qed.

    Lemma mapsto_find_some (m : M.t elt) x e : M.MapsTo x e m -> M.find x m = Some e.
    Proof.
      exact: (proj1 (F.find_mapsto_iff m x e)).
    Qed.

    Lemma find_none_not_in (m : M.t elt) x : M.find x m = None -> ~ M.In x m.
    Proof.
      exact: (proj2 (F.not_find_in_iff m x)).
    Qed.

    Lemma not_in_find_none (m : M.t elt) x : ~ M.In x m -> M.find x m = None.
    Proof.
      exact: (proj1 (F.not_find_in_iff m x)).
    Qed.

    Lemma find_some_in (m : M.t elt) x e : M.find x m = Some e -> M.In x m.
    Proof.
      move=> H; exists e. exact: (find_some_mapsto H).
    Qed.

    Lemma in_find_some (m : M.t elt) x : M.In x m -> exists e, M.find x m = Some e.
    Proof.
      move=> [e H]. exists e. exact: (mapsto_find_some H).
    Qed.

    Lemma find_none_not_mem (m : M.t elt) x : M.find x m = None -> M.mem x m = false.
    Proof.
      move=> H. apply/memP. exact: (find_none_not_in H).
    Qed.

    Lemma not_mem_find_none (m : M.t elt) x : ~~ M.mem x m -> M.find x m = None.
    Proof.
      move/memP=> H. exact: (not_in_find_none H).
    Qed.

    Lemma find_some_mem (m : M.t elt) x e : M.find x m = Some e -> M.mem x m.
    Proof.
      move=> H. apply/memP. exact: (find_some_in H).
    Qed.

    Lemma mem_find_some (m : M.t elt) x : M.mem x m -> exists e, M.find x m = Some e.
    Proof.
      move/memP=> H. exact: (in_find_some H).
    Qed.



    Lemma find_add_eq {m : M.t elt} {x y : M.key} {e : elt} :
      M.E.eq x y -> M.find x (M.add y e m) = Some e.
    Proof.
      move=> Hxy. apply: F.add_eq_o. apply: M.E.eq_sym. exact: Hxy.
    Qed.

    Lemma find_add_neq {m : M.t elt} {x y : M.key} {e : elt} :
      ~(M.E.eq x y) -> M.find x (M.add y e m) = M.find x m.
    Proof.
      move=> Hne. apply: F.add_neq_o. move=> Heq; apply: Hne; apply: M.E.eq_sym.
      exact: Heq.
    Qed.

    Lemma mem_add_eq {m : M.t elt} {x y : M.key} {e : elt} :
      M.E.eq x y -> M.mem x (M.add y e m).
    Proof.
      move=> Hxy. apply: F.add_eq_b. apply: M.E.eq_sym. exact: Hxy.
    Qed.

    Lemma mem_add_neq {m : M.t elt} {x y : M.key} {e : elt} :
      ~(M.E.eq x y) -> M.mem x (M.add y e m) = M.mem x m.
    Proof.
      move=> Hne. apply: F.add_neq_b. move=> Heq; apply: Hne; apply: M.E.eq_sym.
      exact: Heq.
    Qed.

    Lemma find_some_map {f : elt -> elt'} {m : M.t elt} {x : M.key} {e : elt} :
      M.find x m = Some e ->
      M.find x (M.map f m) = Some (f e).
    Proof.
      move=> H. rewrite F.map_o. rewrite /option_map. rewrite H. reflexivity.
    Qed.

    Lemma find_none_map {f : elt -> elt'} {m : M.t elt} {x : M.key} :
      M.find x m = None ->
      M.find x (M.map f m) = None.
    Proof.
      move=> H. rewrite F.map_o. rewrite /option_map. rewrite H. reflexivity.
    Qed.

    Lemma find_map_some (f : elt -> elt') (m : M.t elt) (x : M.key) (e : elt') :
      M.find x (M.map f m) = Some e ->
      exists a, e = f a /\ M.find x m = Some a.
    Proof.
      move=> H. move: (M.find_2 H) => {H} H. case: (F.map_mapsto_iff m x e f) => Hf _.
      move: (Hf H) => {H Hf} [] => a [Hea Hxa]. exists a. split.
      - assumption.
      - apply: M.find_1. assumption.
    Qed.

    Lemma find_map_none (f : elt -> elt') (m : M.t elt) (x : M.key) :
      M.find x (M.map f m) = None ->
      M.find x m = None.
    Proof.
      rewrite F.map_o. rewrite /option_map. case: (M.find x m).
      - discriminate.
      - reflexivity.
    Qed.

    Lemma mem_map (f : elt -> elt') (m : M.t elt) (x : M.key) :
      M.mem x (M.map f m) = M.mem x m.
    Proof.
      exact: F.map_b.
    Qed.

    Lemma empty_mem (m : M.t elt) (x : M.key) :
      M.Empty m -> M.mem x m -> False.
    Proof.
      move=> Hempty Hmem. move/memP: Hmem => [e Hmapsto]. move: (Hempty x e); apply.
      exact: Hmapsto.
    Qed.

    Lemma find_eq_mem_eq (m1 m2 : M.t elt) (x1 x2 : M.key) :
      M.find x1 m1 = M.find x2 m2 -> M.mem x1 m1 = M.mem x2 m2.
    Proof.
      case Hfind1: (M.find x1 m1); move=> Hfind2;
      rewrite mem_find_b mem_find_b Hfind1 -Hfind2; reflexivity.
    Qed.

    Lemma Empty_in (m : M.t elt) (x : M.key) :
      M.Empty m -> ~ (M.In x m).
    Proof.
      move=> Hemp Hin. case: Hin => [v Hmapsto]. exact: (Hemp x v Hmapsto).
    Qed.

    Lemma Empty_mem (m : M.t elt) (x : M.key) :
      M.Empty m -> ~~ M.mem x m.
    Proof.
      move=> Hemp. apply/negP => Hmem. move/memP: Hmem. exact: Empty_in.
    Qed.

    Lemma Empty_find (m : M.t elt) (x : M.key) :
      M.Empty m -> M.find x m = None.
    Proof.
      move=> Hemp. move: (not_find_in_iff m x) => [H _]. apply: H => H.
      exact: (Empty_in Hemp H).
    Qed.

    Lemma find_some_none_neq (m : M.t elt) (x y : M.key) (v : elt) :
      M.find x m = Some v -> M.find y m = None ->
      ~ (M.E.eq x y).
    Proof.
      move=> Hx Hy Heq. rewrite (F.find_o _ Heq) in Hx. rewrite Hx in Hy. discriminate.
    Qed.

    Lemma Add_mem_add x k e (m m' : M.t elt) :
      OP.P.Add k e m m' ->
      M.mem x m' = M.mem x (M.add k e m).
    Proof.
      move=> Hadd. move: (Hadd x). rewrite 2!mem_find_b.
      move=> ->. reflexivity.
    Qed.

    Lemma Add_in k e (m m' : M.t elt) :
      OP.P.Add k e m m' -> M.In k m'.
    Proof.
      move=> Hadd. move: (Hadd k). rewrite (add_eq_o _ _ (M.E.eq_refl k)).
      exact: find_some_in.
    Qed.

    Lemma in_Add_in k e k' (m m' : M.t elt) :
      M.In k' m -> OP.P.Add k e m m' -> M.In k' m'.
    Proof.
      move=> Hin Hadd. case: (M.E.eq_dec k k').
      - move=> Heq. rewrite -Heq. exact: (Add_in Hadd).
      - move=> Hneq. apply/memP. rewrite (Add_mem_add k' Hadd).
        rewrite (add_neq_b _ _ Hneq). apply/memP. exact: Hin.
    Qed.

    Lemma mem_combine_cons (x : M.key) k (keys : list M.key) v (vals : list elt) :
      (M.mem x (OP.P.of_list (List.combine (k::keys) (v::vals)))) =
       ((eqb k x) || (M.mem x (OP.P.of_list (List.combine keys vals)))).
    Proof.
      rewrite /= /OP.P.uncurry /=. rewrite /eqb. case: (M.E.eq_dec k x).
      - move=> Heq. rewrite (F.add_eq_b _ _ Heq) orTb. reflexivity.
      - move=> Hneq. rewrite (F.add_neq_b _ _ Hneq) orFb. reflexivity.
    Qed.

    Lemma mem_combine_in (x : M.key) (keys : list M.key) (vals : list elt) :
      M.mem x (OP.P.of_list (List.combine keys vals)) ->
      SetoidList.InA M.E.eq x keys.
    Proof.
      elim: keys vals.
      - move=> /= vals Hmem. rewrite empty_a in Hmem. discriminate.
      - move=> key_hd key_tl IH. case.
        + move=> /= Hmem. rewrite empty_a in Hmem. discriminate.
        + move=> val_hd val_tl Hmem. rewrite mem_combine_cons in Hmem.
          move/orP: Hmem; case.
          * rewrite /eqb /=. case: (P.F.eq_dec key_hd x); last by discriminate.
            move=> H _. apply: InA_cons_hd. apply: M.E.eq_sym. exact: H.
          * move=> H. apply: InA_cons_tl. exact: (IH _ H).
    Qed.

    Lemma add_diag (x : M.key) (e : elt) (m : M.t elt) :
      M.Equal (M.add x e (M.add x e m)) (M.add x e m).
    Proof.
      move=> y. case: (M.E.eq_dec y x).
      - move=> Hyx. rewrite !(find_add_eq Hyx). reflexivity.
      - move=> Hyx. rewrite !(find_add_neq Hyx). reflexivity.
    Qed.

    Lemma add_same (x : M.key) (e : elt) (m : M.t elt) :
      M.find x m = Some e -> M.Equal (M.add x e m) m.
    Proof.
      move=> Hfind y. case: (M.E.eq_dec y x) => Hyx.
      - rewrite (find_add_eq Hyx). rewrite -Hfind Hyx. reflexivity.
      - rewrite (find_add_neq Hyx). reflexivity.
    Qed.

    Lemma add_comm (x1 x2 : M.key) (e1 e2 : elt) (m : M.t elt) :
      ~ M.E.eq x1 x2 ->
      M.Equal (M.add x1 e1 (M.add x2 e2 m)) (M.add x2 e2 (M.add x1 e1 m)).
    Proof.
      move=> Hne y. case: (M.E.eq_dec y x1); case: (M.E.eq_dec y x2).
      - move=> Heq2 Heq1. apply: False_ind. apply: Hne. rewrite -Heq1 -Heq2.
        reflexivity.
      - move=> Hne2 Heq1. rewrite (find_add_eq Heq1) (find_add_neq Hne2).
        rewrite (find_add_eq Heq1). reflexivity.
      - move=> Heq2 Hne1. rewrite (find_add_neq Hne1) !(find_add_eq Heq2).
        reflexivity.
      - move=> Hne2 Hne1. rewrite (find_add_neq Hne1) !(find_add_neq Hne2).
        rewrite (find_add_neq Hne1). reflexivity.
    Qed.

    Lemma add2_equal k1 k2 v (m1 m2 : M.t elt) :
      M.E.eq k1 k2 ->
      M.Equal m1 m2 ->
      M.Equal (M.add k1 v m1) (M.add k2 v m2).
    Proof. move=> Heq. by apply: F.add_m. Qed.

  End FMapLemmas.

  Section Proper.

    Variable elt elt' : Type.

    Variable f : elt -> elt'.

    Global Instance add_f_proper :
      Proper (M.E.eq ==> eq ==> M.Equal ==> M.Equal)
             (fun (k : M.key) (e : elt) (m : M.t elt') => M.add k (f e) m).
    Proof.
      move=> x1 x2 Heqx. move=> y1 y2 Heqy. move=> m1 m2 Heqm.
      have Heq: (f y1 = f y2) by rewrite Heqy. exact: (F.add_m Heqx Heq Heqm).
    Qed.

    Lemma add_f_transpose_neqkey :
      OP.P.transpose_neqkey
        M.Equal
        (fun (k : M.key) (e : elt) (m : M.t elt') => M.add k (f e) m).
    Proof.
      move=> k1 k2 e1 e2 m Hneq x. rewrite 4!add_o.
      case: (M.E.eq_dec k1 x); case: (M.E.eq_dec k2 x); try reflexivity.
      move=> Heq2 Heq1. move: (M.E.eq_sym Heq2) => {Heq2} Heq2.
      move: (M.E.eq_trans Heq1 Heq2) => Heq. apply: False_ind; apply: Hneq.
      exact: Heq.
    Qed.

  End Proper.

  Section Split.

    Variable elt elt' : Type.

    Definition split (m : M.t (elt * elt')) : M.t elt * M.t elt' :=
      (M.fold (fun k e m1 => M.add k (fst e) m1) m (M.empty elt),
       M.fold (fun k e m2 => M.add k (snd e) m2) m (M.empty elt')).

    Lemma mem_split1 (m : M.t (elt * elt')) (x : M.key) :
      M.mem x m = M.mem x (fst (split m)).
    Proof.
      rewrite /split /=. move: m. eapply OP.P.map_induction.
      - move=> m Hemp. rewrite (OP.P.fold_Empty (Equal_ST elt) _ _ Hemp).
        rewrite empty_a. rewrite (negbTE (Empty_mem x Hemp)). reflexivity.
      - move=> m m' IH y e Hin Hadd. rewrite (Add_mem_add _ Hadd).
        rewrite (OP.P.fold_Add (Equal_ST elt)
                               (add_f_proper fst)
                               (add_f_transpose_neqkey fst) _ Hin Hadd).
        case: (M.E.eq_dec y x).
        + move=> Heq. rewrite 2!(add_eq_b _ _ Heq). reflexivity.
        + move=> Hneq. rewrite 2!(add_neq_b _ _ Hneq). exact: IH.
    Qed.

    Lemma mem_split2 (m : M.t (elt * elt')) (x : M.key) :
      M.mem x m = M.mem x (snd (split m)).
    Proof.
      rewrite /split /=. move: m. eapply OP.P.map_induction.
      - move=> m Hemp. rewrite (OP.P.fold_Empty (Equal_ST elt') _ _ Hemp).
        rewrite empty_a. rewrite (negbTE (Empty_mem x Hemp)). reflexivity.
      - move=> m m' IH y e Hin Hadd. rewrite (Add_mem_add _ Hadd).
        rewrite (OP.P.fold_Add (Equal_ST elt')
                               (add_f_proper snd)
                               (add_f_transpose_neqkey snd) _ Hin Hadd).
        case: (M.E.eq_dec y x).
        + move=> Heq. rewrite 2!(add_eq_b _ _ Heq). reflexivity.
        + move=> Hneq. rewrite 2!(add_neq_b _ _ Hneq). exact: IH.
    Qed.

    Lemma find_split1_none (m : M.t (elt * elt')) (x : M.key) :
      M.find x m = None ->
      M.find x (fst (split m)) = None.
    Proof.
      rewrite /split /=. move: m. apply: OP.P.map_induction.
      - move=> m Hemp. rewrite (OP.P.fold_Empty (Equal_ST elt) _ _ Hemp).
        rewrite empty_o. reflexivity.
      - move=> m m' IH y e Hin Hadd. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt)
                               (add_f_proper fst)
                               (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + discriminate.
        + move=> _ H. exact: (IH H).
    Qed.

    Lemma find_split2_none (m : M.t (elt * elt')) (x : M.key) :
      M.find x m = None ->
      M.find x (snd (split m)) = None.
    Proof.
      rewrite /split /=. move: m. apply: OP.P.map_induction.
      - move=> m Hemp. rewrite (OP.P.fold_Empty (Equal_ST elt') _ _ Hemp).
        rewrite empty_o. reflexivity.
      - move=> m m' IH y e Hin Hadd. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt')
                               (add_f_proper snd)
                               (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + discriminate.
        + move=> _ H. exact: (IH H).
    Qed.

    Lemma find_split1_some (m : M.t (elt * elt')) (x : M.key) e1 e2 :
      M.find x m = Some (e1, e2) ->
      M.find x (fst (split m)) = Some e1.
    Proof.
      rewrite /split /=. move: m e1 e2. apply: OP.P.map_induction.
      - move=> m Hemp e1 e2. rewrite (Empty_find _ Hemp). discriminate.
      - move=> m m' IH y e Hin Hadd e1 e2. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt)
                               (add_f_proper fst)
                               (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + move=> Heq [] He. by rewrite He.
        + move=> Hneq H. exact: (IH _ _ H).
    Qed.

    Lemma find_split2_some (m : M.t (elt * elt')) (x : M.key) e1 e2 :
      M.find x m = Some (e1, e2) ->
      M.find x (snd (split m)) = Some e2.
    Proof.
      rewrite /split /=. move: m e1 e2. apply: OP.P.map_induction.
      - move=> m Hemp e1 e2. rewrite (Empty_find _ Hemp). discriminate.
      - move=> m m' IH y e Hin Hadd e1 e2. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt')
                               (add_f_proper snd)
                               (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + move=> Heq [] He. by rewrite He.
        + move=> Hneq H. exact: (IH _ _ H).
    Qed.

    Lemma split1_find_none (m : M.t (elt * elt')) (x : M.key) :
      M.find x (fst (split m)) = None ->
      M.find x m = None.
    Proof.
      rewrite /split /=. move: m. apply: OP.P.map_induction.
      - move=> m Hemp _. exact: (Empty_find _ Hemp).
      - move=> m m' IH y e Hin Hadd. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt)
                               (add_f_proper fst)
                               (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + discriminate.
        + move=> _ H. exact: (IH H).
    Qed.

    Lemma split2_find_none (m : M.t (elt * elt')) (x : M.key) :
      M.find x (snd (split m)) = None ->
      M.find x m = None.
    Proof.
      rewrite /split /=. move: m. apply: OP.P.map_induction.
      - move=> m Hemp _. exact: (Empty_find _ Hemp).
      - move=> m m' IH y e Hin Hadd. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt')
                               (add_f_proper snd)
                               (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + discriminate.
        + move=> _ H. exact: (IH H).
    Qed.

    Lemma split1_find_some (m : M.t (elt * elt')) (x : M.key) e1 :
      M.find x (fst (split m)) = Some e1 ->
      exists e2, M.find x m = Some (e1, e2).
    Proof.
      rewrite /split /=. move: m e1. apply: OP.P.map_induction.
      - move=> m Hemp e1. rewrite (OP.P.fold_Empty (Equal_ST elt) _ _ Hemp).
        rewrite empty_o. discriminate.
      - move=> m m' IH y e Hin Hadd e1. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt)
                               (add_f_proper fst)
                               (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + move=> Heq [] He. exists (snd e). rewrite -He -surjective_pairing.
          reflexivity.
        + move=> Hneq H. exact: (IH _ H).
    Qed.

    Lemma split2_find_some (m : M.t (elt * elt')) (x : M.key) e2 :
      M.find x (snd (split m)) = Some e2 ->
      exists e1, M.find x m = Some (e1, e2).
    Proof.
      rewrite /split /=. move: m e2. apply: OP.P.map_induction.
      - move=> m Hemp e2. rewrite (OP.P.fold_Empty (Equal_ST elt') _ _ Hemp).
        rewrite empty_o. discriminate.
      - move=> m m' IH y e Hin Hadd e2. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt')
                               (add_f_proper snd)
                               (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 2!add_o. case: (M.E.eq_dec y x).
        + move=> Heq [] He. exists (fst e). rewrite -He -surjective_pairing.
          reflexivity.
        + move=> Hneq H. exact: (IH _ H).
    Qed.

    Lemma split_find_some (m : M.t (elt * elt')) (x : M.key) e1 e2 :
      M.find x (fst (split m)) = Some e1 ->
      M.find x (snd (split m)) = Some e2 ->
      M.find x m = Some (e1, e2).
    Proof.
      rewrite /split /=. move: m e1 e2. apply: OP.P.map_induction.
      - move=> m Hemp e1 e2. rewrite (OP.P.fold_Empty (Equal_ST elt) _ _ Hemp).
        rewrite empty_o. discriminate.
      - move=> m m' IH y e Hin Hadd e1 e2. rewrite (Hadd x).
        rewrite (OP.P.fold_Add (Equal_ST elt)
                               (add_f_proper fst)
                               (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite (OP.P.fold_Add (Equal_ST elt')
                               (add_f_proper snd)
                               (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 3!add_o. case: (M.E.eq_dec y x).
        + move=> Heq [] He1 [] He2. rewrite -He1 -He2 -surjective_pairing.
          reflexivity.
        + move=> Hneq H1 H2. exact: (IH _ _ H1 H2).
    Qed.

  End Split.

  Section Submap.

    Unset Implicit Arguments.

    Context {elt : Type}.

    Definition submap (m m' : M.t elt) :=
      forall {k v}, M.find k m = Some v -> M.find k m' = Some v.

    Lemma submap_refl (m : M.t elt) : submap m m.
    Proof. move=> k v Hfind. exact: Hfind. Qed.

    Lemma submap_trans {m2 m1 m3 : M.t elt} :
      submap m1 m2 -> submap m2 m3 -> submap m1 m3.
    Proof.
      move=> H12 H23 k v Hf1. apply: H23. apply: H12. exact: Hf1.
    Qed.

    Lemma submap_none_add {m1 m2 : M.t elt} {k : M.key} (e : elt) :
      submap m1 m2 -> M.find k m1 = None -> submap m1 (M.add k e m2).
    Proof.
      move=> Hsub Hfind k' v' Hfind'. rewrite add_o. case: (P.F.eq_dec k k').
      - move=> Heq. rewrite (F.find_o m1 Heq) in Hfind. rewrite Hfind in Hfind'.
        discriminate.
      - move=> Hneq. exact: (Hsub k' v' Hfind').
    Qed.

    Lemma submap_not_mem_add {m1 m2 : M.t elt} {k : M.key} (e : elt) :
      submap m1 m2 -> ~~ M.mem k m1 -> submap m1 (M.add k e m2).
    Proof.
      move=> Hsub Hmem. exact: (submap_none_add _ Hsub (not_mem_find_none Hmem)).
    Qed.

    Lemma submap_some_add {m1 m2 : M.t elt} {k : M.key} {e : elt} :
      submap m1 m2 -> M.find k m1 = Some e -> submap m1 (M.add k e m2).
    Proof.
      move=> Hsub Hfind k' v' Hfind'. rewrite add_o. case: (P.F.eq_dec k k').
      - move=> Heq. rewrite (F.find_o m1 Heq) in Hfind. rewrite Hfind in Hfind'.
        exact: Hfind'.
      - move=> Hneq. exact: (Hsub k' v' Hfind').
    Qed.

    Lemma submap_add_diag {m : M.t elt} {k : M.key} (e : elt) :
      ~~ M.mem k m -> submap m (M.add k e m).
    Proof.
      move=> Hmem. apply: (submap_not_mem_add _ _ Hmem). exact: submap_refl.
    Qed.

    Lemma submap_mem {m1 m2 : M.t elt} {k : M.key} :
      submap m1 m2 -> M.mem k m1 -> M.mem k m2.
    Proof.
      move=> Hsub Hmem1. move: (mem_find_some Hmem1) => {Hmem1} [e Hfind1].
      move: (Hsub k e Hfind1) => Hfind2. exact: (find_some_mem Hfind2).
    Qed.

    Lemma submap_add_find {m1 m2 : M.t elt} {k : M.key} {e : elt} :
      submap (M.add k e m1) m2 -> M.find k m2 = Some e.
    Proof.
      move=> H. apply: (H k e). rewrite (find_add_eq (M.E.eq_refl k)). reflexivity.
    Qed.

    Lemma submap_add_find_none {m1 m2 : M.t elt} {k : M.key} {e : elt} :
      submap (M.add k e m1) m2 -> M.find k m1 = None -> submap m1 m2.
    Proof.
      move=> H Hfindk1 x ex Hfindx1. apply: H. case: (M.E.eq_dec x k).
      - move=> Heq. apply: False_ind. rewrite (F.find_o _ Heq) Hfindk1 in Hfindx1.
        discriminate.
      - move=> Hne. rewrite (find_add_neq Hne). assumption.
    Qed.

    Lemma submap_add_not_mem {m1 m2 : M.t elt} {k : M.key} {e : elt} :
      submap (M.add k e m1) m2 -> ~~ M.mem k m1 -> submap m1 m2.
    Proof.
      move=> H Hmem. move: (not_mem_find_none Hmem) => Hfind.
      exact: (submap_add_find_none H Hfind).
    Qed.

    Lemma submap_Equal {m1 m2 : M.t elt} :
      submap m1 m2 -> submap m2 m1 -> M.Equal m1 m2.
    Proof.
      move=> Hsub12 Hsub21. move=> x. case Hfind1: (M.find x m1).
      - rewrite (Hsub12 _ _ Hfind1). reflexivity.
      - case Hfind2: (M.find x m2).
        + rewrite (Hsub21 _ _ Hfind2) in Hfind1. discriminate.
        + reflexivity.
    Qed.

    Lemma Equal_submap {m1 m2 : M.t elt} : M.Equal m1 m2 -> submap m1 m2.
    Proof.
      move=> Heq x v Hfind. rewrite (Heq x) in Hfind. exact: Hfind.
    Qed.

    Lemma submap_add {te1 te2: M.t elt} x v :
      submap te1 te2 ->
      submap (M.add x v te1) (M.add x v te2).
    Proof.
      move=> Hsm k typ. case: (M.E.eq_dec k x).
      - move=> H. by rewrite !(find_add_eq H).
      - move=> Hne. rewrite !(find_add_neq Hne). exact: Hsm.
    Qed.

    Set Implicit Arguments.

  End Submap.

  Module EFacts := OrderedType.OrderedTypeFacts M.E.

  Section MaxMin.

    Variable elt : Type.

    Lemma eqb_eq k1 k2 : eqb k1 k2 -> M.E.eq k1 k2.
    Proof.
      rewrite /eqb. case: P.F.eq_dec.
      - move=> H _; exact: H.
      - move=> _ H. discriminate.
    Qed.

    Lemma eqb_key_refl : forall (k : M.key), eqb k k.
    Proof.
      move=> k. rewrite /eqb. case: (P.F.eq_dec k k); first by done.
      move=> H; apply: False_ind; apply: H. exact: M.E.eq_refl.
    Qed.

    (* max_key *)

    Definition max_opt (k : M.key) (o : option M.key) : M.key :=
      match o with
      | None => k
      | Some k' => match M.E.compare k k' with
                   | LT _ => k'
                   | _ => k
                   end
      end.

    Lemma max_opt_cases k x o :
      max_opt k o = x ->
      (o = None /\ x = k) \/
      (exists k', o = Some k' /\ M.E.lt k k' /\ x = k') \/
      (exists k', o = Some k' /\ ~(M.E.lt k k') /\ x = k).
    Proof.
      case: o=> /=.
      - move=> k'. dcase (M.E.compare k k'). case.
        + move=> Hlt Hcomp Hx. right; left. exists k'. rewrite -Hx.
          repeat split; try reflexivity. exact: Hlt.
        + move=> Heq Hcomp Hx. right; right. exists k'. rewrite -Hx.
          repeat split; try reflexivity. exact: (EFacts.eq_not_lt Heq).
        + move=> Hgt Hcomp Hx. right; right. exists k'. rewrite -Hx.
          repeat split; try reflexivity. move=> Hlt. move: (M.E.lt_trans Hgt Hlt).
          exact: (@EFacts.lt_antirefl k').
      - move=> Hx. rewrite -Hx. by left.
    Qed.

    Lemma max_opt_none k : max_opt k None = k.
    Proof.
      reflexivity.
    Qed.

    Lemma max_opt_lt k k' : M.E.lt k k' -> max_opt k (Some k') = k'.
    Proof.
      move=> Hlt /=. move: (EFacts.elim_compare_lt Hlt)=> {Hlt} [Hlt ->].
      reflexivity.
    Qed.

    Lemma max_opt_eq k k' : M.E.eq k k' -> max_opt k (Some k') = k.
    Proof.
      move=> Heq /=. move: (EFacts.elim_compare_eq Heq) => {Heq} [Heq ->].
      reflexivity.
    Qed.

    Lemma max_opt_gt k k' : M.E.lt k' k -> max_opt k (Some k') = k.
    Proof.
      move=> Hgt /=. move: (EFacts.elim_compare_gt Hgt) => {Hgt} [Hgt ->].
      reflexivity.
    Qed.

    Lemma max_opt_not_lt_l k o x : max_opt k o = x -> ~ M.E.lt x k.
    Proof.
      move=> Hmax. case: (max_opt_cases Hmax); last case.
      - move=> [Ho Hx]. rewrite Hx. exact: (@EFacts.lt_antirefl k).
      - move=> [k' [Ho [Hlt Hx]]]. rewrite Hx => H. move: (M.E.lt_trans Hlt H).
        exact: (@EFacts.lt_antirefl k).
      - move=> [k' [Ho [Hlt Hx]]]. rewrite Hx. exact: (@EFacts.lt_antirefl k).
    Qed.

    Lemma max_opt_not_lt_r k k' x : max_opt k (Some k') = x -> ~ M.E.lt x k'.
    Proof.
      move=> Hmax. case: (max_opt_cases Hmax); last case.
      - move=> [H1 H2]; discriminate.
      - move=> [k'' [[] Hk'' [Hk Hx]]]. rewrite Hx -Hk''.
        exact: (@EFacts.lt_antirefl k').
      - move=> [k'' [[] Hk'' [Hk Hx]]]. rewrite Hx Hk''. assumption.
    Qed.

    Fixpoint max_key_elements (l : list (M.key * elt)) : option M.key :=
      match l with
      | [::] => None
      | (k, _)::tl => Some (max_opt k (max_key_elements tl))
      end.

    Definition max_key (m : M.t elt) : option M.key :=
      max_key_elements (M.elements m).

    Lemma max_key_elements_mem :
      forall (elements : seq (M.key * elt)) (k : M.key),
        max_key_elements elements = Some k ->
        existsb (fun p : M.E.t * elt => eqb k (fst p)) elements.
    Proof.
      elim => /=.
      - discriminate.
      - move=> [k_hd v_hd] tl IH k Hmax_tl /=.
        case Heqb: (eqb k k_hd); first by done. rewrite /=. apply: IH. move: Hmax_tl.
        move=> [] Hmax. case: (max_opt_cases Hmax); last case.
        + move=> [_ Hk]. rewrite Hk eqb_key_refl in Heqb. discriminate.
        + move=> [k' [Hmax_tl [Hlt Hk]]]. rewrite Hk. assumption.
        + move=> [k' [Hmax_tl [Heq Hk]]]. rewrite Hk eqb_key_refl in Heqb.
          discriminate.
    Qed.

    Lemma max_key_mem :
      forall (m : M.t elt) k, max_key m = Some k -> M.mem k m.
    Proof.
      rewrite /max_key=> m k Hmax. rewrite elements_b. move: k Hmax.
      move: (M.elements m) => {m}. exact: max_key_elements_mem.
    Qed.

    Lemma max_key_elements_none :
      forall l, max_key_elements l = None -> l = [::].
    Proof.
      case => /=.
      - reflexivity.
      - move=> [k v] tl H. discriminate.
    Qed.

    Lemma max_key_none :
      forall (m : M.t elt), max_key m = None -> M.Empty m.
    Proof.
      rewrite /max_key=> m Hmax. apply/OP.P.elements_Empty. move: Hmax.
      move: (M.elements m) => {m}. exact: max_key_elements_none.
    Qed.

    Lemma max_key_elements_not_lt :
      forall (elements : seq (M.key * elt)) (k1 k2 : M.key),
        max_key_elements elements = Some k1 ->
        existsb (fun p : M.E.t * elt => eqb k2 (fst p)) elements -> ~ M.E.lt k1 k2.
    Proof.
      elim=> /=.
      - discriminate.
      - move=> [k_hd v_hd] tl IH k1 k2 [] Hmax /=. case/orP.
        + move=> Hk2 Hlt. apply: (max_opt_not_lt_l Hmax).
          move: (eqb_eq Hk2) => {Hk2} Hk2. exact: (EFacts.lt_eq Hlt Hk2).
        + case: (max_opt_cases Hmax); last case.
          * move=> [Hmax_tl Hk1]. rewrite (max_key_elements_none Hmax_tl) /=. done.
          * move=> [k_tl [Hmax_tl [Hk_tl Hk1]]]. move=> H; apply: (IH _ _ _ H).
            rewrite Hk1; assumption.
          * move=> [k_tl [Hmax_tl [Hk_tl Hk1]]]. move=> H. move: (IH _ _ Hmax_tl H).
            move=> Hlt_tl Hlt_k1. rewrite Hk1 in Hlt_k1 => {Hmax Hk1}.
            case: (EFacts.lt_total k_hd k_tl); last case; move=> Hlt_hd.
            -- apply: Hk_tl; assumption.
            -- apply: Hlt_tl. exact: (EFacts.eq_lt (M.E.eq_sym Hlt_hd) Hlt_k1).
            -- apply: Hlt_tl. exact: (M.E.lt_trans Hlt_hd Hlt_k1).
    Qed.

    Lemma max_key_not_lt :
      forall (m : M.t elt) k1 k2,
        max_key m = Some k1 -> M.mem k2 m -> ~ M.E.lt k1 k2.
    Proof.
      rewrite /max_key=> m k1 k2. rewrite elements_b. move: k1 k2.
      move: (M.elements m) => {m}. exact: max_key_elements_not_lt.
    Qed.

    (* min_key *)

    Definition min_opt (k : M.key) (o : option M.key) : M.key :=
      match o with
      | None => k
      | Some k' => match M.E.compare k k' with
                   | GT _ => k'
                   | _ => k
                   end
      end.

    Lemma min_opt_cases k x o :
      min_opt k o = x ->
      (o = None /\ x = k) \/
      (exists k', o = Some k' /\ M.E.lt k' k /\ x = k') \/
      (exists k', o = Some k' /\ ~(M.E.lt k' k) /\ x = k).
    Proof.
      case: o=> /=.
      - move=> k'. dcase (M.E.compare k k'). case.
        + move=> Hlt Hcomp Hx. right; right; exists k'. rewrite -Hx.
          repeat split; try reflexivity. exact: (EFacts.lt_le Hlt).
        + move=> Heq Hcomp Hx. right; right; exists k'. rewrite -Hx.
          repeat split; try reflexivity. exact: (EFacts.eq_not_lt (M.E.eq_sym Heq)).
        + move=> Hgt Hcomp Hx. right; left; exists k'. rewrite -Hx.
          repeat split; try reflexivity. assumption.
      - move=> Hx. rewrite -Hx. by left.
    Qed.

    Lemma min_opt_none k : min_opt k None = k.
    Proof.
      reflexivity.
    Qed.

    Lemma min_opt_lt k k' : M.E.lt k k' -> min_opt k (Some k') = k.
    Proof.
      move=> Hlt /=. move: (EFacts.elim_compare_lt Hlt)=> {Hlt} [Hlt ->].
      reflexivity.
    Qed.

    Lemma min_opt_eq k k' : M.E.eq k k' -> min_opt k (Some k') = k.
    Proof.
      move=> Heq /=. move: (EFacts.elim_compare_eq Heq) => {Heq} [Heq ->].
      reflexivity.
    Qed.

    Lemma min_opt_gt k k' : M.E.lt k' k -> min_opt k (Some k') = k'.
    Proof.
      move=> Hgt /=. move: (EFacts.elim_compare_gt Hgt) => {Hgt} [Hgt ->].
      reflexivity.
    Qed.

    Lemma min_opt_not_lt_l k o x : min_opt k o = x -> ~ M.E.lt k x.
    Proof.
      move=> Hmin. case: (min_opt_cases Hmin); last case.
      - move=> [Ho Hx]. rewrite Hx. exact: (@EFacts.lt_antirefl k).
      - move=> [k' [Ho [Hlt Hx]]]. rewrite Hx => H. move: (M.E.lt_trans Hlt H).
        exact: (@EFacts.lt_antirefl k').
      - move=> [k' [Ho [Hlt Hx]]]. rewrite Hx. exact: (@EFacts.lt_antirefl k).
    Qed.

    Lemma min_opt_not_lt_r k k' x : min_opt k (Some k') = x -> ~ M.E.lt k' x.
    Proof.
      move=> Hmin. case: (min_opt_cases Hmin); last case.
      - move=> [H1 H2]; discriminate.
      - move=> [k'' [[] Hk'' [Hk Hx]]]. rewrite Hx -Hk''.
        exact: (@EFacts.lt_antirefl k').
      - move=> [k'' [[] Hk'' [Hk Hx]]]. rewrite Hx Hk''. assumption.
    Qed.

    Fixpoint min_key_elements (l : list (M.key * elt)) : option M.key :=
      match l with
      | [::] => None
      | (k, _)::tl => Some (min_opt k (min_key_elements tl))
      end.

    Definition min_key (m : M.t elt) : option M.key :=
      min_key_elements (M.elements m).

    Lemma min_key_elements_mem :
      forall (elements : seq (M.key * elt)) (k : M.key),
        min_key_elements elements = Some k ->
        existsb (fun p : M.E.t * elt => eqb k (fst p)) elements.
    Proof.
      elim => /=.
      - discriminate.
      - move=> [k_hd v_hd] tl IH k Hmin_tl /=.
        case Heqb: (eqb k k_hd); first by done. rewrite /=. apply: IH. move: Hmin_tl.
        move=> [] Hmin. case: (min_opt_cases Hmin); last case.
        + move=> [_ Hk]. rewrite Hk eqb_key_refl in Heqb. discriminate.
        + move=> [k' [Hmin_tl [Hlt Hk]]]. rewrite Hk. assumption.
        + move=> [k' [Hmin_tl [Heq Hk]]]. rewrite Hk eqb_key_refl in Heqb.
          discriminate.
    Qed.

    Lemma min_key_mem :
      forall (m : M.t elt) k, min_key m = Some k -> M.mem k m.
    Proof.
      rewrite /min_key=> m k Hmin. rewrite elements_b. move: k Hmin.
      move: (M.elements m) => {m}. exact: min_key_elements_mem.
    Qed.

    Lemma min_key_elements_none :
      forall l, min_key_elements l = None -> l = [::].
    Proof.
      case => /=.
      - reflexivity.
      - move=> [k v] tl H. discriminate.
    Qed.

    Lemma min_key_none :
      forall (m : M.t elt), min_key m = None -> M.Empty m.
    Proof.
      rewrite /min_key=> m Hmin. apply/OP.P.elements_Empty. move: Hmin.
      move: (M.elements m) => {m}. exact: min_key_elements_none.
    Qed.

    Lemma min_key_elements_not_lt :
      forall (elements : seq (M.key * elt)) (k1 k2 : M.key),
        min_key_elements elements = Some k1 ->
        existsb (fun p : M.E.t * elt => eqb k2 (fst p)) elements -> ~ M.E.lt k2 k1.
    Proof.
      elim=> /=.
      - discriminate.
      - move=> [k_hd v_hd] tl IH k1 k2 [] Hmin /=. case/orP.
        + move=> Hk2 Hlt. apply: (min_opt_not_lt_l Hmin).
          move: (eqb_eq Hk2) => {Hk2} Hk2. exact: (EFacts.eq_lt (M.E.eq_sym Hk2) Hlt).
        + case: (min_opt_cases Hmin); last case.
          * move=> [Hmin_tl Hk1]. rewrite (min_key_elements_none Hmin_tl) /=. done.
          * move=> [k_tl [Hmin_tl [Hk_tl Hk1]]]. move=> H; apply: (IH _ _ _ H).
            rewrite Hk1; assumption.
          * move=> [k_tl [Hmin_tl [Hk_tl Hk1]]]. move=> H. move: (IH _ _ Hmin_tl H).
            move=> Hlt_tl Hlt_k1. rewrite Hk1 in Hlt_k1 => {Hmin Hk1}.
            case: (EFacts.lt_total k_hd k_tl); last case; move=> Hlt_hd.
            -- apply: Hlt_tl. exact: (M.E.lt_trans Hlt_k1 Hlt_hd).
            -- apply: Hlt_tl. exact: (EFacts.lt_eq Hlt_k1 Hlt_hd).
            -- apply: Hk_tl; assumption.
    Qed.

    Lemma min_key_not_lt :
      forall (m : M.t elt) k1 k2,
        min_key m = Some k1 -> M.mem k2 m -> ~ M.E.lt k2 k1.
    Proof.
      rewrite /min_key=> m k1 k2. rewrite elements_b. move: k1 k2.
      move: (M.elements m) => {m}. exact: min_key_elements_not_lt.
    Qed.

  End MaxMin.

End FMapLemmas.



(* Keys as a set *)

Module MapKeySet (X : SsrOrder) (M : SsrFMap with Module SE := X) (S : SsrFSet with Module SE := X).

  Module MLemmas := FMapLemmas M.
  Module SLemmas := FSetLemmas S.

  Section Aux.

    Variable elt : Type.

    Definition add_to_set x (e : elt) s := S.add x s.

    (* Return the keys as a set *)
    Definition key_set (m : M.t elt) : S.t := M.fold add_to_set m S.empty.

    Global Instance add_to_set_proper :
      Proper (M.SE.eq ==> eq ==> S.Equal ==> S.Equal) add_to_set.
    Proof.
      move=> x y Hxy a b -> s1 s2 Heq. rewrite /add_to_set Hxy Heq. reflexivity.
    Qed.

    Global Instance add_to_set_proper_map :
      Proper (M.SE.eq ==> eq ==> eq ==> S.Equal) add_to_set.
    Proof.
      move=> x y Hxy a b ? s1 s2 ?; subst. rewrite /add_to_set Hxy. reflexivity.
    Qed.

    Global Instance add_to_set_proper_set :
      Proper (eq ==> eq ==> S.Equal ==> S.Equal) add_to_set.
    Proof.
      move=> x y ? a b ? s1 s2 Heq; subst. rewrite /add_to_set Heq. reflexivity.
    Qed.

    Global Instance add_proper_key_set :
      Proper (M.Equal ==> S.Equal) key_set.
    Proof.
      move=> m1 m2 Heq. rewrite /key_set. apply: MLemmas.fold_Equal.
      assumption.
    Qed.

    Lemma add_to_set_transpose_neqkey :
      MLemmas.OP.P.transpose_neqkey S.Equal add_to_set.
    Proof.
      move=> x y a b s Hxy. rewrite /add_to_set. exact: SLemmas.OP.P.add_add.
    Qed.

    Lemma key_set_Empty m : M.Empty m -> S.Empty (key_set m).
    Proof.
      rewrite /key_set => Hempty.
      rewrite (MLemmas.OP.P.fold_Empty SLemmas.Equal_ST add_to_set S.empty Hempty).
      exact: S.empty_1.
    Qed.

    Lemma key_set_empty : key_set (M.empty elt) = S.empty.
    Proof. rewrite /key_set. apply: MLemmas.OP.P.fold_Empty. exact: M.empty_1. Qed.

    Lemma mem_key_set1 m :
      forall x, M.mem x m -> S.mem x (key_set m).
    Proof.
      rewrite /key_set. eapply MLemmas.P.fold_rec.
      - move=> {m} m Hempty x Hmem. apply: False_ind.
        exact: (MLemmas.empty_mem Hempty Hmem).
      - move=> x e m' E1 E2 _ _ Hadd Hind y Hmem. case Hyx: (y == x).
        + exact: (SLemmas.mem_add_eq Hyx).
        + move/negP: Hyx => Hyx. rewrite (SLemmas.mem_add_neq Hyx).
          apply: Hind. move: (Hadd y) => {Hadd}.
          rewrite (MLemmas.find_add_neq Hyx) => {Hyx} Hfind.
          rewrite -(MLemmas.find_eq_mem_eq Hfind). exact: Hmem.
    Qed.

    Lemma mem_key_set2 m x : S.mem x (key_set m) -> M.mem x m.
    Proof.
      move: m x. apply: MLemmas.OP.P.map_induction.
      - move=> m Hempty x Hmem. move: (key_set_Empty Hempty) => {Hempty} Hempty.
        apply: False_ind. apply: (Hempty x). apply/SLemmas.memP. assumption.
      - move=> m m' IH x e Hin HAdd y Hmem. rewrite (MLemmas.Add_mem_add _ HAdd).
        case Hyx: (y == x).
        + rewrite (eqP Hyx) in Hmem *. apply: MLemmas.mem_add_eq. reflexivity.
        + move/idP: Hyx => Hyx. rewrite (MLemmas.mem_add_neq Hyx).
          rewrite /key_set in Hmem. move: (MLemmas.OP.P.fold_Add
                                             SLemmas.Equal_ST add_to_set_proper
                                             add_to_set_transpose_neqkey
                                             S.empty Hin HAdd) => Heq.
          move/SLemmas.memP: Hmem => Hiny. move: (Heq y) => {Heq} [H _].
          move: (H Hiny) => {H Hiny}. rewrite /add_to_set. move/SLemmas.memP.
          rewrite (SLemmas.mem_add_neq Hyx). exact: IH.
    Qed.

    Lemma mem_key_set m x : S.mem x (key_set m) = M.mem x m.
    Proof.
      case H: (M.mem x m).
      - exact: (mem_key_set1 H).
      - apply/negP=> Hmem. move/negP: H. apply. exact: (mem_key_set2 Hmem).
    Qed.

    Lemma submap_key_set m1 m2 :
      MLemmas.submap m1 m2 -> S.subset (key_set m1) (key_set m2).
    Proof.
      move=> Hsub. apply: S.subset_1 => x Hin1. apply/SLemmas.memP.
      move/SLemmas.memP: Hin1 => Hmem1.  rewrite !mem_key_set in Hmem1 *.
      exact: (MLemmas.submap_mem Hsub Hmem1).
    Qed.

    Lemma mem_key_set_add x v e m :
      S.mem x (key_set (M.add v e m)) = (x == v) || S.mem x (key_set m).
    Proof.
      rewrite !mem_key_set. rewrite MLemmas.add_b. case H: (x == v).
      - rewrite (eqP H). rewrite MLemmas.eqb_key_refl. reflexivity.
      - rewrite /=. case Hmem: (M.mem x m).
        + by rewrite orbT.
        + rewrite orbF. apply/negP => Heqb. move: (MLemmas.eqb_eq Heqb) => Heq.
          move/negP: H; apply. rewrite eq_sym. exact: Heq.
    Qed.

    Lemma key_set_add v e m :
      S.Equal (key_set (M.add v e m)) (S.add v (key_set m)).
    Proof.
      move=> x; split => Hin.
      - move/SLemmas.memP: Hin=> Hmem. rewrite mem_key_set_add in Hmem.
        apply/SLemmas.memP. rewrite SLemmas.add_b. case/orP: Hmem => Hmem.
        + rewrite eq_sym in Hmem. by rewrite (SLemmas.eq_eqb Hmem).
        + by rewrite Hmem orbT.
      - move/SLemmas.memP: Hin=> Hmem. apply/SLemmas.memP.
        rewrite mem_key_set_add. rewrite SLemmas.add_b in Hmem.
        case/orP: Hmem => Hmem.
        + move: (SLemmas.eqb_eq Hmem). move=> /eqP ->. by rewrite eqxx.
        + by rewrite Hmem orbT.
    Qed.

    Lemma mem_key_set_find v m :
      S.mem v (key_set m) ->
      exists e, M.find v m = Some e.
    Proof.
      rewrite mem_key_set => Hmem. exact: (MLemmas.mem_find_some Hmem).
    Qed.

    Lemma not_mem_key_set_find v m :
      ~~ S.mem v (key_set m) ->
      M.find v m = None.
    Proof.
      rewrite mem_key_set => Hmem. exact: (MLemmas.not_mem_find_none Hmem).
    Qed.

  End Aux.

End MapKeySet.



(* Functors for making finite maps *)

Module MakeListMap' (X : SsrOrder) <: SsrFMap with Module SE := X.
  Module SE := X.
  Include FMapList.Make X.
End MakeListMap'.

Module MakeListMap (X : SsrOrder) <: SsrFMap with Module SE := X.
  Module M := MakeListMap' X.
  Module Lemmas := FMapLemmas M.
  Include M.
End MakeListMap.

Module MakeTreeMap' (X : SsrOrder) <: SsrFMap with Module SE := X.
  Module SE := X.
  Include FMapAVL.Make X.
End MakeTreeMap'.

Module MakeTreeMap (X : SsrOrder) <: SsrFMap with Module SE := X.
  Module M := MakeTreeMap' X.
  Module Lemmas := FMapLemmas M.
  Include M.
End MakeTreeMap.

Module Make (X : SsrOrder) <: SsrFMap with Module SE := X := MakeListMap X.



(* Maps that can generate new keys. *)

Module MakeElementGenerator (M : SsrFMap) (D : HasDefault M.SE) (S : HasSucc M.SE) (L : HasLtnSucc M.SE M.SE S).

  Module Lemmas := FMapLemmas M.

  Section Gen.

    Variable elt : Type.

    (* Generate a new key *)
    Definition new_key (m : M.t elt) : M.key :=
      match Lemmas.max_key m with
      | Some k => S.succ k
      | None => D.default
      end.

    Lemma new_key_is_new :
      forall (m : M.t elt), ~~ M.mem (new_key m) m.
    Proof.
      move=> m. rewrite /new_key. case H: (Lemmas.max_key m).
      - apply/negP=> Hmem. apply: (Lemmas.max_key_not_lt H Hmem). exact: L.ltn_succ.
      - move: (Lemmas.max_key_none H) => Hempty.
        exact: (Lemmas.Empty_mem D.default Hempty).
    Qed.

  End Gen.

End MakeElementGenerator.

Module Type SsrFMapWithNew <: SsrFMap.
  Include SsrFMap.
  Section NewKey.
    Variable elt : Type.
    Parameter new_key : t elt -> key.
    Parameter new_key_is_new : forall (m : t elt), ~~ mem (new_key m) m.
  End NewKey.
End SsrFMapWithNew.

Module MakeListMapWithNew (X : SsrOrderWithDefaultSucc) <: SsrFMapWithNew.
  Module M := MakeListMap' X.
  Include M.
  Include MakeElementGenerator M X X X.
End MakeListMapWithNew.

Module MakeTreeMapWithNew (X : SsrOrderWithDefaultSucc) <: SsrFMapWithNew.
  Module M := MakeTreeMap' X.
  Include M.
  Include MakeElementGenerator M X X X.
End MakeTreeMapWithNew.



(* Map a map to another map *)

Module Map2Map (M1 : FMapInterface.S) (M2 : FMapInterface.S).

  Module Lemmas1 := FMapLemmas M1.
  Module Lemmas2 := FMapLemmas M2.

  Section Map2Map.

    Variable elt1 elt2 : Type.
    Variable fk : M1.E.t -> option M2.E.t.
    Variable fk_eq_none :
      forall k1 k2 : M1.E.t,
        M1.E.eq k1 k2 -> fk k1 = None -> fk k2 = None.
    Variable fk_eq_some :
      forall (k1 k2 : M1.E.t) (fk1 : M2.E.t),
        M1.E.eq k1 k2 -> fk k1 = Some fk1 ->
        exists fk2, fk k2 = Some fk2 /\ M2.E.eq fk1 fk2.
    Variable fk_neq_some :
      forall (k1 k2 : M1.E.t) (fk1 fk2 : M2.E.t),
        ~ M1.E.eq k1 k2 -> fk k1 = Some fk1 -> fk k2 = Some fk2 -> ~ M2.E.eq fk1 fk2.

    Variable fv : M1.E.t -> elt1 -> elt2.
    Variable fv_eq_key :
      forall (k1 k2 : M1.E.t) (v : elt1),
        M1.E.eq k1 k2 -> fv k1 v = fv k2 v.

    Definition f k1 v1 m2 :=
      match fk k1 with
      | None => m2
      | Some k2 => M2.add k2 (fv k1 v1) m2
      end.
    Definition map2map (m1 : M1.t elt1) : M2.t elt2 :=
      M1.fold f m1 (M2.empty elt2).

    Lemma f_eq_kv k1 k2 v1 v2 m :
      M1.E.eq k1 k2 -> v1 = v2 -> M2.Equal (f k1 v1 m) (f k2 v2 m).
    Proof.
      move=> Heqk12 Heqv12 k. rewrite /f. dcase (fk k1). case.
      - move=> fk1 Hfk1. move: (fk_eq_some Heqk12 Hfk1). move=> [fk2 [Hfk2 Heqfk12]].
        rewrite Hfk2. rewrite Heqfk12 Heqv12. rewrite (fv_eq_key _ Heqk12). reflexivity.
      - move=> Hfk1. rewrite (fk_eq_none Heqk12 Hfk1). reflexivity.
    Qed.

    Lemma f_eq_kvm k1 k2 v1 v2 (m1 m2 : M2.t elt2) :
      M1.E.eq k1 k2 -> v1 = v2 -> M2.Equal m1 m2 -> M2.Equal (f k1 v1 m1) (f k2 v2 m2).
    Proof.
      move=> Heqk12 Heqv12 Heqm12 k. rewrite /f. dcase (fk k1). case.
      - move=> fk1 Hfk1. move: (fk_eq_some Heqk12 Hfk1). move=> [fk2 [Hfk2 Heqfk12]].
        rewrite Hfk2. rewrite Heqfk12 Heqv12 Heqm12. rewrite (fv_eq_key _ Heqk12).
        reflexivity.
      - move=> Hfk1. rewrite (fk_eq_none Heqk12 Hfk1) Heqm12. reflexivity.
    Qed.

    Lemma f_eq_proper :
      Proper (M1.E.eq ==> eq ==> M2.Equal ==> M2.Equal) f.
    Proof.
      move=> k1 k2 Heqk. move=> v1 v2 Heqv. move=> m1 m2 Heqm.
      exact: (f_eq_kvm Heqk Heqv Heqm).
    Qed.

    Lemma f_eq_transpose_negkey :
      Lemmas1.OP.P.transpose_neqkey M2.Equal f.
    Proof.
      move=> k1 k2 e1 e2 m Hneqk12 k. rewrite /f. dcase (fk k1); case.
      - move=> fk1 Hfk1. dcase (fk k2); case.
        + move=> fk2 Hfk2. move: (fk_neq_some Hneqk12 Hfk1 Hfk2) => Hneqfk12.
          case: (M2.E.eq_dec fk2 k); case: (M2.E.eq_dec fk1 k).
          * move=> Heqk1 Heqk2. apply: False_ind; apply: Hneqfk12.
            rewrite Heqk1 Heqk2. exact: M2.E.eq_refl.
          * move=> Hneqk1 Heqk2. rewrite (Lemmas2.F.add_neq_o _ _ Hneqk1).
            rewrite 2!(Lemmas2.F.add_eq_o _ _ Heqk2). reflexivity.
          * move=> Heqk1 Hneqk2. rewrite (Lemmas2.F.add_neq_o _ _ Hneqk2).
            rewrite 2!(Lemmas2.F.add_eq_o _ _ Heqk1). reflexivity.
          * move=> Hneqk1 Hneqk2. rewrite (Lemmas2.F.add_neq_o _ _ Hneqk1).
            rewrite 2!(Lemmas2.F.add_neq_o _ _ Hneqk2) (Lemmas2.F.add_neq_o _ _ Hneqk1).
            reflexivity.
        + move=> Hfk2. reflexivity.
      - move=> Hfk1. reflexivity.
    Qed.

    Lemma map2map_empty :
      M2.Equal (map2map (M1.empty elt1)) (M2.empty elt2).
    Proof.
      rewrite /map2map. apply: (Lemmas1.OP.P.fold_Empty (Lemmas2.F.Equal_ST elt2) f).
      exact: M1.empty_1.
    Qed.

    Lemma map2map_Empty m :
      M1.Empty m -> M2.Empty (map2map m).
    Proof.
      rewrite /map2map => H1. rewrite (Lemmas1.OP.P.fold_Empty _ _ _ H1).
      exact: M2.empty_1.
    Qed.

    Lemma map2map_not_in_Add m1 m1' k1 v1 :
      ~ M1.In k1 m1 ->
      Lemmas1.OP.P.Add k1 v1 m1 m1' ->
      M2.Equal (map2map m1') (f k1 v1 (map2map m1)).
    Proof.
      move=> Hin Hadd. rewrite /map2map.
      rewrite (Lemmas1.OP.P.fold_Add (Lemmas2.F.Equal_ST elt2)
                                     f_eq_proper f_eq_transpose_negkey
                                     _ Hin Hadd). reflexivity.
    Qed.

    Lemma map2map_mem (m1 : M1.t elt1) k1 fk1 :
      fk k1 = Some fk1 -> M1.mem k1 m1 = M2.mem fk1 (map2map m1).
    Proof.
      move=> Hfk1. move: m1.
      eapply (@Lemmas1.OP.P.map_induction
                elt1
                (fun (m1 : M1.t elt1) =>
                   (M1.mem k1 m1 = M2.mem fk1 (map2map m1)))).
      - move=> m1 Hempty1. move: (map2map_Empty Hempty1) => Hempty2.
        rewrite (negPf (Lemmas1.Empty_mem k1 Hempty1)).
        rewrite (negPf (Lemmas2.Empty_mem fk1 Hempty2)). reflexivity.
      - move=> m m' IH k2 e2 Hin2 Hadd2. rewrite (map2map_not_in_Add Hin2 Hadd2).
        rewrite (Lemmas1.Add_mem_add _ Hadd2). case: (M1.E.eq_dec k1 k2).
        + move=> Heq12. rewrite (Lemmas1.F.add_eq_b _ _ (M1.E.eq_sym Heq12)).
          rewrite /f -/f. move: (fk_eq_some Heq12 Hfk1) => [fk2 [Hfk2 Heqfk12]].
          rewrite Hfk2. rewrite (Lemmas2.F.add_eq_b _ _ (M2.E.eq_sym Heqfk12)).
          reflexivity.
        + move=> Hneq12. have Hneq21: ~ M1.E.eq k2 k1 by
              move=> H; apply: Hneq12; apply: M1.E.eq_sym.
          rewrite (Lemmas1.F.add_neq_b _ _ Hneq21). rewrite /f -/f. dcase (fk k2); case.
          * move=> fk2 Hfk2. move: (fk_neq_some Hneq12 Hfk1 Hfk2) => Hneqfk12.
            have Hneqfk21: ~ M2.E.eq fk2 fk1 by
                move=> H; apply: Hneqfk12; apply: M2.E.eq_sym.
            rewrite (Lemmas2.F.add_neq_b _ _ Hneqfk21) -IH. reflexivity.
          * move=> Hfk2. exact: IH.
    Qed.

    Lemma map2map_not_in (m1 : M1.t elt1) k1 fk1 :
      fk k1 = Some fk1 -> ~ M1.In k1 m1 -> ~ M2.In fk1 (map2map m1).
    Proof.
      move=> Hfk1 Hink1. apply/Lemmas2.memP. rewrite -(map2map_mem _ Hfk1).
      apply/Lemmas1.memP. assumption.
    Qed.

    Lemma map2map_find_none (m1 : M1.t elt1) k1 fk1 :
      fk k1 = Some fk1 -> M1.find k1 m1 = None ->
      M2.find fk1 (map2map m1) = None.
    Proof.
      move=> Hfk1 Hfind. apply: Lemmas2.not_mem_find_none.
      rewrite -(map2map_mem _ Hfk1). apply/negPf. apply: Lemmas1.find_none_not_mem.
      assumption.
    Qed.

    Lemma map2map_find_some (m1 : M1.t elt1) k1 fk1 v1 :
      fk k1 = Some fk1 -> M1.find k1 m1 = Some v1 ->
      M2.find fk1 (map2map m1) = Some (fv k1 v1).
    Proof.
      move: m1.
      eapply (@Lemmas1.OP.P.map_induction
                elt1
                (fun (m1 : M1.t elt1) =>
                   (fk k1 = Some fk1 ->
                    M1.find k1 m1 = Some v1 ->
                    M2.find fk1 (map2map m1) = Some (fv k1 v1)))).
      - move=> m1 Hempty Hfk1 Hfind1. rewrite (Lemmas1.Empty_find _ Hempty) in Hfind1.
        discriminate.
      - move=> m1 m1' IH k2 v2 Hin2 Hadd2 Hfk1 Hfind1.
        rewrite (map2map_not_in_Add Hin2 Hadd2). case: (M1.E.eq_dec k1 k2).
        + move=> Heqk12. move: (fk_eq_some Heqk12 Hfk1) => [fk2 [Hfk2 Heqfk12]].
          rewrite /f Hfk2. rewrite (Lemmas2.F.add_eq_o _ _ (M2.E.eq_sym Heqfk12)).
          rewrite (Lemmas1.F.find_o _ Heqk12) in Hfind1. rewrite (Hadd2 k2) in Hfind1.
          rewrite (Lemmas1.add_eq_o _ _ (M1.E.eq_refl k2))in Hfind1.
          case: Hfind1 => ->. rewrite (fv_eq_key _ Heqk12). reflexivity.
        + move=> Hneqk12. rewrite (Hadd2 k1) in Hfind1.
          have Hneqk21: ~ M1.E.eq k2 k1 by
              move=> H; apply: Hneqk12; apply: M1.E.eq_sym.
          rewrite (Lemmas1.add_neq_o _ _ Hneqk21) in Hfind1.
          rewrite /f. dcase (fk k2); case.
          * move=> fk2 Hfk2. move: (fk_neq_some Hneqk12 Hfk1 Hfk2) => Hneqfk12.
            have Hneqfk21: ~ M2.E.eq fk2 fk1 by
                move=> H; apply: Hneqfk12; apply: M2.E.eq_sym.
            rewrite (Lemmas2.add_neq_o _ _ Hneqfk21). apply: (IH Hfk1). exact: Hfind1.
          * move=> Hfk. exact: (IH Hfk1 Hfind1).
    Qed.

  End Map2Map.

End Map2Map.



(* Maps that agree values of a sub-domain *)

Module MapAgree
       (E : OrderedType)
       (M : FMapInterface.S with Module E := E)
       (S : FSetInterface.S with Module E := E).

  Section AgreeDefn.

    Variable elt : Type.

    Variable s : S.t.

    Definition agree (m1 m2 : M.t elt) : Prop :=
      forall x, S.mem x s -> M.find x m1 = M.find x m2.

    Lemma agree_refl m : agree m m.
    Proof. move=> x Hmem. reflexivity. Qed.

    Lemma agree_sym m1 m2 : agree m1 m2 -> agree m2 m1.
    Proof. move=> H x Hmem. rewrite (H x Hmem). reflexivity. Qed.

    Lemma agree_trans m1 m2 m3 :
      agree m1 m2 -> agree m2 m3 -> agree m1 m3.
    Proof. move=> H12 H23 x Hmem. rewrite (H12 x Hmem). exact: (H23 x Hmem). Qed.

    Global Instance agree_equivalence : Equivalence agree.
    Proof.
      split.
      - exact: agree_refl.
      - exact: agree_sym.
      - exact: agree_trans.
    Qed.

  End AgreeDefn.

  Add Parametric Relation (elt : Type) (s : S.t) : (M.t elt) (@agree elt s)
      reflexivity proved by (@agree_refl elt s)
      symmetry proved by (@agree_sym elt s)
      transitivity proved by (@agree_trans elt s)
      as agree_rel.

  Module VSLemmas := FSetLemmas S.
  Module VMLemmas := FMapLemmas M.

  (*
  Module SF := FSetFacts.Facts(S).
  Module SOP := FSetProperties.OrdProperties S.
  Module MF := FMapFacts.Facts(M).*)

  Section AgreeLemmas.

    Variable elt : Type.

    Global Instance add_agree_proper1 :
      Proper (S.Equal ==> eq ==> eq ==> iff) (@agree elt).
    Proof.
      move=> s1 s2 Heqs m1 m1' Heqm1 m2 m2' Heqm2. subst. split => Ha x Hmemx.
      - rewrite (Ha x); first reflexivity.
        apply/S.mem_1. rewrite Heqs. apply/S.mem_2. exact: Hmemx.
      - rewrite (Ha x); first reflexivity.
        apply/S.mem_1. rewrite -Heqs. apply/S.mem_2. exact: Hmemx.
    Qed.

    Global Instance add_agree_proper2 :
      Proper (eq ==> (@M.Equal elt) ==> eq ==> iff) (@agree elt).
    Proof.
      move=> s1 s2 Heqs m1 m1' Heqm1 m2 m2' Heqm2. subst. split => Ha x Hmemx.
      - rewrite <- Heqm1. exact: (Ha x Hmemx).
      - rewrite -> Heqm1. exact: (Ha x Hmemx).
    Qed.

    Global Instance add_agree_proper3 :
      Proper (eq ==> eq ==> (@M.Equal elt) ==> iff) (@agree elt).
    Proof.
      move=> s1 s2 Heqs m1 m1' Heqm1 m2 m2' Heqm2. subst. split => Ha x Hmemx.
      - rewrite <- Heqm2. exact: (Ha x Hmemx).
      - rewrite -> Heqm2. exact: (Ha x Hmemx).
    Qed.

    Global Instance add_agree_proper :
      Proper (S.Equal ==> (@M.Equal elt) ==> (@M.Equal elt) ==> iff) (@agree elt).
    Proof.
      move=> s1 s2 Heqs m1 m1' Heqm1 m2 m2' Heqm2. split; move=> Ha x Hmemx.
      - rewrite -Heqm1 -Heqm2. rewrite (Ha x); first reflexivity.
        apply/S.mem_1. rewrite Heqs. apply/S.mem_2. exact: Hmemx.
      - rewrite Heqm1 Heqm2. rewrite (Ha x); first reflexivity.
        apply/S.mem_1. rewrite -Heqs. apply/S.mem_2. exact: Hmemx.
    Qed.

    Lemma Empty_agree vs (m1 m2 : M.t elt) : S.Empty vs -> agree vs m1 m2.
    Proof. move=> He x /S.mem_2 Hmemx. move: (He _ Hmemx). done. Qed.

    Lemma agree_empty_set (m1 m2 : M.t elt) : agree S.empty m1 m2.
    Proof. apply: Empty_agree. exact: S.empty_1. Qed.

    Lemma agree_singleton_set x (m1 m2 : M.t elt) :
      agree (S.singleton x) m1 m2 <-> M.find x m1 = M.find x m2.
    Proof.
      split=> H.
      - apply: H. apply: S.mem_1. apply: S.singleton_2. reflexivity.
      - move=> y /S.mem_2/S.singleton_1 Hin. rewrite -Hin. assumption.
    Qed.

    Lemma agree_empty_map_l vs (m : M.t elt) x :
      agree vs (M.empty elt) m -> S.mem x vs -> M.find x m = None.
    Proof. move=> Ha Hmem. rewrite -(Ha _ Hmem). exact: VMLemmas.empty_o. Qed.

    Lemma agree_empty_map_r vs (m : M.t elt) x :
      agree vs m (M.empty elt) -> S.mem x vs -> M.find x m = None.
    Proof. move=> Ha Hmem. rewrite (Ha _ Hmem). exact: VMLemmas.empty_o. Qed.

    Lemma Subset_set_agree s1 s2 (m1 m2 : M.t elt) :
      S.Subset s1 s2 -> agree s2 m1 m2 -> agree s1 m1 m2.
    Proof.
      move=> Hsub Ha x /S.mem_2 Hin1. apply: Ha. apply/S.mem_1. exact: (Hsub _ Hin1).
    Qed.

    Lemma subset_set_agree s1 s2 (m1 m2 : M.t elt) :
      S.subset s1 s2 -> agree s2 m1 m2 -> agree s1 m1 m2.
    Proof.
      move=> Hsub Ha. apply: (Subset_set_agree _ Ha). apply: S.subset_2. exact: Hsub.
    Qed.

    Lemma not_mem_add_map_l vs (m1 m2 : M.t elt) x v :
      ~~ S.mem x vs -> agree vs m1 m2 -> agree vs (M.add x v m1) m2.
    Proof.
      move=> Hmem Ha y Hmemy. rewrite VMLemmas.add_neq_o.
      - exact: (Ha _ Hmemy).
      - move=> Heq. move/negP: Hmem; apply. rewrite (VSLemmas.mem_b _ Heq). exact: Hmemy.
    Qed.

    Lemma not_mem_add_map_r vs (m1 m2 : M.t elt) x v :
      ~~ S.mem x vs -> agree vs m1 m2 -> agree vs m1 (M.add x v m2).
    Proof.
      move=> Hmem /agree_sym Ha. apply: agree_sym. exact: (not_mem_add_map_l _ Hmem Ha).
    Qed.

    Lemma agree_add_map2 vs (m1 m2 : M.t elt) x v :
      agree vs m1 m2 -> agree vs (M.add x v m1) (M.add x v m2).
    Proof.
      move=> Ha y Hmemy. case: (E.eq_dec x y).
      - move=> Heq. rewrite 2!(VMLemmas.add_eq_o _ _ Heq). reflexivity.
      - move=> Hneq. rewrite 2!(VMLemmas.add_neq_o _ _ Hneq). exact: (Ha _ Hmemy).
    Qed.

    Lemma agree_add_map_l vs (m1 m2 : M.t elt) x v :
      agree vs m1 m2 -> M.find x m2 = Some v ->
      agree vs (M.add x v m1) m2.
    Proof.
      move=> Ha Hfind y Hmemy. case: (E.eq_dec x y).
      - move=> Heq. rewrite (VMLemmas.add_eq_o _ _ Heq). rewrite -(VMLemmas.find_o _ Heq).
        rewrite -Hfind. reflexivity.
      - move=> Hneq. rewrite (VMLemmas.add_neq_o _ _ Hneq). exact: (Ha _ Hmemy).
    Qed.

    Lemma agree_add_map_r vs (m1 m2 : M.t elt) x v :
      agree vs m1 m2 -> M.find x m1 = Some v ->
      agree vs m1 (M.add x v m2).
    Proof.
      move=> /agree_sym Ha Hf. apply: agree_sym. exact: (agree_add_map_l Ha Hf).
    Qed.

    Lemma agree_add_set_l x vs (m1 m2 : M.t elt) :
      agree (S.add x vs) m1 m2 -> agree (S.singleton x) m1 m2.
    Proof.
      move=> Ha y Hmemy. apply: (Ha y). rewrite VSLemmas.singleton_b in Hmemy.
      rewrite VSLemmas.add_b Hmemy /=. reflexivity.
    Qed.

    Lemma agree_add_set_r x vs (m1 m2 : M.t elt) :
      agree (S.add x vs) m1 m2 -> agree vs m1 m2.
    Proof.
      move=> Ha y Hmemy. apply: (Ha y). rewrite VSLemmas.add_b Hmemy orbT. reflexivity.
    Qed.

    Lemma agree_union_set_l vs1 vs2 (m1 m2 : M.t elt) :
      agree (S.union vs1 vs2) m1 m2 -> agree vs1 m1 m2.
    Proof.
      move=> Ha x Hmemx. apply: (Ha x). rewrite VSLemmas.union_b Hmemx /=. reflexivity.
    Qed.

    Lemma agree_union_set_r vs1 vs2 (m1 m2 : M.t elt) :
      agree (S.union vs1 vs2) m1 m2 -> agree vs2 m1 m2.
    Proof.
      move=> Ha x Hmemx. apply: (Ha x). rewrite VSLemmas.union_b Hmemx /= orbT. reflexivity.
    Qed.

    Lemma agree_add_to_set x vs (m1 m2 : M.t elt) :
      agree vs m1 m2 -> M.find x m1 = M.find x m2 -> agree (S.add x vs) m1 m2.
    Proof.
      move=> Ha Hf y /S.mem_2 Hmem.
      case/VSLemmas.OP.P.Dec.F.add_iff: Hmem => H.
      - rewrite -2!(VMLemmas.find_o _ H). exact: Hf.
      - move/S.mem_1: H => Hmem. exact: (Ha _ Hmem).
    Qed.

    Lemma agree_union_sets vs1 vs2 (m1 m2 : M.t elt) :
      agree vs1 m1 m2 -> agree vs2 m1 m2 -> agree (S.union vs1 vs2) m1 m2.
    Proof.
      move=> Ha1 Ha2 x Hmem. rewrite VSLemmas.union_b in Hmem. case/orP: Hmem=> Hmem.
      - exact: (Ha1 _ Hmem).
      - exact: (Ha2 _ Hmem).
    Qed.

    Lemma agree_add_set x vs (m1 m2 : M.t elt) :
      agree (S.add x vs) m1 m2 <-> agree (S.singleton x) m1 m2 /\ agree vs m1 m2.
    Proof.
      split.
      - move=> H. exact: (conj (agree_add_set_l H) (agree_add_set_r H)).
      - move=> [H1 H2]. apply: (agree_add_to_set H2). apply/agree_singleton_set.
        assumption.
    Qed.

    Lemma agree_union_set vs1 vs2 (m1 m2 : M.t elt) :
      agree (S.union vs1 vs2) m1 m2 <-> agree vs1 m1 m2 /\ agree vs2 m1 m2.
    Proof.
      split.
      - move=> H. exact: (conj (agree_union_set_l H) (agree_union_set_r H)).
      - move=> [H1 H2]. exact: agree_union_sets.
    Qed.

  End AgreeLemmas.

  Ltac simpl_agree :=
    repeat
      match goal with
      | H : @agree ?t (S.add _ _) _ _ |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          (* `move: (agree_add_set_l H)` succeeds inside this module
             but fails outside this module *)
          generalize (agree_add_set_r H);
          generalize (agree_add_set_l H);
          move=> {H} H1 H2
      | H : @agree ?t (S.union _ _) _ _ |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          generalize (agree_union_set_r H);
          generalize (agree_union_set_l H);
          move=> {H} H1 H2
      end.

  Ltac dp_agree :=
    repeat
      match goal with
      | |- agree S.empty _ _ => exact: agree_empty_set
      | H : S.is_empty ?vs |- agree ?vs _ _ =>
          (apply: Empty_agree); (apply: S.is_empty_2); assumption
      | H : S.Empty ?vs |- agree ?vs _ _ => exact: Empty_agree H
      | |- agree _ ?E ?E => exact: agree_refl
      | H : agree ?vs ?E1 ?E2 |- agree ?vs ?E2 ?E1 => exact: (agree_sym H)
      | H1 : agree ?vs ?E1 ?E2, H2 : agree ?vs ?E2 ?E3
        |- agree ?vs ?E1 ?E3 => exact: (agree_trans H1 H2)
      | H : agree (S.singleton _) _ _ |- _ => move/agree_singleton_set: H => H
      | |- agree (S.singleton _) _ _ => apply/agree_singleton_set
      | |- agree (S.add _ _) _ _ => apply: agree_add_to_set
      | |- agree (S.union _ _) _ _ => apply: agree_union_sets
      | |- agree _ (M.add ?x ?v _) (M.add ?x ?v _) => apply: agree_add_map2
      | |- agree _ (M.add _ _ _) _ => apply: agree_add_map_l
      | |- agree _ _ (M.add _ _ _) => apply: agree_add_map_r
      | H1 : is_true (S.subset ?s1 ?s2),
          H2 : agree ?s2 ?m1 ?m2 |- agree ?s1 ?m1 ?m2 =>
          exact: (subset_set_agree H1 H2)
      | H1 : is_true (~~ S.mem ?x ?vs),
          H2 : agree ?vs ?m1 ?m2 |- agree ?vs (M.add ?x ?v ?m1) ?m2 =>
          exact: (not_mem_add_map_l H1 H2)
      | H1 : is_true (~~ S.mem ?x ?vs),
          H2 : agree ?vs ?m1 ?m2 |- agree ?vs ?m1 (M.add ?x ?v ?m2) =>
          exact: (not_mem_add_map_r H1 H2)
      | H : ?e |- ?e => assumption
      end.

End MapAgree.
