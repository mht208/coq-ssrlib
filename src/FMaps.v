
(** * Some auxiliary lemmas for FMaps. *)

(** These lemmas can be proven by facts in Coq.FSets.FMapFacts. *)

From Coq Require Import FMaps FMapAVL OrderedType.
From mathcomp Require Import ssreflect ssrbool eqtype.
From ssrlib Require Import Types SsrOrdered Lists Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



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



    Lemma find_add_eq (m : M.t elt) (x y : M.key) (e : elt) :
      M.E.eq x y -> M.find x (M.add y e m) = Some e.
    Proof.
      move=> Hxy. apply: F.add_eq_o. apply: M.E.eq_sym. exact: Hxy.
    Qed.

    Lemma find_add_neq (m : M.t elt) (x y : M.key) (e : elt) :
      ~(M.E.eq x y) -> M.find x (M.add y e m) = M.find x m.
    Proof.
      move=> Hne. apply: F.add_neq_o. move=> Heq; apply: Hne; apply: M.E.eq_sym.
      exact: Heq.
    Qed.

    Lemma find_some_map (f : elt -> elt') (m : M.t elt) (x : M.key) (e : elt) :
      M.find x m = Some e ->
      M.find x (M.map f m) = Some (f e).
    Proof.
      move=> H. rewrite F.map_o. rewrite /option_map. rewrite H. reflexivity.
    Qed.

    Lemma find_none_map (f : elt -> elt') (m : M.t elt) (x : M.key) :
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

  End FMapLemmas.

  Section Proper.

    Variable elt elt' : Type.

    Variable f : elt -> elt'.

    Lemma add_f_proper :
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

    Variable elt : Type.

    Definition submap (m m' : M.t elt) :=
      forall k v, M.find k m = Some v -> M.find k m' = Some v.

    Lemma submap_refl (m : M.t elt) : submap m m.
    Proof.
      move=> k v Hfind. exact: Hfind.
    Qed.

    Lemma submap_trans (m1 m2 m3 : M.t elt) :
      submap m1 m2 -> submap m2 m3 -> submap m1 m3.
    Proof.
      move=> H12 H23 k v Hf1. apply: H23. apply: H12. exact: Hf1.
    Qed.

    Lemma submap_none_add (m1 m2 : M.t elt) (k : M.key) (e : elt) :
      submap m1 m2 -> M.find k m1 = None -> submap m1 (M.add k e m2).
    Proof.
      move=> Hsub Hfind k' v' Hfind'. rewrite add_o. case: (P.F.eq_dec k k').
      - move=> Heq. rewrite (F.find_o m1 Heq) in Hfind. rewrite Hfind in Hfind'.
        discriminate.
      - move=> Hneq. exact: (Hsub k' v' Hfind').
    Qed.

    Lemma submap_some_add (m1 m2 : M.t elt) (k : M.key) (e : elt) :
      submap m1 m2 -> M.find k m1 = Some e -> submap m1 (M.add k e m2).
    Proof.
      move=> Hsub Hfind k' v' Hfind'. rewrite add_o. case: (P.F.eq_dec k k').
      - move=> Heq. rewrite (F.find_o m1 Heq) in Hfind. rewrite Hfind in Hfind'.
        exact: Hfind'.
      - move=> Hneq. exact: (Hsub k' v' Hfind').
    Qed.

  End Submap.

End FMapLemmas.

Module MakeListMap (V : SsrOrderedType).
  Module M := FMapList.Make V.
  Module Lemmas := FMapLemmas(M).
  Include M.
End MakeListMap.

Module MakeTreeMap (V : SsrOrderedType).
  Module M := FMapAVL.Make V.
  Module Lemmas := FMapLemmas(M).
  Include M.
End MakeTreeMap.

Module Make (V : SsrOrderedType) := MakeListMap V.

Module Map2Map (M1 : FMapInterface.S) (M2 : FMapInterface.S).

  Module Lemmas1 := FMapLemmas M1.
  Module Lemmas2 := FMapLemmas M2.

  Section Map2Map.

    Variable elt1 elt2 : Type.
    Variable fk : M1.key -> option M2.key.
    Variable fk_eq_none :
      forall k1 k2 : M1.key,
        M1.E.eq k1 k2 -> fk k1 = None -> fk k2 = None.
    Variable fk_eq_some :
      forall (k1 k2 : M1.key) (fk1 : M2.key),
        M1.E.eq k1 k2 -> fk k1 = Some fk1 ->
        exists fk2, fk k2 = Some fk2 /\ M2.E.eq fk1 fk2.
    Variable fk_neq_some :
      forall (k1 k2 : M1.key) (fk1 fk2 : M2.key),
        ~ M1.E.eq k1 k2 -> fk k1 = Some fk1 -> fk k2 = Some fk2 -> ~ M2.E.eq fk1 fk2.
    Variable fv : elt1 -> elt2.
    Definition f k1 v1 m2 :=
      match fk k1 with
      | None => m2
      | Some k2 => M2.add k2 (fv v1) m2
      end.
    Definition map2map (m1 : M1.t elt1) : M2.t elt2 :=
      M1.fold f m1 (M2.empty elt2).

    Lemma f_eq_kv k1 k2 v1 v2 m :
      M1.E.eq k1 k2 -> v1 = v2 -> M2.Equal (f k1 v1 m) (f k2 v2 m).
    Proof.
      move=> Heqk12 Heqv12 k. rewrite /f. dcase (fk k1). case.
      - move=> fk1 Hfk1. move: (fk_eq_some Heqk12 Hfk1). move=> [fk2 [Hfk2 Heqfk12]].
        rewrite Hfk2. rewrite Heqfk12 Heqv12. reflexivity.
      - move=> Hfk1. rewrite (fk_eq_none Heqk12 Hfk1). reflexivity.
    Qed.

    Lemma f_eq_kvm k1 k2 v1 v2 (m1 m2 : M2.t elt2) :
      M1.E.eq k1 k2 -> v1 = v2 -> M2.Equal m1 m2 -> M2.Equal (f k1 v1 m1) (f k2 v2 m2).
    Proof.
      move=> Heqk12 Heqv12 Heqm12 k. rewrite /f. dcase (fk k1). case.
      - move=> fk1 Hfk1. move: (fk_eq_some Heqk12 Hfk1). move=> [fk2 [Hfk2 Heqfk12]].
        rewrite Hfk2. rewrite Heqfk12 Heqv12 Heqm12. reflexivity.
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
      M2.find fk1 (map2map m1) = Some (fv v1).
    Proof.
      move: m1.
      eapply (@Lemmas1.OP.P.map_induction
                elt1
                (fun (m1 : M1.t elt1) =>
                   (fk k1 = Some fk1 ->
                    M1.find k1 m1 = Some v1 ->
                    M2.find fk1 (map2map m1) = Some (fv v1)))).
      - move=> m1 Hempty Hfk1 Hfind1. rewrite (Lemmas1.Empty_find _ Hempty) in Hfind1.
        discriminate.
      - move=> m1 m1' IH k2 v2 Hin2 Hadd2 Hfk1 Hfind1.
        rewrite (map2map_not_in_Add Hin2 Hadd2). case: (M1.E.eq_dec k1 k2).
        + move=> Heqk12. move: (fk_eq_some Heqk12 Hfk1) => [fk2 [Hfk2 Heqfk12]].
          rewrite /f Hfk2. rewrite (Lemmas2.F.add_eq_o _ _ (M2.E.eq_sym Heqfk12)).
          rewrite (Lemmas1.F.find_o _ Heqk12) in Hfind1. rewrite (Hadd2 k2) in Hfind1.
          rewrite (Lemmas1.add_eq_o _ _ (M1.E.eq_refl k2))in Hfind1.
          case: Hfind1 => ->; reflexivity.
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
