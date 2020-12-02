
From Coq Require Import Arith.
From mathcomp Require Import ssreflect eqtype ssrfun ssrnat ssrbool seq.
From ssrlib Require Import Nats FSets.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module S := MakeTreeSet NatOrder.

  Lemma subset_cardinal s1 s2 :
    S.subset s1 s2 -> S.cardinal s1 <= S.cardinal s2.
  Proof.
    move=> Hsub. apply: le_leq. apply: S.Lemmas.OP.P.subset_cardinal.
    apply: S.TS.subset_2. assumption.
  Qed.

  Lemma uniq_of_list_cardinal xs :
    uniq xs -> S.cardinal (S.Lemmas.OP.P.of_list xs) = size xs.
  Proof.
    elim: xs => [| x xs IH] //=. move/andP=> [Hnotin Huniq].
    rewrite S.Lemmas.P.add_cardinal_2.
    - rewrite (IH Huniq). reflexivity.
    - move/S.Lemmas.memP=> Hmem. rewrite -S.Lemmas.in_mem in Hmem.
      rewrite Hmem in Hnotin. discriminate.
  Qed.

Section Pigeonhole.

  Variable f : nat -> nat.

  Fixpoint below (n : nat) : S.t :=
    match n with
    | O => S.empty
    | S m => S.add m (below m)
    end.

  Lemma below_mem (n m : nat) : m < n -> S.mem m (below n).
  Proof.
    elim: n m => [| n IHn] m Hnm //=. rewrite ltnS leq_eqVlt in Hnm.
    case/orP: Hnm => Hnm.
    - apply: S.Lemmas.mem_add2. assumption.
    - apply: S.Lemmas.mem_add3. exact: (IHn _ Hnm).
  Qed.

  Lemma below_notin (n m : nat) : n <= m -> ~~ S.mem m (below n).
  Proof.
    elim: n m => [| n IHn] m Hnm //=. rewrite S.Lemmas.add_b negb_or.
    rewrite (IHn _ (ltnW Hnm)) andbT. apply/negP=> /S.Lemmas.eqb_eq Heq.
    rewrite (eqP Heq) ltnn in Hnm. discriminate.
  Qed.

  Lemma below_size n : S.cardinal (below n) = n.
  Proof.
    elim: n => [| n IHn] //=. rewrite S.Lemmas.P.add_cardinal_2.
    - by rewrite IHn.
    - move=> /S.Lemmas.memP Hmem. move: (below_notin (leqnn n)). rewrite Hmem.
      discriminate.
  Qed.

  Fixpoint find_same used n : bool * seq nat :=
    match n with
    | O => (false, used)
    | S m => if f m \in used then (true, used)
             else find_same (f m::used) m
    end.

  Lemma find_same_exists n used :
    find_same [::] n = (true, used) ->
    exists i1, exists i2, i1 < i2 /\ i2 < n /\ f i1 = f i2.
  Proof.
    move: (leqnn n).
    have: forall i, i < size ([::] : seq nat) ->
                    exists m, n <= m /\ m < n /\ f m = nth 0 [::] i.
    { move=> i /= H. by inversion H. }
    move: {2 4 6}n. move: [::].
    elim: n used => [| n IHn] //= oused iused max Hexists Hsize Hfind.
    case Hin: (f n \in iused) Hfind.
    - case => ?; subst. move: (Hin) => Hn. move/(nthP 0): Hin => [i Hi Hnthi].
      rewrite -Hnthi in Hn. move: (Hexists _ Hi) => [j [H1 [H2 H3]]].
      exists n; exists j. rewrite H1 H2 H3 Hnthi. done.
    - move=> Hfind. apply: (IHn oused (f n::iused) _ _ (ltnW Hsize) Hfind).
      move=> i Hi. case Hi0: (i == 0).
      + rewrite (eqP Hi0). exists n. rewrite leqnn Hsize /=. done.
      + rewrite /= ltnS in Hi. have H0i: 0 < i by rewrite lt0n Hi0.
        rewrite (Seqs.nth_cons _ _ _ H0i).
        move: (ltn_leq_trans H0i Hi) => Hsize0.
        have Hisize: i - 1 < size iused.
        { apply: (ltn_leq_trans _ Hi). rewrite -{2}(subn0 i). by apply: ltn_sub2l. }
        move: (Hexists _ Hisize) => [j [Hj1 [Hj2 Hj3]]].
        exists j. rewrite (ltnW Hj1) Hj2 Hj3. done.
  Qed.

  Lemma find_same_size n used :
    find_same [::] n = (false, used) -> size used = n.
  Proof.
    have: size ([::] : seq nat) = n - n by rewrite subnn.
    move: (leqnn n).
    move: [::]. move: {2 3 6}n => max.
    elim: n used => [| n IHn] /= oused iused Hmax Hs Hfind.
    - case: Hfind => ?; subst. rewrite Hs subn0. reflexivity.
    - case Hin: (f n \in iused) Hfind => //= Hfind.
      apply: (IHn _ (f n::iused) (ltnW Hmax) _ Hfind).
      rewrite /= Hs. rewrite subnS. rewrite (@ltn_predK 0); first reflexivity.
      rewrite subn_gt0. assumption.
  Qed.

  Lemma find_same_uniq n found used :
    find_same [::] n = (found, used) -> uniq used.
  Proof.
    have: uniq ([::] : seq nat) by done. move: [::].
    elim: n found used => [| n IHn] /= found oused iused.
    - move=> Hi [] ? ?; subst. assumption.
    - move=> Hi. case Hin: (f n \in iused).
      + case=> ? ?; subst. assumption.
      + move=> Hfind. apply: (IHn found oused (f n :: iused) _ Hfind).
        rewrite /=. rewrite Hi andbT. apply/negPf. assumption.
  Qed.

  Lemma find_same_subset n m used :
    (forall i, i < n -> f i < m) ->
    find_same [::] n = (false, used) ->
    S.subset (S.Lemmas.OP.P.of_list used) (below m).
  Proof.
    have: S.subset (S.Lemmas.OP.P.of_list [::]) (below m).
    { rewrite /=. exact: S.Lemmas.subset_empty. }
    move: ([::] : seq nat). elim: n used => [| n IHn] /= oused iused.
    - move=> Hsub Hfi [] ?; subst. assumption.
    - move=> Hsub Hfi. case Hin: (f n \in iused).
      + by case.
      + move=> Hfind. apply: (IHn _ (f n::iused) _ _ Hfind) => /=.
        * apply: S.Lemmas.subset_add3.
          -- apply: below_mem. apply: Hfi. exact: ltnSn.
          -- assumption.
        * move=> i Hi. apply: Hfi. rewrite ltnS. exact: (ltnW Hi).
  Qed.

  Lemma find_same_failed n m used :
    m < n ->
    (forall i, i < n -> f i < m) ->
    find_same [::] n = (false, used) -> False.
  Proof.
    move=> Hmn Hfi Hfind. move: (find_same_size Hfind) => Hn.
    move: (find_same_subset Hfi Hfind) => Hm.
    move: (subset_cardinal Hm). rewrite below_size.
    rewrite (uniq_of_list_cardinal (find_same_uniq Hfind)).
    rewrite Hn leqNgt Hmn. discriminate.
  Qed.

  Lemma pigeonhole (n m : nat) :
    m < n ->
    (forall i, i < n -> f i < m) ->
    exists i1, exists i2, i1 < i2 /\ i2 < n /\ f i1 = f i2.
  Proof.
    move=> Hmn Hf. case Hfind: (find_same [::] n) => [found used].
    case: found Hfind => Hfind.
    - exact: (find_same_exists Hfind).
    - apply: False_ind. exact: (find_same_failed Hmn Hf Hfind).
  Qed.

End Pigeonhole.
