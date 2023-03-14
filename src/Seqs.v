
From Coq Require Import List Relations Morphisms.
From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype ssrfun.
From ssrlib Require Import Compatibility Lists.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** Lemmas for sequences of Type *)

Section SeqLemmas.

  Variable A : Type.

  Variable B : Type.

  Variable default : A.

  Lemma in_cat (x : A) (s1 s2 : seq A) :
    In x (s1 ++ s2) -> In x s1 \/ In x s2.
  Proof.
    elim: s1 s2 => [| y s1 IH] s2 /=.
    - move=> H; right; assumption.
    - case => H.
      + left; left; assumption.
      + case: (IH _ H) => {}H.
        * left; right; assumption.
        * right; assumption.
  Qed.

  Lemma in_cat_l (x : A) (s1 s2 : seq A) :
    In x s1 -> In x (s1 ++ s2).
  Proof.
    elim: s1 s2 => [| y s1 IH] s2 //=. case => H.
    + left; assumption.
    + right; exact: (IH _ H).
  Qed.

  Lemma in_cat_r (x : A) (s1 s2 : seq A) :
    In x s2 -> In x (s1 ++ s2).
  Proof.
    elim: s1 s2 => [| y s1 IH] s2 //=. move=> H; right; exact: (IH _ H).
  Qed.

  Lemma in_singleton (x y : A) :
    In x [:: y] -> x = y.
  Proof. by case => //=. Qed.

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

  Lemma drop_take (s : seq A) n m :
    n <= m -> m < size s -> drop (m - n) (take m s) = take n (drop (m - n) s).
  Proof.
    elim: s n m => [| x s IH] n m Hnm Hms //. rewrite /= in Hms.
    case: m Hnm Hms.
    - rewrite leqn0 => /eqP ->. rewrite subnn drop0 take0. reflexivity.
    - move=> m Hnm Hms. rewrite -(addn1 m) -(addn1 (size s)) ltn_add2r in Hms.
      rewrite leq_eqVlt in Hnm. case/orP: Hnm => Hnm.
      + rewrite (eqP Hnm) subnn !drop0. reflexivity.
      + rewrite ltnS in Hnm. rewrite take_cons. rewrite !(subSn Hnm) !drop_cons.
        exact: (IH _ _ Hnm Hms).
  Qed.

  Lemma take_take (s : seq A) (n m : nat) : take n (take m s) = take (minn n m) s.
  Proof.
    elim: s n m => [| x s IH] n m //.
    case: m => [| m] //. case: n => [| n] //. rewrite minnSS.
    rewrite !take_cons. rewrite IH. reflexivity.
  Qed.

  Lemma nseq_addn (x : A) n m : nseq (n + m) x = nseq n x ++ nseq m x.
  Proof.
    elim: n m => [| n IHn] m //=. rewrite IHn. reflexivity.
  Qed.

  Lemma drop_nseq (x : A) n m : drop n (nseq m x) = nseq (m - n) x.
  Proof.
    case Hnm: (m <= n).
    - rewrite -{1}(subnK Hnm). rewrite -drop_drop.
      have Hm: m = size (nseq m x) by rewrite size_nseq.
      rewrite {2}Hm. rewrite drop_size /=. rewrite -subn_eq0 in Hnm.
      rewrite (eqP Hnm) /=. reflexivity.
    - move/idP/negP: Hnm. rewrite -ltnNge => Hnm. move: (subnK (ltnW Hnm)) => H.
      rewrite -{1}H. rewrite addnC nseq_addn.
      rewrite drop_size_cat; last by rewrite size_nseq. reflexivity.
  Qed.

  Lemma take_nseq (x : A) n m : take n (nseq m x) = nseq (minn n m) x.
  Proof.
    case Hnm: (n <= m).
    - move/minn_idPl: (Hnm) => ->. move: (subnK Hnm) => <-.
      rewrite addnC nseq_addn. rewrite take_size_cat; last by rewrite size_nseq.
      reflexivity.
    - move/idP/negP: Hnm. rewrite -ltnNge => Hnm.
      move/minn_idPr: (ltnW Hnm) => ->. rewrite take_oversize; first by reflexivity.
      rewrite size_nseq. exact: (ltnW Hnm).
  Qed.

  Lemma drop_nseq_more (s : seq A) (x : A) n m :
    n <= m -> drop n s = nseq (size s - n) x -> drop m s = nseq (size s - m) x.
  Proof.
    move=> Hmn Hdn. move: (subnK Hmn) => H. rewrite -{1}H.
    rewrite -drop_drop. rewrite Hdn. rewrite drop_nseq. rewrite -subnDA.
    rewrite addnC H. reflexivity.
  Qed.

  Lemma take_nseq_less_minn (s : seq A) (x : A) n m :
    m <= n -> take n s = nseq (minn n (size s)) x ->
    take m s = nseq (minn m (size s)) x.
  Proof.
    move=> Hmn. case Hns: (n <= size s).
    - move/minn_idPl: (Hns) => ->. move/minn_idPl: (leq_trans Hmn Hns) => ->.
      elim: s n m Hmn Hns => [| e s IH] n m Hmn Hns.
      + rewrite leqn0 in Hns. rewrite (eqP Hns) in Hmn.
        rewrite leqn0 in Hmn. rewrite (eqP Hmn). reflexivity.
      + case: n Hmn Hns => [| n] Hmn Hns.
        * rewrite leqn0 in Hmn. rewrite (eqP Hmn). reflexivity.
        * case: m Hmn => [| m] Hmn.
          -- reflexivity.
          -- rewrite /= !ltnS in Hmn Hns. rewrite !take_cons.
             rewrite -(addn1 n) -(addn1 m). rewrite (addnC n) (addnC m).
             rewrite !nseq_addn /=. case => -> H.
             rewrite (IH _ _ Hmn Hns H). reflexivity.
    - move/idP/negP: Hns. rewrite -ltnNge => Hsn. move/minn_idPr: (ltnW Hsn) => ->.
      rewrite (take_oversize (ltnW Hsn)). move=> ->. rewrite size_nseq.
      case Hms: (m <= size s).
      + rewrite take_nseq. move/minn_idPl: (Hms) => ->. reflexivity.
      + move/idP/negP: Hms. rewrite -ltnNge => Hsm. move/minn_idPr: (ltnW Hsm) => ->.
        rewrite take_oversize; first reflexivity.
        rewrite size_nseq. exact: (ltnW Hsm).
  Qed.

  Lemma take_nseq_less (s : seq A) (x : A) n m :
    m <= n -> n <= size s -> take n s = nseq n x -> take m s = nseq m x.
  Proof.
    move=> Hmn Hns. move/minn_idPl: (leq_trans Hmn Hns) => {2}<-.
    move/minn_idPl: (Hns) => {2}<-. exact: (take_nseq_less_minn Hmn).
  Qed.

  Lemma catsl_inj (s1 s2 s3 : seq A) : s1 ++ s2 = s1 ++ s3 -> s2 = s3.
  Proof. elim: s1 s2 s3 => [| hd tl IH] s2 s3 //=. case. exact: IH. Qed.

  Lemma catsr_inj (s1 s2 s3 : seq A) : s2 ++ s1 = s3 ++ s1 -> s2 = s3.
  Proof.
    elim: s1 s2 s3 => [| hd tl IH] s2 s3 /=.
    - rewrite !cats0. by apply.
    - rewrite -!cat_rcons. move=> H. move: (IH _ _ H) => {} H.
      move: (rcons_inj H). case. by apply.
  Qed.

  Lemma In_rcons x (s : seq A) l :
    List.In x (rcons s l) <-> List.In x s \/ x = l.
  Proof.
    elim: s => [| hd tl IH] /=.
    - split; case=> H //=.
      + right. symmetry. assumption.
      + left; symmetry. assumption.
    - move: IH=> [IH1 IH2]. split; case => H /=.
      + left; left. assumption.
      + case: (IH1 H) => {} H.
        * left; right; assumption.
        * right; assumption.
      + case: H => H.
        * left; assumption.
        * right. exact: (IH2 (or_introl H)).
      + right. exact: (IH2 (or_intror H)).
  Qed.

  Lemma incl_consl (a : A) (l m : seq A) :
    incl (a :: l) m -> In a m /\ incl l m.
  Proof.
    move=> H. split.
    - apply: (H a). exact: in_eq.
    - move=> x Hinx. apply: (H x). apply: List.in_cons. assumption.
  Qed.

  Lemma incl_empty (s : seq A) :
    incl s [::] -> s = [::].
  Proof.
    elim: s => [| x s IH] //=. move=> H. move: (incl_consl H) => [H1 H2].
    apply: False_ind. exact: (List.in_nil H1).
  Qed.

  Lemma split_cons (x : A * B) (s : seq (A * B)) :
    split (x::s) = (x.1::(split s).1, x.2::(split s).2).
  Proof.
    rewrite /=. case Hs: (split s) => [sa sb] /=. case: x => [xa xb] /=.
    reflexivity.
  Qed.

  Lemma split_cat (s1 s2 : seq (A * B)) :
    split (s1 ++ s2) = ((split s1).1 ++ (split s2).1, (split s1).2 ++ (split s2).2).
  Proof.
    elim: s1 => [| [hd1a hd1b] tl1 IH] //=.
    - by case: (split s2).
    - move: IH. case: (split (tl1 ++ s2)) => [cs1 cs2].
      case: (split tl1) => [tl11 tl12]. case: (split s2) => [tl21 tl22] /=.
      case=> ? ?; subst. reflexivity.
  Qed.

  Lemma split_rcons (s : seq (A * B)) (x : A * B) :
    split (rcons s x) = (rcons (split s).1 x.1, rcons (split s).2 x.2).
  Proof.
    move: s x. apply: last_ind.
    - move=> [xa xb] /=. reflexivity.
    - move=> s [ya yb] IH [xa xb] /=. rewrite IH /=.
      rewrite -(cats1 s) rcons_cat. rewrite split_cat /=.
      rewrite -cats1 cat_rcons. rewrite -cats1 cat_rcons. reflexivity.
  Qed.

  Lemma split_rev (s : seq (A * B)) :
    split (rev s) = (rev (split s).1, rev (split s).2).
  Proof.
    elim: s => [| [hda hdb] tl IH] //=. rewrite rev_cons.
    rewrite split_rcons. rewrite IH /=. case: (split tl) => [s1 s2] /=.
    rewrite !rev_cons. reflexivity.
  Qed.

  Lemma catrevs0 (s : seq A) : catrev s [::] = rev s.
  Proof. by rewrite catrevE cats0. Qed.

  Lemma catrev0s (s : seq A) : catrev [::] s = s.
  Proof. reflexivity. Qed.

  Lemma in_map_exists (s : seq A) (f : A -> B) (x : B) :
    In x (map f s) -> exists y, In y s /\ x = f y.
  Proof.
    elim: s => [| hd tl IH] //=. case=> Hin.
    - subst. exists hd. tauto.
    - move: (IH Hin) => [y [Hiny Hxy]]. exists y. tauto.
  Qed.

  Lemma In_rev x (s : seq A) :
    In x (rev s) <-> In x s.
  Proof.
    elim: s => [| e s IH] //=. move: IH => [IH1 IH2].
    rewrite rev_cons. split => H.
    - case/In_rcons: H => H.
      + right; exact: (IH1 H).
      + left; rewrite H; reflexivity.
    - apply/In_rcons. case: H => H.
      + right; rewrite H; reflexivity.
      + left; exact: (IH2 H).
  Qed.

  Lemma catrev_rev (s1 s2 : seq A) :
    catrev (rev s1) s2 = s1 ++ s2.
  Proof.
    move: s1 s2. apply: last_ind => [| s1 x1 IH1] s2 //=.
    rewrite rev_rcons /= IH1. rewrite cat_rcons. reflexivity.
  Qed.

  (* all, has, Forall, and Exists *)

  Lemma all_Forall (P : pred A) (s : seq A) :
    all P s <-> Forall P s.
  Proof.
    split.
    - elim: s => [| e s IH] //=. move/andP=> [H1 H2]. move: (IH H2) => {}H2.
      by apply: Forall_cons.
    - elim: s => [| e s IH] //=. move=> /Forall_cons_iff [H1 H2].
      by rewrite H1 (IH H2).
  Qed.

  Lemma all_forall (P : pred A) (s : seq A) :
    all P s <-> (forall e, In e s -> P e).
  Proof.
    split => H.
    - apply/Forall_forall. apply/all_Forall. assumption.
    - apply/all_Forall. apply/Forall_forall. assumption.
  Qed.

  Lemma has_Exists (P : pred A) (s : seq A) :
    has P s <-> Exists P s.
  Proof.
    split.
    - elim: s => [| e s IH] //=. case/orP=> H.
      + apply: Exists_cons_hd. assumption.
      + apply: Exists_cons_tl. exact: (IH H).
    - elim: s => [| e s IH] //=.
      + move/Exists_nil. by elim.
      + case/Exists_cons => H.
        * by rewrite H.
        * by rewrite (IH H) orbT.
  Qed.

  Lemma has_exists (P : pred A) (s : seq A) :
    has P s <-> exists e, In e s /\ P e.
  Proof.
    split.
    - move/has_Exists. move/Exists_exists. by apply.
    - move/Exists_exists. move/has_Exists. by apply.
  Qed.

  Lemma all_flatten (P : pred A) (ss : seq (seq A)) :
    all P (flatten ss) = all (all P) ss.
  Proof.
    elim: ss => [| s ss IH] //=. rewrite all_cat IH. reflexivity.
  Qed.

  Lemma has_flatten (P : pred A) (ss : seq (seq A)) :
    has P (flatten ss) = has (has P) ss.
  Proof.
    elim: ss => [| s ss IH] //=. rewrite has_cat IH. reflexivity.
  Qed.

  Lemma all_in (P : pred A) (s : seq A) (x : A) :
    all P s -> In x s -> P x.
  Proof. move/all_forall. by apply. Qed.

End SeqLemmas.


(** Lemmas for foldl and folr *)

Section Fold.

  Context {A : Type} {B : Type} {R : relation B} {E : Equivalence R}.

  Context {f : B -> A -> B}.

  Context {g : A -> B -> B}.

  Context {Rf_swap : forall (a1 a2 : A) (b : B),
              R (f (f b a1) a2) (f (f b a2) a1)}.

  Context {R_foldl : forall (b1 b2 : B) (ls : seq A),
              R b1 b2 -> R (foldl f b1 ls) (foldl f b2 ls)}.

  Lemma foldl_fold_left a s : foldl f a s = fold_left f s a.
  Proof. by elim: s a => [| x s IH] a //=. Qed.

  Lemma foldr_fold_right a s : foldr g a s = fold_right g a s.
  Proof. reflexivity. Qed.

  Lemma foldl_map {C : Type} (h : C -> A) r s :
    foldl f r (map h s) = foldl (fun x y => f x (h y)) r s.
  Proof. by elim: s r => [| x s IH] r //=. Qed.

  Lemma foldl_cons (hd : A) (tl : seq A) (r : B) :
    R (foldl f r (hd::tl)) (f (foldl f r tl) hd).
  Proof.
    elim: tl hd r => /=.
    - move=> hd r. reflexivity.
    - move=> tl_hd tl_tl IH hd r. rewrite -(IH hd (f r tl_hd)).
      move: (Rf_swap tl_hd hd r) => H. rewrite (R_foldl _ H). reflexivity.
  Qed.

  Lemma flodr_cons r x s : foldr g r (x::s) = g x (foldr g r s).
  Proof. reflexivity. Qed.

  Lemma foldr_rev r s : foldr g r (rev s) = foldl (fun r x => g x r) r s.
  Proof.
    elim: s r => [| x s IH] r //=. rewrite rev_cons foldr_rcons. rewrite IH.
    reflexivity.
  Qed.

End Fold.


(** Tail-recursive flatten, the result is the reverse of flatten *)

Section TailRecursiveFlatten.

  Context {A : Type}.

  Definition tflatten (ss : seq (seq A)) := foldl (fun r s => catrev s r) [::] ss.

  Lemma tflatten_flatten ss : tflatten ss = rev (flatten ss).
  Proof.
    rewrite /tflatten. rewrite -(cats0 (rev (flatten ss))).
    move: [::]. move: ss. apply: last_ind => [| ss x IH] l //=.
    rewrite flatten_rcons. rewrite rev_cat -catA. rewrite -IH.
    rewrite foldl_rcons. rewrite catrevE. reflexivity.
  Qed.

  Lemma tflatten_cons s ss : tflatten (s::ss) = (tflatten ss) ++ (rev s).
  Proof. rewrite !tflatten_flatten /=. rewrite rev_cat. reflexivity. Qed.

  Lemma tflatten_rcons ss s :
    tflatten (rcons ss s) = rev s ++ tflatten ss.
  Proof. rewrite !tflatten_flatten. rewrite flatten_rcons rev_cat. reflexivity. Qed.

  Lemma tflattens_cat ss1 ss2 :
    tflatten (ss1 ++ ss2) = tflatten ss2 ++ tflatten ss1.
  Proof. rewrite !tflatten_flatten. rewrite flatten_cat rev_cat. reflexivity. Qed.

  Lemma filter_tflatten ss (p : pred A) :
    filter p (tflatten ss) = tflatten [seq filter p i | i <- ss].
  Proof.
    rewrite (tflatten_flatten [seq filter p i | i <- ss]).
    rewrite -filter_flatten. rewrite -filter_rev. rewrite -tflatten_flatten.
    reflexivity.
  Qed.

  Lemma all_tflatten (p : pred A) ss :
    all p (tflatten ss) = all (all p) ss.
  Proof. rewrite tflatten_flatten. rewrite all_rev. exact: all_flatten. Qed.

  Lemma has_tflatten (p : pred A) ss :
    has p (tflatten ss) = has (has p) ss.
  Proof. rewrite tflatten_flatten. rewrite has_rev. exact: has_flatten. Qed.

End TailRecursiveFlatten.

Lemma map_tflatten {A B : Type} (f : A -> B) ss :
  map f (tflatten ss) = tflatten (map (map f) ss).
Proof.
  rewrite (tflatten_flatten (map (map f) ss)). rewrite -map_flatten.
  rewrite -map_rev. rewrite -tflatten_flatten. reflexivity.
Qed.


(* Tail-recursive maps.
   mapr: the result is the reverse of map
   tmap: the result is the same as map *)

Section MapRev.

  Context {A : Type} {B : Type}.

  Variable f : A -> B.

  Fixpoint mapr_rec res es :=
    match es with
    | [::] => res
    | hd::tl => mapr_rec (f hd::res) tl
    end.

  Definition mapr es := mapr_rec [::] es.

  Lemma mapr_rec_rev_map res es : mapr_rec res es = rev (map f es) ++ res.
  Proof.
    elim: es res => [| e es IH] res //=. rewrite IH. rewrite rev_cons.
    rewrite cat_rcons. reflexivity.
  Qed.

  Lemma mapr_rev_map es : mapr es = rev (map f es).
  Proof. rewrite /mapr. rewrite mapr_rec_rev_map. by rewrite cats0. Qed.

  Lemma mapr_map es : mapr es = map f (rev es).
  Proof. rewrite map_rev. exact: mapr_rev_map. Qed.

  Lemma mapr_rec_cons res e es : mapr_rec res (e::es) = mapr_rec (f e::res) es.
  Proof. reflexivity. Qed.

  Lemma mapr_rec_split res es : mapr_rec res es = mapr_rec [::] es ++ res.
  Proof.
    elim: es res => [| e es IH] //= res. rewrite (IH (f e::res)).
    rewrite (IH [:: f e]). rewrite -cat_rcons. rewrite -cats1. reflexivity.
  Qed.

  Lemma mapr_cons e es : mapr (e::es) = rcons (mapr es) (f e).
  Proof.
    rewrite !mapr_map. rewrite rev_cons map_rcons. reflexivity.
  Qed.

  Lemma mapr_rec_rcons res es e :
    mapr_rec res (rcons es e) = f e :: mapr_rec res es.
  Proof. by elim: es res e => [| e1 es IH] //=. Qed.

  Lemma mapr_rcons es e : mapr (rcons es e) = f e :: mapr es.
  Proof. exact: mapr_rec_rcons. Qed.

  Lemma mapr_rec_cat res es1 es2 :
    mapr_rec res (es1 ++ es2) = mapr_rec (mapr_rec res es1) es2.
  Proof. by elim: es1 res es2 => [| e1 es1 IH] res es2 //=. Qed.

  Lemma mapr_cat es1 es2 : mapr (es1 ++ es2) = mapr es2 ++ mapr es1.
  Proof.
    rewrite !mapr_map. rewrite rev_cat map_cat. reflexivity.
  Qed.

  Lemma size_mapr es : size (mapr es) = size es.
  Proof.
    rewrite mapr_map. rewrite size_map size_rev. reflexivity.
  Qed.

  Lemma mapr_rev es : mapr (rev es) = map f es.
  Proof.
    elim: es => [| e es IH] //=. rewrite rev_cons. rewrite mapr_rcons.
    rewrite IH. reflexivity.
  Qed.


  Definition tmap es := mapr (rev es).

  Lemma tmap_map es : tmap es = map f es.
  Proof. rewrite /tmap mapr_rev. reflexivity. Qed.

  Lemma in_tmap e es : In e es -> In (f e) (tmap es).
  Proof.
    rewrite tmap_map. exact: in_map.
  Qed.

End MapRev.

Section FlattenMap.

  Lemma in_flatten {A : Type} x (ss : seq (seq A)) :
    In x (flatten ss) <-> exists s, In s ss /\ In x s.
  Proof.
    elim: ss => [| s ss IH] //=.
    - split => //=. move=> [s H]. tauto.
    - move: IH => [IH1 IH2]. split => H.
      + case: (in_cat H) => {}H.
        * exists s. split; [ by left | assumption ].
        * move: (IH1 H) => [t [Hint Hinx]]. exists t; tauto.
      + move: H => [t [Hint Hinx]]. case: Hint => Hint.
        * subst. apply: in_cat_l. assumption.
        * apply: in_cat_r. apply: IH2. exists t. tauto.
  Qed.

  Lemma in_tflatten {A : Type} x (ss : seq (seq A)) :
    In x (tflatten ss) <-> exists s, In s ss /\ In x s.
  Proof.
    rewrite tflatten_flatten. move: (in_flatten x ss) => Hin. split => H.
    - move/In_rev: H. tauto.
    - apply/In_rev. tauto.
  Qed.

  Lemma in_flatten_map {A B : Type} (f : B -> seq A) x e (s : seq B) :
    In e s ->
    In x (f e) ->
    In x (flatten (map f s)).
  Proof.
    move=> Hine Hinx. apply/in_flatten. exists (f e). split; [| assumption ].
    apply: in_map. assumption.
  Qed.

  Lemma in_tflatten_tmap {A B : Type} (f : B -> seq A) x e (s : seq B) :
    In e s ->
    In x (f e) ->
    In x (tflatten (tmap f s)).
  Proof.
    move=> H1 H2. rewrite tflatten_flatten tmap_map.
    apply/In_rev. exact: (in_flatten_map H1 H2).
  Qed.

End FlattenMap.


(** Tail-recursive append. *)

Section TailRecursiveAppend.

  Context {A : Type}.

  Definition tappend (es1 es2 : seq A) := rev_append (rev es1) es2.

  Lemma tappend_cat es1 es2 : tappend es1 es2 = es1 ++ es2.
  Proof.
    rewrite /tappend. move: es1 es2. apply: last_ind => [| es1 e1 IH1] es2 //=.
    rewrite rev_rcons /=. rewrite IH1. rewrite cat_rcons. reflexivity.
  Qed.

End TailRecursiveAppend.



(** Lemmas for sequences of eqType *)

Section EqSeqLemmas.

  Variable A : eqType.

  Variable B : eqType.

  Lemma singleton_eq (x y : A) : ([::x] == [::y]) = (x == y).
  Proof.
    case H: (x == y).
    - by rewrite (eqP H) eqxx.
    - apply/negP => /eqP [] Heq. by rewrite Heq eqxx in H.
  Qed.

  Lemma in_In (x : A) (s : seq A) : x \in s <-> In x s.
  Proof.
    elim: s => [| y ys IH] //=. rewrite in_cons. case H: (x == y) => /=.
    - split.
      + move=> _. left. rewrite (eqP H). reflexivity.
      + done.
    - split.
      + move=> Hin. right. apply/IH. exact: Hin.
      + case.
        * move=> Hyx; rewrite Hyx eqxx in H; discriminate.
        * move/IH. by apply.
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

  Lemma cat_nseql (x : A) s1 s2 n :
    s1 ++ s2 = nseq n x -> s1 = nseq (size s1) x.
  Proof.
    move=> H. have: size (s1 ++ s2) = size (nseq n x) by rewrite H.
    rewrite size_cat size_nseq => Hn. rewrite -Hn in H.
    rewrite nseq_addn in H. move/eqP: H. rewrite eqseq_cat; last by rewrite size_nseq.
    move/andP=> [/eqP <- _]. reflexivity.
  Qed.

  Lemma cat_nseqr (x : A) s1 s2 n :
    s1 ++ s2 = nseq n x -> s2 = nseq (size s2) x.
  Proof.
    move=> H. have: size (s1 ++ s2) = size (nseq n x) by rewrite H.
    rewrite size_cat size_nseq => Hn. rewrite -Hn in H.
    rewrite nseq_addn in H. move/eqP: H. rewrite eqseq_cat; last by rewrite size_nseq.
    move/andP=> [_ /eqP <-]. reflexivity.
  Qed.

  Lemma in_rcons (x : A) s (y : A) :
    x \in rcons s y = (x \in s) || (x == y).
  Proof. rewrite mem_rcons in_cons orbC. reflexivity. Qed.

  Lemma in_rev (x : A) s :
    (x \in rev s) = (x \in s).
  Proof.
    elim: s => [| y s IH] //=. rewrite rev_cons in_rcons IH in_cons orbC.
    reflexivity.
  Qed.

  Lemma in_split_rev_l {C : Type} (x : A) (s : seq (A * C)) :
    (x \in (split (rev s)).1) = (x \in (split s).1).
  Proof.
    rewrite split_rev /=. rewrite mem_rev. reflexivity.
  Qed.

  Lemma in_split_rev_r {C : Type} (x : B) (s : seq (C * B)) :
    (x \in (split (rev s)).2) = (x \in (split s).2).
  Proof.
    rewrite split_rev /=. rewrite mem_rev. reflexivity.
  Qed.


  (* Tail-recursive filter function, the result is the reverse of filter *)

  Variable p : pred A.

  Definition tfilter es := foldl (fun r x => if p x then x::r else r) [::] es.

  Lemma tfilter_filter es : tfilter es = filter p (rev es).
  Proof.
    rewrite -(cats0 (filter p (rev es))). rewrite /tfilter. rewrite filter_rev.
    move: [::]. elim: es => [| e es IH] r //=. case: (p e).
    - rewrite rev_cons. rewrite cat_rcons. rewrite -IH. reflexivity.
    - exact: IH.
  Qed.

  Lemma tfilter_cat es1 es2 : tfilter (es1 ++ es2) = tfilter es2 ++ tfilter es1.
  Proof.
    rewrite !tfilter_filter. rewrite rev_cat filter_cat. reflexivity.
  Qed.

  Lemma tfilter_rcons es e :
    tfilter (rcons es e) = if p e
                           then e::(tfilter es)
                           else tfilter es.
  Proof.
    rewrite !tfilter_filter. rewrite rev_rcons /=. reflexivity.
  Qed.

  Lemma tfilter_cons e es :
    tfilter (e::es) = if p e
                      then rcons (tfilter es) e
                      else tfilter es.
  Proof.
    rewrite !tfilter_filter. rewrite rev_cons filter_rcons. reflexivity.
  Qed.

  Lemma tfilter_nil : tfilter [::] = [::].
  Proof. reflexivity. Qed.

End EqSeqLemmas.


(* Tail-recursive zip *)

Section TailRecursiveZip.

  Context {A : Type} {B : Type}.

  Fixpoint zipr_rec res_rev (xs : seq A) (ys : seq B) : seq (A * B) :=
    match xs, ys with
    | _, [::]
    | [::], _ => res_rev
    | x::xs, y::ys => zipr_rec ((x, y)::res_rev) xs ys
    end.

  Definition zipr (xs : seq A) (ys : seq B) : seq (A * B) := zipr_rec [::] xs ys.

  Definition unzip1r := mapr (@fst A B).

  Definition unzip2r := mapr (@snd A B).

  Lemma zipr_rec_cons r x xs y ys : zipr_rec r (x::xs) (y::ys) = zipr_rec ((x, y)::r) xs ys.
  Proof. reflexivity. Qed.

  Lemma zipr_zip xs ys : zipr xs ys = rev (zip xs ys).
  Proof.
    rewrite /zipr. rewrite -(cats0 (rev (zip xs ys))). move: [::].
    elim: xs ys => [| x xs IHx] [| y ys] r //=. rewrite IHx. rewrite rev_cons.
    rewrite cat_rcons. reflexivity.
  Qed.

  Lemma unzip1r_unzip1 s : unzip1r s = rev (unzip1 s).
  Proof. rewrite /unzip1r. rewrite mapr_map map_rev. reflexivity. Qed.

  Lemma unzip2r_unzip2 s : unzip2r s = rev (unzip2 s).
  Proof. rewrite /unzip2r. rewrite mapr_map map_rev. reflexivity. Qed.

  Lemma zipr_cons x xs y ys : zipr (x::xs) (y::ys) = rcons (zipr xs ys) (x, y).
  Proof. rewrite !zipr_zip /=. rewrite rev_cons. reflexivity. Qed.

  Lemma zipr_rcons xs x ys y :
    size xs = size ys -> zipr (rcons xs x) (rcons ys y) = (x, y)::(zipr xs ys).
  Proof.
    move=> Hs. rewrite !zipr_zip. rewrite (zip_rcons _ _ Hs).
    rewrite rev_rcons. reflexivity.
  Qed.

  Lemma zipr_cat xs1 xs2 ys1 ys2 :
    size xs1 = size ys1 -> zipr (xs1 ++ xs2) (ys1 ++ ys2) = zipr xs2 ys2 ++ zipr xs1 ys1.
  Proof.
    move=> Hs. rewrite !zipr_zip. rewrite (zip_cat _ _ Hs). rewrite rev_cat.
    reflexivity.
  Qed.

  Lemma rev_zipr xs ys : size xs = size ys -> rev (zipr xs ys) = zipr (rev xs) (rev ys).
  Proof.
    move=> Hs. rewrite !zipr_zip. rewrite (rev_zip Hs). reflexivity.
  Qed.

  Lemma unzip1_zipr s t : size s <= size t -> unzip1 (zipr s t) = rev s.
  Proof.
    rewrite zipr_zip => Hs. move: (unzip1_zip Hs). rewrite /unzip1.
    rewrite map_rev. move=> ->. reflexivity.
  Qed.

  Lemma unzip2_zipr s t : size t <= size s -> unzip2 (zipr s t) = rev t.
  Proof.
    rewrite zipr_zip => Hs. move: (unzip2_zip Hs). rewrite /unzip2.
    rewrite map_rev. move=> ->. reflexivity.
  Qed.

  Lemma unzip1r_zipr s t : size s <= size t -> unzip1r (zipr s t) = s.
  Proof.
    rewrite unzip1r_unzip1 => Hs. rewrite (unzip1_zipr Hs). by rewrite revK.
  Qed.

  Lemma unzip2r_zipr s t : size t <= size s -> unzip2r (zipr s t) = t.
  Proof.
    rewrite unzip2r_unzip2 => Hs. rewrite (unzip2_zipr Hs). by rewrite revK.
  Qed.

  Lemma size1_zipr s t : size s <= size t -> size (zipr s t) = size s.
  Proof.
    rewrite zipr_zip => Hs. rewrite size_rev. rewrite (size1_zip Hs). reflexivity.
  Qed.

  Lemma size2_zipr s t : size t <= size s -> size (zipr s t) = size t.
  Proof.
    rewrite zipr_zip => Hs. rewrite size_rev. rewrite (size2_zip Hs). reflexivity.
  Qed.

  Lemma size_zipr xs ys : size (zipr xs ys) = minn (size xs) (size ys).
  Proof. rewrite zipr_zip size_rev size_zip. reflexivity. Qed.

  Lemma nth_zipr x y s t i :
    size s = size t -> nth (x, y) (zipr s t) i = (nth x (rev s) i, nth y (rev t) i).
  Proof.
    move=> Hs. rewrite zipr_zip. rewrite (rev_zip Hs). rewrite nth_zip; first reflexivity.
    rewrite !size_rev; assumption.
  Qed.

  Lemma zipr_map {C : eqType} (f : C -> A) (g : C -> B) (s : seq C) :
    zipr (map f s) (map g s) = mapr (fun x => (f x, g x)) s.
  Proof. rewrite zipr_zip. rewrite zip_map mapr_map map_rev. reflexivity. Qed.

  Lemma zipr_mapr {C : eqType} (f : C -> A) (g : C -> B) (s : seq C) :
    zipr (mapr f s) (mapr g s) = map (fun x => (f x, g x)) s.
  Proof.
    rewrite zipr_zip. rewrite !mapr_map !map_rev.
    rewrite rev_zip; last by rewrite !size_rev !size_map. rewrite !revK.
    rewrite zip_map. reflexivity.
  Qed.

End TailRecursiveZip.

Section ZipLemmas.

  Context {A : eqType} {B : eqType}.

  Lemma unzip1_l_nil (pairs : seq (A * B)) :
    (unzip1 pairs == [::]) = (pairs == [::]).
  Proof. by rewrite /unzip1 map_l_nil. Qed.

  Lemma unzip2_l_nil (pairs : seq (A * B)) :
    (unzip2 pairs == [::]) = (pairs == [::]).
  Proof. by rewrite /unzip2 map_l_nil. Qed.

End ZipLemmas.


Section Map2.

  Context {S T U : Type}.

  Context (f : S -> T -> U).

  (* This function is tail-recursive. *)
  Definition map2 (s : seq S) (t : seq T) : seq U :=
    mapr (fun '(a, b) => f a b) (zipr s t).

  Lemma map2s0 s : map2 s [::] = [::].
  Proof. by case: s. Qed.

  Lemma map20s t : map2 [::] t = [::].
  Proof. by case: t. Qed.

  Lemma map2_cons s ss t tt : map2 (s::ss) (t::tt) = (f s t)::(map2 ss tt).
  Proof. rewrite /map2. rewrite zipr_cons mapr_rcons. reflexivity. Qed.

  Lemma map2_rcons ss s tt t :
    size ss = size tt ->
    map2 (rcons ss s) (rcons tt t) = rcons (map2 ss tt) (f s t).
  Proof.
    move=> Hs. rewrite /map2 (zipr_rcons _ _ Hs). rewrite mapr_cons. reflexivity.
  Qed.

  Lemma map2_cat ss1 ss2 tt1 tt2 :
    size ss1 = size tt1 ->
    map2 (ss1 ++ ss2) (tt1 ++ tt2) = (map2 ss1 tt1) ++ (map2 ss2 tt2).
  Proof.
    move=> Hs. rewrite /map2. rewrite (zipr_cat _ _ Hs). rewrite mapr_cat. reflexivity.
  Qed.

  Lemma map2_equal_size ss tt :
    map2 ss tt = map2 (take (minn (size ss) (size tt)) ss)
                      (take (minn (size ss) (size tt)) tt).
  Proof.
    elim: ss tt => [| s ss IH] [| t tt] //=. rewrite map2_cons. rewrite !minnSS.
    rewrite !take_cons map2_cons. rewrite -IH. reflexivity.
  Qed.

  Lemma map2_size_gt_l ss tt :
    size tt < size ss -> map2 ss tt = map2 (take (size tt) ss) tt.
  Proof.
    move=> Hs. rewrite map2_equal_size /minn. move: (ltn_geF Hs).
    rewrite leq_eqVlt. move/Bool.orb_false_elim => [_ {}Hs]. rewrite Hs take_size.
    reflexivity.
  Qed.

  Lemma map2_size_gt_r ss tt :
    size ss < size tt -> map2 ss tt = map2 ss (take (size ss) tt).
  Proof.
    move=> Hs. rewrite map2_equal_size /minn. rewrite Hs take_size.
    reflexivity.
  Qed.

End Map2.

Section Map2SSS.

  Context {S : Type}.
  Context (f : S -> S -> S).
  Context {f_commutative : commutative f}.
  Context {f_associative : associative f}.
  Context {f_idempotent : idempotent f}.

  Lemma map2_comm xs ys : map2 f xs ys = map2 f ys xs.
  Proof.
    elim: xs ys => [| x xs IH] [| y ys] //=.
    rewrite !map2_cons. rewrite f_commutative IH. reflexivity.
  Qed.

  Lemma map2_assoc xs ys zs : map2 f xs (map2 f ys zs) = map2 f (map2 f xs ys) zs.
  Proof.
    elim: xs ys zs => [| x xs IH] //=.
    - move=> ys zs. rewrite !map20s. reflexivity.
    - case=> [| y ys] //=.
      + move=> zs. rewrite map20s map2s0. reflexivity.
      + case=> [| z zs] //=.
        * rewrite !map2s0. reflexivity.
        * rewrite !map2_cons. rewrite f_associative IH. reflexivity.
  Qed.

  Lemma map2_idem xs : map2 f xs xs = xs.
  Proof.
    elim: xs => [| x xs IH] //=. rewrite map2_cons f_idempotent IH. reflexivity.
  Qed.

End Map2SSS.


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

  Lemma prefix_of_cat s1 s2 s3 :
    prefix_of s1 s2 -> prefix_of s1 (s2 ++ s3).
  Proof.
    move: s3 s2. apply: last_ind => [| s3 x IH] s2 Hpre12 //=.
    - rewrite cats0. assumption.
    - rewrite -rcons_cat. apply: prefix_of_rcons. exact: (IH _ Hpre12).
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


Section ExtSeq.

  Context {A : Type} (a : A).
  (* Extend a sequence *)
  Fixpoint extseq (xs ys : seq A) :=
    match xs, ys with
    | _, [::] => [::]
    | [::], _::ys => a::(extseq xs ys)
    | x::xs, y::ys => x::(extseq xs ys)
    end.

  Lemma extseq_cons x xs y ys :
    extseq (x::xs) (y::ys) = x::(extseq xs ys).
  Proof. reflexivity. Qed.

  Lemma extseqs0 xs : extseq xs [::] = [::].
  Proof. by elim: xs => [| x xs IH] //=. Qed.

  Lemma extseq0s ys : extseq [::] ys = nseq (size ys) a.
  Proof.
    elim: ys => [| y ys IH] //=. rewrite IH. reflexivity.
  Qed.

  Lemma extseq_eqsize xs ys : size xs = size ys -> extseq xs ys = xs.
  Proof.
    elim: xs ys => [| x xs IH] [| y ys] //= Hs. move: (eq_add_S _ _ Hs) => {}Hs.
    rewrite (IH _ Hs). reflexivity.
  Qed.

  Lemma extseq_lesize xs ys :
    size xs <= size ys -> extseq xs ys = xs ++ nseq (size ys - size xs) a.
  Proof.
    elim: xs ys => [| x xs IH] [| y ys] //=.
    - move=> _. rewrite extseq0s. reflexivity.
    - move=> Hs. move: (ltnSE Hs) => {}Hs. rewrite subSS. rewrite (IH _ Hs).
      reflexivity.
  Qed.

  Lemma extseq_gesize xs ys : size ys <= size xs -> extseq xs ys = take (size ys) xs.
  Proof.
    elim: xs ys => [| x xs IH] [| y ys] //=. move=> Hs. move: (ltnSE Hs) => {}Hs.
    rewrite (IH _ Hs). reflexivity.
  Qed.

  Lemma size_extseq xs ys : size (extseq xs ys) = size ys.
  Proof.
    case Hseq: (size xs == size ys).
    - rewrite (extseq_eqsize (eqP Hseq)). exact: (eqP Hseq).
    - case/orP: (leq_total (size xs) (size ys)) => Hs.
      + rewrite (extseq_lesize Hs). rewrite seq.size_cat size_nseq.
        rewrite (subnKC Hs). reflexivity.
      + rewrite (extseq_gesize Hs). rewrite size_take. rewrite leq_eqVlt in Hs.
        rewrite eq_sym in Hseq. rewrite Hseq /= in Hs. rewrite Hs. reflexivity.
  Qed.

End ExtSeq.
