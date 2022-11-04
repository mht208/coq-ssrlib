
From Coq Require Import Arith ZArith OrderedType Lia.
From mathcomp Require Import ssreflect eqtype ssrbool ssrnat ssralg ssrfun choice.
From ssrlib Require Import Types SsrOrder Nats Compatibility.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "m <=? n <=? p" (at level 70, n at next level).
Reserved Notation "m <? n <=? p" (at level 70, n at next level).
Reserved Notation "m <=? n <? p" (at level 70, n at next level).
Reserved Notation "m <? n <? p" (at level 70, n at next level).



(** Positive is an eqType, a choiceType, and a countType. *)

Section PositiveEqType.

  Local Open Scope positive_scope.

  Lemma pos_eqP : forall (n m : positive), reflect (n = m) (n =? m).
  Proof.
    move=> n m.
    move: (Pos.eqb_eq n m) => [H1 H2].
    case H: (n =? m).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hnm.
      move: (H2 Hnm).
      by rewrite H.
  Qed.

  Definition pos_pickle (n : positive) : nat :=
    ssrnat.subn (Pos.to_nat n) 1.

  Definition pos_unpickle (n : nat) : option positive :=
    Some (Pos.of_nat (ssrnat.addn n 1)).

  Lemma pos_count : pcancel pos_pickle pos_unpickle.
  Proof.
    move=> n.
    rewrite /pos_unpickle /pos_pickle.
    move: (Pos2Nat.is_succ n) => [m Hm].
    rewrite Hm -ssrnat.addn1 (ssrnat.addnK 1%nat m).
    rewrite (ssrnat.addnC m 1%nat) ssrnat.add1n -Hm.
    rewrite Pos2Nat.id.
    reflexivity.
  Qed.

  Definition pos_eqMixin := EqMixin pos_eqP.
  Definition pos_countMixin := CountMixin pos_count.
  Definition pos_choiceMixin := CountChoiceMixin pos_countMixin.
  Canonical pos_eqType := Eval hnf in EqType positive pos_eqMixin.
  Canonical pos_choiceType := Eval hnf in ChoiceType positive pos_choiceMixin.
  Canonical pos_countType := Eval hnf in CountType positive pos_countMixin.

End PositiveEqType.

Notation "m <=? n <=? p" :=
  ((m <=? n) && (n <=? p))%positive (at level 70, n at next level) : positive_scope.
Notation "m <? n <=? p" :=
  ((m <? n) && (n <=? p))%positive (at level 70, n at next level) : positive_scope.
Notation "m <=? n <? p" :=
  ((m <=? n) && (n <? p))%positive (at level 70, n at next level) : positive_scope.
Notation "m <? n <? p" :=
  ((m <? n) && (n <? p))%positive (at level 70, n at next level) : positive_scope.



Section PositiveLemmas.

  Local Open Scope positive_scope.

  Lemma pos_ltP : forall x y : positive, reflect (x < y) (x <? y).
  Proof.
    move=> x y.
    move: (Pos.ltb_lt x y) => [H1 H2].
    case H: (x <? y).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hlt.
      move: (H2 Hlt).
      by rewrite H.
  Qed.

  Lemma pos_leP : forall x y : positive, reflect (x <= y) (x <=? y).
  Proof.
    move=> x y.
    move: (Pos.leb_le x y) => [H1 H2].
    case H: (x <=? y).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hlt.
      move: (H2 Hlt).
      by rewrite H.
  Qed.

  Lemma pos_le_add_diag_r : forall x y : positive, x <= x + y.
  Proof.
    move=> x y. apply: Pos.lt_le_incl. exact: Pos.lt_add_diag_r.
  Qed.

  Lemma pos_le_add_r (x y z : positive) : (x <= y)%positive -> (x <= y + z)%positive.
  Proof.
    move=> Hxy. apply: (Pos.le_trans _ _ _ Hxy). exact: pos_le_add_diag_r.
  Qed.

  Lemma pos_lt_add_r : forall x y z : positive, x < y -> x < y + z.
  Proof.
    move=> x y z Hxy. apply: (Pos.lt_le_trans _ _ _ Hxy).
    exact: pos_le_add_diag_r.
  Qed.

  Lemma pos_ltb_trans : forall x y z : positive, x <? y -> y <? z -> x <? z.
  Proof.
    move=> x y z /pos_ltP Hxy /pos_ltP Hyz. apply/pos_ltP.
    exact: (Pos.lt_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma pos_ltb_leb_trans : forall x y z : positive, x <? y -> y <=? z -> x <? z.
  Proof.
    move=> x y z /pos_ltP Hxy /pos_leP Hyz. apply/pos_ltP.
    exact: (Pos.lt_le_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma pos_leb_ltb_trans : forall x y z : positive, x <=? y -> y <? z -> x <? z.
  Proof.
    move=> x y z /pos_leP Hxy /pos_ltP Hyz. apply/pos_ltP.
    exact: (Pos.le_lt_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma pos_leb_trans : forall x y z : positive, x <=? y -> y <=? z -> x <=? z.
  Proof.
    move=> x y z /pos_leP Hxy /pos_leP Hyz. apply/pos_leP.
    exact: (Pos.le_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma pos_eqn_ltn_gtn_cases m n : (m == n) || (m <? n) || (n <? m).
  Proof.
    move: (Pos.lt_total m n). case; last case.
    - move/pos_ltP => H. rewrite H orbT /=. reflexivity.
    - move/eqP=> H. rewrite H orTb /=. reflexivity.
    - move/pos_ltP => H. rewrite H orbT /=. reflexivity.
  Qed.

  Lemma pos_leb_add_diag_r :
    forall x y : positive, x <=? x + y.
  Proof.
    move=> x y. apply/pos_leP. apply: Pos.lt_le_incl. exact: Pos.lt_add_diag_r.
  Qed.

  Lemma pos_ltb_add_diag_r :
    forall x y : positive, x <? x + y.
  Proof.
    move=> x y. apply/pos_ltP. exact: Pos.lt_add_diag_r.
  Qed.

  Lemma pos_ltb_leb_incl :
    forall x y : positive, x <? y -> x <=? y.
  Proof.
    move=> x y /pos_ltP Hxy. apply/pos_leP. exact: Pos.lt_le_incl.
  Qed.

  Lemma pos_to_nat_is_pos (p : positive) : (0 < Pos.to_nat p)%nat.
  Proof. apply/ltP. exact: Pos2Nat.is_pos. Qed.

  Lemma pos2nat_is_nonzero n : (Pos.to_nat n <> 0)%N.
  Proof.
    move: (Pos2Nat.is_pos n) => H1 H2. rewrite H2 in H1. move: (lt_ltn H1).
    by rewrite ltnn.
  Qed.

  Lemma pos_xO_double (n : positive) : n~0 = 2 * n.
  Proof. reflexivity. Qed.

  Lemma pos_xI_succ_double (n : positive) : n~1 = (2 * n) + 1.
  Proof. rewrite Pos.xI_succ_xO. reflexivity. Qed.

  Lemma pos_pow_1_l (n : positive) : 1 ^ n = 1.
  Proof.
    move: n. apply: Pos.peano_ind => //=.
    move=> n IH. rewrite Pos.pow_succ_r. rewrite Pos.mul_1_l. assumption.
  Qed.

  Lemma Pos2N_inj_pow n m :
    Pos.to_nat (n ^ m) = (Pos.to_nat n ^ Pos.to_nat m)%N.
  Proof.
    move: m n. apply: Pos.peano_ind.
    - move=> n. rewrite Pos.pow_1_r expn1. reflexivity.
    - move=> m IH n. rewrite Pos.pow_succ_r. rewrite Pos2Nat.inj_mul.
      rewrite IH. rewrite -muln_mul. rewrite -expnS. rewrite -addn1.
      rewrite addn_add. replace 1%N with (Pos.to_nat 1) by reflexivity.
      rewrite -Pos2Nat.inj_add. rewrite Pos.add_1_r. reflexivity.
  Qed.

End PositiveLemmas.



(** N is an eqType, a choiceType, and a countType. *)

Section NEqType.

  Local Open Scope N_scope.

  Lemma N_eqP : forall n m, reflect (n = m) (n =? m).
  Proof.
    move=> n m.
    move: (N.eqb_eq n m) => [H1 H2].
    case H: (n =? m).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hnm.
      move: (H2 Hnm).
      by rewrite H.
  Qed.

  Definition N_pickle (n : N) : nat := N.to_nat n.

  Definition N_unpickle (n : nat) : option N := Some (N.of_nat n).

  Lemma N_count : pcancel N_pickle N_unpickle.
  Proof.
    move=> n.
    rewrite /N_unpickle /N_pickle.
    rewrite Nnat.N2Nat.id.
    reflexivity.
  Qed.

  Definition N_eqMixin := EqMixin N_eqP.
  Definition N_countMixin := CountMixin N_count.
  Definition N_choiceMixin := CountChoiceMixin N_countMixin.
  Canonical N_eqType := Eval hnf in EqType N N_eqMixin.
  Canonical N_choiceType := Eval hnf in ChoiceType N N_choiceMixin.
  Canonical N_countType := Eval hnf in CountType N N_countMixin.

End NEqType.

Notation "m <=? n <=? p" :=
  ((m <=? n) && (n <=? p))%num (at level 70, n at next level) : N_scope.
Notation "m <? n <=? p" :=
  ((m <? n) && (n <=? p))%num (at level 70, n at next level) : N_scope.
Notation "m <=? n <? p" :=
  ((m <=? n) && (n <? p))%num (at level 70, n at next level) : N_scope.
Notation "m <? n <? p" :=
  ((m <? n) && (n <? p))%num (at level 70, n at next level) : N_scope.



Section NLemmas.

  Local Open Scope N_scope.

  Lemma N_ltP : forall x y : N, reflect (x < y) (x <? y).
  Proof.
    move=> x y. move: (N.ltb_lt x y) => [H1 H2]. case H: (x <? y).
    - apply: ReflectT. exact: (H1 H).
    - apply: ReflectF. move=> Hlt. move: (H2 Hlt). by rewrite H.
  Qed.

  Lemma N_leP : forall x y : N, reflect (x <= y) (x <=? y).
  Proof.
    move=> x y. move: (N.leb_le x y) => [H1 H2]. case H: (x <=? y).
    - apply: ReflectT. exact: (H1 H).
    - apply: ReflectF. move=> Hlt. move: (H2 Hlt). by rewrite H.
  Qed.

  Lemma NltSn n : n < n + 1.
  Proof. rewrite N.add_1_r. exact: N.lt_succ_diag_r. Qed.

  Lemma NltnSn n : n <? n + 1.
  Proof. apply/N_ltP. exact: NltSn. Qed.

  Lemma Nltnn n : (n <? n) = false.
  Proof. exact: N.ltb_irrefl. Qed.

  Lemma Nltn_eqF n m : (n <? m) -> (n == m) = false.
  Proof. move/N_ltP => H. apply/eqP. exact: N.lt_neq. Qed.

  Lemma Nltn_trans n m p : (m <? n) -> (n <? p) -> (m <? p).
  Proof.
    move=> /N_ltP Hmn /N_ltP Hnp. apply/N_ltP. exact: (N.lt_trans _ _ _ Hmn Hnp).
  Qed.

  Lemma Nleq_trans n m p : (m <=? n) -> (n <=? p) -> (m <=? p).
  Proof.
    move=> /N_leP Hmn /N_leP Hnp. apply/N_leP. exact: (N.le_trans _ _ _ Hmn Hnp).
  Qed.

  Lemma Nleq_ltn_trans n m p : (m <=? n) -> (n <? p) -> (m <? p).
  Proof.
    move=> /N_leP Hmn /N_ltP Hnp. apply/N_ltP. exact: (N.le_lt_trans _ _ _ Hmn Hnp).
  Qed.

  Lemma Nltn_leq_trans n m p : (m <? n) -> (n <=? p) -> (m <? p).
  Proof.
    move=> /N_ltP Hmn /N_leP Hnp. apply/N_ltP. exact: (N.lt_le_trans _ _ _ Hmn Hnp).
  Qed.

  Lemma N_eqn_ltn_gtn_cases m n : (m == n) || (m <? n) || (n <? m).
  Proof.
    move: (N.lt_total m n). case; last case.
    - move/N_ltP => H. rewrite H orbT /=. reflexivity.
    - move/eqP=> H. rewrite H orTb /=. reflexivity.
    - move/N_ltP => H. rewrite H orbT /=. reflexivity.
  Qed.

  Lemma Nltn0Sn n : 0 <? n + 1.
  Proof. apply/N_ltP. apply: N.add_pos_r. done. Qed.

  Lemma NltnW m n : (m <? n) -> (m <=? n).
  Proof. move=> /N_ltP H. apply/N_leP. exact: (N.lt_le_incl _ _ H). Qed.

  Lemma Nltn_ltnF (n m : N) : n <? m -> m <? n = false.
  Proof.
    move=> H1. apply/negP => H2.  move: (Nltn_trans H1 H2). by rewrite Nltnn.
  Qed.

  Lemma Nltn_neqAlt (n m : N) : n <? m = (n != m) && ~~ (m <? n).
  Proof.
    case H: (n == m).
    - rewrite (eqP H) Nltnn. reflexivity.
    - move/negPf/eqP: H => H. move/(N.lt_gt_cases n m): H. case.
      + move/N_ltP=> H. rewrite H. rewrite (Nltn_ltnF H). reflexivity.
      + move/N_ltP=> H; rewrite H. rewrite (Nltn_ltnF H). reflexivity.
  Qed.

  Lemma Nleqnn n : n <=? n.
  Proof. exact: N.leb_refl. Qed.

  Lemma Nleqn0 n : (n <=? 0) = (n == 0).
  Proof.
    move: (N.le_0_r n) => [H1 H2].
    case H: (n == 0); apply/N_leP.
    - exact: (H2 (eqP H)).
    - move=> Hle.
      move: (H1 Hle) => /eqP Heq.
      by rewrite H in Heq.
  Qed.

  Lemma Nleb_add_diag_r x y : x <=? x + y.
  Proof. apply/N_leP. exact: N.le_add_r. Qed.

  Lemma Nltb_add_diag_r x y : 0 <? y -> x <? x + y.
  Proof. move/N_ltP=> H. apply/N_ltP. exact: (N.lt_add_pos_r _ _ H). Qed.

  Lemma Nltb_leb_incl x y : x <? y -> x <=? y.
  Proof. move/N_ltP=> H. apply/N_leP. exact: (N.lt_le_incl _ _ H). Qed.

  Lemma Nsubn0 n : n - 0 = n.
  Proof. exact: (N.sub_0_r n). Qed.

  Lemma Nleq_eqVlt m n : (m <=? n) = (m == n) || (m <? n).
  Proof.
    move: (N.lt_eq_cases m n) => [H1 H2].
    symmetry.
    case H: (m <=? n).
    - apply/orP.
      move/N_leP: H => H.
      case: (H1 H) => {} H.
      + right; apply/N_ltP; assumption.
      + left; apply/eqP; assumption.
    - apply/negP => /orP Hor.
      move/negP: H; apply; apply/N_leP; apply: H2.
      case: Hor => H.
      + right; apply/eqP; assumption.
      + left; apply/N_ltP; assumption.
  Qed.

  Lemma NltnS n m : (n <? m + 1) = (n <=? m).
  Proof.
    rewrite N.add_1_r.
    move: (N.lt_succ_r n m) => [H1 H2].
    case Hle: (n <=? m).
    - move/N_leP: Hle => Hle.
      apply/N_ltP.
      exact: (H2 Hle).
    - apply/N_ltP => Hlt.
      move/negP: Hle; apply.
      apply/N_leP.
      exact: (H1 Hlt).
  Qed.

  Lemma Nltn_add2r p m n : ((m + p) <? (n + p)) = (m <? n).
  Proof.
    move: (N.add_lt_mono_r m n p) => [H1 H2].
    case Hlt: (m <? n).
    - move/N_ltP: Hlt => Hlt.
      apply/N_ltP.
      exact: (H1 Hlt).
    - apply/negP => /N_ltP H.
      move/negP: Hlt; apply; apply/N_ltP.
      exact: (H2 H).
  Qed.

  Lemma N2Nat_inj_lt x y : (N.to_nat x < N.to_nat y)%N <-> (x < y)%num.
  Proof.
    case: x; case: y => //=.
    - move=> y. split=> H //=. move: (Pos2Nat.is_pos y) => {} H. exact: (lt_ltn H).
    - move=> x y. split=> H.
      + move/ltn_lt: H => H. move/Pos2Nat.inj_lt: H. done.
      + apply/lt_ltn/Pos2Nat.inj_lt. done.
  Qed.

  Lemma Nat2N_inj_lt x y : (N.of_nat x < N.of_nat y)%num <-> (x < y)%coq_nat.
  Proof.
    split => H.
    - apply: Nats.ltn_lt. move/N2Nat_inj_lt: H => H.
      rewrite !Nnat.Nat2N.id in H. assumption.
    - move: (Nats.lt_ltn H) => {} H. apply/N2Nat_inj_lt.
      rewrite !Nnat.Nat2N.id. assumption.
  Qed.

  Lemma N2Nat_inj_le x y : (N.to_nat x <= N.to_nat y)%N <-> (x <= y)%num.
  Proof.
    split=> H.
    - rewrite leq_eqVlt in H. apply/N.lt_eq_cases. case/orP: H => H.
      + right; move/eqP: H => H. exact: (Nnat.N2Nat.inj _ _ H).
      + left; move/N2Nat_inj_lt: H; by apply.
    - rewrite leq_eqVlt. case/N.lt_eq_cases: H => H.
      + move/N2Nat_inj_lt: H => ->. by rewrite orbT.
      + by rewrite H eqxx orTb.
  Qed.

  Lemma nat_of_bin_pos p :
    nat_of_bin (N.pos p) = nat_of_pos p.
  Proof. reflexivity. Qed.

  Lemma Npos_ge1 p : (1 <= N.pos p)%num.
  Proof. by elim: p. Qed.

End NLemmas.



(** Z is an eqType, a choiceType, and a countType. *)

Section ZEqType.

  Local Open Scope Z_scope.

  Lemma Z_eqP : forall n m, reflect (n = m) (n =? m).
  Proof.
    move=> n m.
    move: (Z.eqb_eq n m) => [H1 H2].
    case H: (n =? m).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hnm.
      move: (H2 Hnm).
      by rewrite H.
  Qed.

  Definition natsum_of_Z (n : Z) : nat + nat :=
    match n with
    | Z0 => inl 0%nat
    | Zpos m => inl (Pos.to_nat m)
    | Zneg m => inr (Pos.to_nat m)
    end.

  Definition Z_of_natsum (n : nat + nat) : Z :=
    match n with
    | inl O => Z0
    | inl (S _ as m) => Zpos (Pos.of_nat m)
    | inr m => Zneg (Pos.of_nat m)
    end.

  Lemma natsum_of_ZK : cancel natsum_of_Z Z_of_natsum.
  Proof.
    move=> n.
    elim: n => /=.
    - reflexivity.
    - move=> p.
      rewrite Pos2Nat.id.
      case H: (Pos.to_nat p).
      + move: (Pos2Nat.is_pos p) => Hp.
        rewrite H in Hp.
        by inversion Hp.
      + reflexivity.
    - move=> p.
      rewrite Pos2Nat.id.
      reflexivity.
  Qed.

  Definition Z_eqMixin := EqMixin Z_eqP.
  Definition Z_countMixin := CanCountMixin natsum_of_ZK.
  Definition Z_choiceMixin := CountChoiceMixin Z_countMixin.
  Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.
  Canonical Z_choiceType := Eval hnf in ChoiceType Z Z_choiceMixin.
  Canonical Z_countType := Eval hnf in CountType Z Z_countMixin.

End ZEqType.

Notation "m <=? n <=? p" :=
  ((m <=? n) && (n <=? p))%Z (at level 70, n at next level) : Z_scope.
Notation "m <? n <=? p" :=
  ((m <? n) && (n <=? p))%Z (at level 70, n at next level) : Z_scope.
Notation "m <=? n <? p" :=
  ((m <=? n) && (n <? p))%Z (at level 70, n at next level) : Z_scope.
Notation "m <? n <? p" :=
  ((m <? n) && (n <? p))%Z (at level 70, n at next level) : Z_scope.



(** Z is a ZmodType *)

Module ZZmod.

  Definition zopp (n : Z) : Z := -n.

  Definition zaddA : associative Z.add := Z.add_assoc.
  Definition zaddC : commutative Z.add := Z.add_comm.
  Definition zadd0 : left_id 0%Z Z.add := Z.add_0_l.
  Lemma zaddN : left_inverse 0%Z zopp Z.add.
  Proof.
    move=> n.
    rewrite /zopp.
    rewrite zaddC.
    exact: Z.add_opp_diag_r.
  Qed.

  Definition Mixin := ZmodMixin zaddA zaddC zadd0 zaddN.

End ZZmod.

Canonical Z_ZmodType := ZmodType Z ZZmod.Mixin.



(** Z is a ring. *)

Module ZRing.

  Definition zmulA : associative Z.mul := Z.mul_assoc.
  Definition zmulC : commutative Z.mul := Z.mul_comm.
  Definition zmul1 : left_id 1%Z Z.mul := Z.mul_1_l.
  Definition zmul_addl : left_distributive Z.mul Z.add := Z.mul_add_distr_r.
  Definition znonzero1 : (1 != 0)%Z := is_true_true.

  Definition comMixin := ComRingMixin zmulA zmulC zmul1 zmul_addl znonzero1.

End ZRing.

Canonical Z_Ring := Eval hnf in RingType Z ZRing.comMixin.
Canonical Z_comRing := Eval hnf in ComRingType Z ZRing.zmulC.



(** EQTYPE modules. *)

Module PositiveEqtype <: EQTYPE.
  Definition t := pos_eqType.
End PositiveEqtype.

Module NEqtype <: EQTYPE.
  Definition t := N_eqType.
End NEqtype.

Module ZEqtype <: EQTYPE.
  Definition t := Z_eqType.
End ZEqtype.



(** Additional Lemmas *)

Section ZLemmas.

  Local Open Scope Z_scope.

  Lemma Z_ltP : forall x y : Z, reflect (x < y) (x <? y).
  Proof.
    move=> x y.
    move: (Z.ltb_lt x y) => [H1 H2].
    case H: (x <? y).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hlt.
      move: (H2 Hlt).
      by rewrite H.
  Qed.

  Lemma Z_leP : forall x y : Z, reflect (x <= y) (x <=? y).
  Proof.
    move=> x y.
    move: (Z.leb_le x y) => [H1 H2].
    case H: (x <=? y).
    - apply: ReflectT.
      exact: (H1 H).
    - apply: ReflectF.
      move=> Hlt.
      move: (H2 Hlt).
      by rewrite H.
  Qed.

  Lemma Z_ltb_trans x y z : x <? y -> y <? z -> x <? z.
  Proof.
    move=> /Z_ltP Hxy /Z_ltP Hyz. apply/Z_ltP. exact: (Z.lt_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma Z_ltb_leb_trans x y z : x <? y -> y <=? z -> x <? z.
  Proof.
    move=> /Z_ltP Hxy /Z_leP Hyz. apply/Z_ltP. exact: (Z.lt_le_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma Z_leb_ltb_trans x y z : x <=? y -> y <? z -> x <? z.
  Proof.
    move=> /Z_leP Hxy /Z_ltP Hyz. apply/Z_ltP. exact: (Z.le_lt_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma Z_leb_trans x y z : x <=? y -> y <=? z -> x <=? z.
  Proof.
    move=> /Z_leP Hxy /Z_leP Hyz. apply/Z_leP. exact: (Z.le_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma Z_eqn_ltn_gtn_cases m n : (m == n) || (m <? n) || (n <? m).
  Proof.
    move: (Z.lt_ge_cases m n). case.
    - move/Z_ltP => H. rewrite H orbT /=. reflexivity.
    - move=> H. move: (Zle_lt_or_eq _ _ H). case=> {H}.
      + move/Z_ltP => H. rewrite H orbT /=. reflexivity.
      + move/eqP=> H. rewrite eq_sym H /=. reflexivity.
  Qed.

  Lemma Zdouble_positive (n : Z) :
    0 <= n -> n <= Z.double n.
  Proof.
    rewrite Z.double_spec -Z.add_diag => H.
    exact: (Z.add_le_mono _ _ _ _ H (Z.le_refl n)).
  Qed.

  Lemma Zdouble_negative (n : Z) :
    n <= 0 -> Z.double n <= n.
  Proof.
    rewrite Z.double_spec -Z.add_diag => H.
    move: (Z.add_le_mono _ _ _ _ (Z.le_refl n) H) => {} H.
    rewrite Z.add_0_r in H.
    exact: H.
  Qed.

  Lemma Zle_plus_r n m p :
    n <= m -> 0 <= p -> n <= m + p.
  Proof.
    move=> Hnm H0p.
    apply: (Z.le_trans _ _ _ Hnm).
    rewrite -{1}(Z.add_0_r m).
    exact: (Zplus_le_compat_l _ _ _ H0p).
  Qed.

  Lemma Zle_plus_l n m p :
    n <= m -> p <= 0 -> n + p <= m.
  Proof.
    move=> Hnm H0p.
    apply: (Z.le_trans _ _ _ _ Hnm).
    rewrite -{2}(Z.add_0_r n).
    exact: (Zplus_le_compat_l _ _ _ H0p).
  Qed.

  Lemma Zle_succ n : n <= Z.succ n.
  Proof.
    apply: (Zle_plus_r (Z.le_refl n)).
    done.
  Qed.

  Lemma two_power_nat_gt_zero n : two_power_nat n > 0.
  Proof.
    rewrite two_power_nat_equiv.
    move: (two_p_gt_ZERO (Z.of_nat n)).
    rewrite two_p_correct.
    apply.
      by induction n.
  Qed.

  Lemma zero_lt_two_power_nat n : 0 < two_power_nat n.
  Proof.
    apply: Z.gt_lt.
    exact: two_power_nat_gt_zero.
  Qed.

  Lemma two_power_of_nat_gt0 n : 2 ^ Z.of_nat n > 0.
  Proof.
    rewrite -two_p_equiv. apply: two_p_gt_ZERO. exact: Nat2Z.is_nonneg.
  Qed.

  Lemma zero_lt_two_power_of_nat n : 0 < 2 ^ Z.of_nat n.
  Proof.
    apply: Z.gt_lt. exact: two_power_of_nat_gt0.
  Qed.

  Lemma two_power_of_nat_ne0 n : 2 ^ Z.of_nat n <> 0.
  Proof.
    move=> H. apply: (Z.lt_neq _ _ (zero_lt_two_power_of_nat n)).
    symmetry. exact: H.
  Qed.

  Lemma ltn_Sdouble n m : n < m -> 2 * n + 1 < 2 * m.
  Proof.
    move=> Hnm.
    rewrite -2!Z.add_diag.
    rewrite -Z.add_assoc.
    apply: Z.add_lt_le_mono.
    - exact: Hnm.
    - apply: Zlt_le_succ.
      exact: Hnm.
  Qed.

  Lemma Sdouble_ltn n m : 2 * n + 1 < 2 * m -> n < m.
  Proof.
    move=> H.
    apply: (Zmult_lt_reg_r _ _ 2).
    - done.
    - rewrite (Z.mul_comm n 2) (Z.mul_comm m 2).
      move: (Z.le_succ_l (2 * n)%Z (2 * m)%Z) => [] H1 _; apply: H1.
      exact: (Z.lt_le_incl _ _ H).
  Qed.

  Lemma Zminus_plus : forall n m : Z, n - m + m = n.
  Proof.
    move=> n m.
    rewrite -Z.add_assoc (Z.add_comm (-m) m) Z.add_opp_diag_r Z.add_0_r.
    reflexivity.
  Qed.

  Lemma Zsplit_l :
    forall h l n p,
      0 <= l < 2^p ->
      h * 2^p + l = n ->
      l = n mod (2^p).
  Proof.
    move=> h l n p Hl Heq.
    apply: (Zmod_unique_full _ _ h).
    - by left.
    - by rewrite Z.mul_comm Heq.
  Qed.

  Lemma Zsplit_h :
    forall h l n p,
      0 <= l < 2^p ->
      h * 2^p + l = n ->
      h = n / (2^p).
  Proof.
    move=> h l n p Hl Heq.
    apply: (Zdiv_unique _ _ _ l).
    - exact: Hl.
    - by rewrite Z.mul_comm Heq.
  Qed.

  Lemma Zpower_nat_gt0 n p :
    n > 0 ->
    Zpower_nat n p > 0.
  Proof.
    elim: p n => /=.
    - done.
    - move=> p IH n Hn.
      exact: (Zmult_gt_0_compat _ _ Hn (IH _ Hn)).
  Qed.

  Lemma Zpow_pos_gt0 n p :
    n > 0 ->
    Z.pow_pos n p > 0.
  Proof.
    rewrite Zpower_pos_nat.
    exact: Zpower_nat_gt0.
  Qed.

  Lemma Zdiv_mul_lt_l x y p :
    0 <= x < p -> 0 <= y < p -> (x * y) / p < p.
  Proof.
    move=> [Hx1 Hx2] [Hy1 Hy2]. have: 0 < p by lia. move=> Hp.
    exact: (Zdiv_lt_upper_bound
              (x * y) p p Hp (Z.mul_lt_mono_nonneg _ _ _ _ Hx1 Hx2 Hy1 Hy2)).
  Qed.

  Lemma Zhalf_bit_double (n : Z) (b : bool) :
    Z.div2 (Z.b2z b + n * 2) = n.
  Proof.
    rewrite Zdiv2_div Z_div_plus.
    - by case: b.
    - done.
  Qed.

  Lemma Zmul2l_add (n : Z) : 2 * n = n + n.
  Proof.
    replace 2 with (Z.succ 1) by reflexivity.
    rewrite Z.mul_succ_l Z.mul_1_l. reflexivity.
  Qed.

  Lemma Zmul2r_add (n : Z) : n * 2 = n + n.
  Proof.
    rewrite Z.mul_comm. exact: Zmul2l_add.
  Qed.

  Lemma Zmod_mul2_sub1 n : 0 < n -> (n * 2 - 1) mod n = n - 1.
  Proof.
    move=> Hn. rewrite Zmul2r_add -Z.add_sub_assoc Z.add_comm.
    rewrite -{2}(Z.mul_1_l n) Z_mod_plus_full Zmod_small; first by reflexivity.
    split.
    - exact: (proj1 (Z.lt_le_pred _ _) Hn).
    - exact: (Z.lt_pred_l).
  Qed.

  Lemma divn_muln2_subn1 n : 0 < n -> (n * 2 - 1) / n = 1.
  Proof.
    move=> Hn1.
    move: (not_eq_sym (Z.lt_neq _ _ Hn1)) => Hn2.
    move: (Z_div_mod_eq (n * 2 - 1) n (Z.lt_gt _ _ Hn1)).
    rewrite (Zmod_mul2_sub1 Hn1).
    replace (n * 2 - 1) with (n + (n - 1)) by ring.
    move=> H. move: (proj1 (Z.add_cancel_r _ _ _) H) => {} H.
    exact: (proj1 (Z.mul_id_r _ _ Hn2) (Logic.eq_sym H)).
  Qed.

  Lemma ltn_ltn_addn_divn x y n :
    0 <= x < n -> 0 <= y < n -> Z.div (x + y) n = 0 \/ Z.div (x + y) n = 1.
  Proof.
    move=> [Hx1 Hx2] [Hy1 Hy2].
    move: (Z.le_lt_trans _ _ _ Hx1 Hx2) => Hn1.
    move: (Z.lt_gt _ _ Hn1) => Hn2.
    move: (not_eq_sym (Z.lt_neq _ _ Hn1)) => Hn3.
    move: (Z.add_le_mono _ _ _ _ Hx1 Hy1) => /= Hxy1.
    move: (Z.add_lt_mono _ _ _ _ Hx2 Hy2) => Hxy2.
    move: (proj1 (Z.lt_le_pred (x + y) (n + n)) Hxy2) => {} Hxy2.
    move: (Z.lt_ge_cases (x + y) n); case => Hxy3.
    - rewrite (Z.div_small _ _ (conj Hxy1 Hxy3)). left; reflexivity.
    - move: (Z_div_le _ _ _ Hn2 Hxy3).
      rewrite (Z_div_same_full _ Hn3) => Hdiv1.
      move: (Z_div_le _ _ _ Hn2 Hxy2).
      rewrite -Zmul2r_add (divn_muln2_subn1 Hn1) => Hdiv2.
      right. exact: (Z.le_antisymm _ _ Hdiv2 Hdiv1).
  Qed.

  Lemma Zdiv_eucl_q (n d q r : Z) :
    (q, r) = Z.div_eucl n d ->
    q = n / d.
  Proof.
    move=> Hqr. rewrite /Z.div -Hqr. reflexivity.
  Qed.

  Lemma Zdiv_eucl_r (n d q r : Z) :
    (q, r) = Z.div_eucl n d ->
    r = n mod d.
  Proof.
    move=> Hqr. rewrite /Z.modulo -Hqr. reflexivity.
  Qed.

  Lemma Zdiv_eucl_q_ge0 (a b : Z) :
    let (q, r) := Z.div_eucl a b in
    0 <= a -> 0 <= b -> 0 <= q.
  Proof.
    set tmp := Z.div_eucl a b.
    have: tmp = Z.div_eucl a b by reflexivity.
    destruct tmp as [q r]. move=> Heucl Ha Hb.
    rewrite (Zdiv_eucl_q Heucl).
    case: (proj1 (Z.lt_eq_cases 0 b) Hb) => {} Hb.
    - exact: (Z.ge_le _ _ (Z_div_ge0 _ _ (Z.lt_gt _ _ Hb) (Z.le_ge _ _ Ha))).
    - by rewrite -Hb Zdiv_0_r.
  Qed.

  Lemma Zmod_sub (n m : Z) :
    m <= n -> n mod m = (n - m) mod m.
  Proof.
    move=> Hmn. rewrite -(Z_mod_plus_full (n - m) 1).
    rewrite Z.mul_1_l. rewrite -Z.sub_sub_distr Z.sub_diag Z.sub_0_r.
    reflexivity.
  Qed.

  Lemma Nat2Z_inj_odd (n : nat) :
    Z.odd (Z.of_nat n) = Nat.odd n.
  Proof.
    elim: n.
    - reflexivity.
    - move=> n IH. rewrite -Nat.add_1_r Nat2Z.inj_add Z.odd_add Nat.odd_add /=.
      rewrite IH.
      reflexivity.
  Qed.

  Lemma Nat2Z_inj_pow (n m : nat) :
    Z.of_nat (Nat.pow n m) = Z.pow (Z.of_nat n) (Z.of_nat m).
  Proof.
    elim: m n.
    - reflexivity.
    - move=> n IH m.
      rewrite Nat2Z.inj_mul IH -!Zpower_nat_Z -Zpower_nat_succ_r.
      reflexivity.
  Qed.

  Corollary Nat2Z_inj_expn (n m : nat) :
    Z.of_nat (ssrnat.expn n m) = Z.pow (Z.of_nat n) (Z.of_nat m).
  Proof.
    rewrite expn_pow. exact: Nat2Z_inj_pow.
  Qed.

  Lemma Zpow_pos_mul_r n x y  :
    Z.pow_pos n (x * y) = Z.pow_pos (Z.pow_pos n x) y.
  Proof.
    rewrite !Z.pow_pos_fold. rewrite Pos2Z.inj_mul.
    rewrite (Z.pow_mul_r _ _ _ (Pos2Z.is_nonneg _) (Pos2Z.is_nonneg _)).
    reflexivity.
  Qed.

  Lemma Zpow_pos_mul_l x y n :
    Z.pow_pos (x * y) n = Z.pow_pos x n * Z.pow_pos y n.
  Proof.
    rewrite !Z.pow_pos_fold. rewrite Z.pow_mul_l. reflexivity.
  Qed.

  Lemma Z2Nat_le0 (n : Z) : n <= 0 -> Z.to_nat n = 0%N.
  Proof. by case: n. Qed.

  Lemma Z2Nat_inj_pow_pos (n : Z) (m : positive) :
    0 <= n ->
    Z.to_nat (Z.pow_pos n m) = (Z.to_nat n ^ Pos.to_nat m)%N.
  Proof.
    case: n => /=.
    - move=> _. rewrite (exp0n (pos_to_nat_is_pos m)). rewrite Z.pow_pos_fold.
      rewrite (Z.pow_0_l _ (Pos2Z.pos_is_pos m)). reflexivity.
    - move=> n _. rewrite -Pos2Z.inj_pow_pos. rewrite Z2Nat.inj_pos.
      exact: Pos2N_inj_pow.
    - move=> n H. move: (Pos2Z.neg_is_neg n) => Hn. move: (Z.le_lt_trans _ _ _ H Hn).
      done.
  Qed.

  Lemma Z2Nat_inj_pow (n m : Z) :
    0 <= n -> 0 <= m ->
    Z.to_nat (n ^ m) = (Z.to_nat n ^ Z.to_nat m)%N.
  Proof.
    case: m => //=. move=> m Hn Hm. apply: Z2Nat_inj_pow_pos.
    assumption.
  Qed.

  Import ssrnat div.

  Lemma Nat2Z_inj_modn (n m : nat) :
    (m != 0)%N ->
    Z.of_nat (div.modn n m) = (Z.of_nat n) mod (Z.of_nat m).
  Proof.
    move=> Hm0. case H: (n < m)%N.
    - rewrite (modn_small H) Zmod_small; first reflexivity.
      split; first exact: Nat2Z.is_nonneg. apply: (proj1 (Nat2Z.inj_lt _ _)).
      apply: ltn_lt. exact: H.
    - move/negP/idP: H; rewrite -leqNgt => H.
      move: m H Hm0. induction n using nat_strong_ind.
      move=> m Hmn Hm0. have HmnZ: Z.of_nat m <= Z.of_nat n.
      { apply: (proj1 (Nat2Z.inj_le _ _)). apply: leq_le. exact: Hmn. }
      rewrite (modn_subn Hmn) (Zmod_sub HmnZ).
      case Hsub: ((n - m) < m)%N.
      + have HsubZ: Z.of_nat n - Z.of_nat m < Z.of_nat m.
        { rewrite -(Nat2Z.inj_sub _ _ (leq_le Hmn)).
          apply: (proj1 (Nat2Z.inj_lt _ _)). apply: ltn_lt. exact: Hsub. }
        have Hge0: 0 <= Z.of_nat n - Z.of_nat m.
        { apply: (proj2 (Z.le_0_sub _ _)). apply: (proj1 (Nat2Z.inj_le _ _)).
          apply: leq_le. exact: Hmn. }
        rewrite (modn_small Hsub) (Zmod_small _ _ (conj Hge0 HsubZ)).
        rewrite subn_sub (Nat2Z.inj_sub _ _ (leq_le Hmn)). reflexivity.
      + move/negP/idP: Hsub; rewrite -leqNgt => Hsub.
        rewrite -(Nat2Z.inj_sub _ _ (leq_le Hmn)). apply: H.
        * rewrite -lt0n in Hm0. rewrite -{2}(subn0 n). apply: ltn_sub2l.
          -- exact: (ltn_leq_trans Hm0 Hmn).
          -- exact: Hm0.
        * exact: Hsub.
        * exact: Hm0.
  Qed.

  Corollary Nat2Z_inj_mod (n m : nat) :
    Z.of_nat (Nat.modulo n m) = (Z.of_nat n) mod (Z.of_nat m).
  Proof.
    case H: (m == 0)%N.
    - rewrite (eqP H) Zmod_0_r /=. reflexivity.
    - move/negP/idP: H => H. rewrite -(Nats.modn_modulo _ H).
      exact: (Nat2Z_inj_modn _ H).
  Qed.

  Lemma Nat2Z_inj_divn (n m : nat) :
    Z.of_nat (div.divn n m) = (Z.of_nat n) / (Z.of_nat m).
  Proof.
    case Hm0: (m == 0)%N.
    - rewrite (eqP Hm0) divn0 Zdiv_0_r. reflexivity.
    - move/negP/idP: Hm0=> Hm0. have Hne: (m <> 0)%N by move/eqP: Hm0; apply.
      case Hnm: (n < m)%N.
      + rewrite (divn_small Hnm) Zdiv_small; first reflexivity.
        split; first exact: Nat2Z.is_nonneg. apply: (proj1 (Nat2Z.inj_lt _ _)).
        apply: ltn_lt. exact: Hnm.
      + move/negP/idP: Hnm; rewrite -leqNgt => Hnm. move: (eq_refl n).
        rewrite {1}(divn_eq n m). have Hmod: (n %% m <= n)%N.
        { apply: ltnW. apply: (ltn_leq_trans _ Hnm). rewrite ltn_mod.
          rewrite lt0n. exact: Hm0. }
        rewrite (addn_subn _ Hmod). move=> H. have HneZ: Z.of_nat m <> 0.
        { move=> Heq; apply: Hne. apply: Nat2Z.inj. exact: Heq. }
        apply: (proj1 (Z.mul_cancel_r (Z.of_nat (n %/ m))
                                      (Z.of_nat n / Z.of_nat m)
                                      (Z.of_nat m) HneZ)).
        rewrite -Nat2Z.inj_mul -muln_mul. rewrite (eqP H).
        rewrite (Nat2Z.inj_sub _ _ (leq_le Hmod)) (Nat2Z_inj_modn _ Hm0).
        symmetry.
        apply: (proj1 (Z.add_move_l (Z.of_nat n mod Z.of_nat m)
                                    (Z.of_nat n / Z.of_nat m * Z.of_nat m)
                                    (Z.of_nat n))).
        rewrite Z.add_comm Z.mul_comm -Z_div_mod_eq; first reflexivity.
        change 0 with (Z.of_nat 0). apply: (proj1 (Nat2Z.inj_gt _ _)).
        apply: gtn_gt. rewrite lt0n. exact: Hm0.
  Qed.

  Corollary Nat2Z_inj_div (n m : nat) :
    Z.of_nat (n / m) = (Z.of_nat n) / (Z.of_nat m).
  Proof.
    rewrite -divn_div. exact: Nat2Z_inj_divn.
  Qed.

  Definition Zsub_l := Z.sub_move_r.

  Lemma Zsub_r n m p : n - m = p -> m = n - p.
  Proof.
    move/Z.sub_move_r. move/Zplus_minus_eq. by apply.
  Qed.

  Local Close Scope Z_scope.

End ZLemmas.



(** An ordered type for positive with a Boolean equality in mathcomp. *)

Module PositiveOrderMinimal <: SsrOrderMinimal.

  Local Open Scope positive_scope.

  Definition t : eqType := pos_eqType.

  Definition eqn : t -> t -> bool := fun x y : t => x == y.

  Definition ltn : t -> t -> bool := fun x y => Pos.ltb x y.

  Global Hint Unfold eqn ltn : core.

  Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
  Proof.
    move=> Hxy Hyz. move/pos_ltP: Hxy; move/pos_ltP: Hyz => Hyz Hxy.
    apply/pos_ltP. exact: (Pos.lt_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
  Proof.
    move=> Hlt. apply/negP => Heq. rewrite (eqP Heq) in Hlt.
    apply: (Pos.lt_irrefl y). apply/pos_ltP. assumption.
  Qed.

  Lemma compare (x y : t) : Compare ltn eqn x y.
  Proof.
    case H: (Pos.compare x y).
    - apply: EQ. move: (Pos.compare_eq_iff x y) => [Hc _].
      apply/eqP. exact: (Hc H).
    - apply: LT. move: (Pos.compare_lt_iff x y) => [Hc _].
      apply/pos_ltP. exact: (Hc H).
    - apply: GT. move: (Pos.compare_gt_iff x y) => [Hc _].
      apply/pos_ltP. exact: (Hc H).
  Defined.

  Local Close Scope positive_scope.

End PositiveOrderMinimal.

Module PositiveOrder <: SsrOrder := MakeSsrOrder PositiveOrderMinimal.



(** An ordered type for N with a Boolean equality in mathcomp. *)

Module NOrderMinimal <: SsrOrderMinimal.

  Local Open Scope N_scope.

  Definition t : eqType := N_eqType.

  Definition eqn : t -> t -> bool := fun x y : t => x == y.

  Definition ltn : t -> t -> bool := fun x y => N.ltb x y.

  Global Hint Unfold eqn ltn : core.

  Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
  Proof.
    move=> Hxy Hyz. move/N_ltP: Hxy; move/N_ltP: Hyz => Hyz Hxy.
    apply/N_ltP. exact: (N.lt_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
  Proof.
    move=> Hlt. apply/negP => Heq. rewrite (eqP Heq) in Hlt.
    apply: (N.lt_irrefl y). apply/N_ltP. assumption.
  Qed.

  Lemma compare (x y : t) : Compare ltn eqn x y.
  Proof.
    case H: (N.compare x y).
    - apply: EQ. move: (N.compare_eq_iff x y) => [Hc _].
      apply/eqP. exact: (Hc H).
    - apply: LT. move: (N.compare_lt_iff x y) => [Hc _].
      apply/N_ltP. exact: (Hc H).
    - apply: GT. move: (N.compare_gt_iff x y) => [Hc _].
      apply/N_ltP. exact: (Hc H).
  Defined.

  Local Close Scope N_scope.

End NOrderMinimal.

Module NOrder <: SsrOrder := MakeSsrOrder NOrderMinimal.



(** An ordered type for Z with a Boolean equality in mathcomp. *)

Module ZOrderMinimal <: SsrOrderMinimal.

  Local Open Scope Z_scope.

  Definition t : eqType := Z_eqType.

  Definition eqn : t -> t -> bool := fun x y : t => x == y.

  Definition ltn : t -> t -> bool := fun x y => Z.ltb x y.

  Global Hint Unfold eqn ltn : core.

  Lemma ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z.
  Proof.
    move=> Hxy Hyz. move/Z_ltP: Hxy; move/Z_ltP: Hyz => Hyz Hxy.
    apply/Z_ltP. exact: (Z.lt_trans _ _ _ Hxy Hyz).
  Qed.

  Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
  Proof.
    move=> Hlt. apply/negP => Heq. rewrite (eqP Heq) in Hlt.
    apply: (Z.lt_irrefl y). apply/Z_ltP. assumption.
  Qed.

  Lemma compare (x y : t) : Compare ltn eqn x y.
  Proof.
    case H: (Z.compare x y).
    - apply: EQ. move: (Z.compare_eq_iff x y) => [Hc _].
      apply/eqP. exact: (Hc H).
    - apply: LT. move: (Z.compare_lt_iff x y) => [Hc _].
      apply/Z_ltP. exact: (Hc H).
    - apply: GT. move: (Z.compare_gt_iff x y) => [Hc _].
      apply/Z_ltP. exact: (Hc H).
  Defined.

  Local Close Scope Z_scope.

End ZOrderMinimal.

Module ZOrder <: SsrOrder := MakeSsrOrder ZOrderMinimal.



(** Equality Modulo *)

Require Import Lia.

Section EqualityModulo.

  Local Open Scope Z_scope.

  Definition modulo (a b p : Z) := exists k : Z, a - b = k * p.

  Definition eqmb (x y p : Z) : bool :=
    x mod p == y mod p.

  Lemma eqmP : forall x y p, reflect (eqm p x y) (eqmb x y p).
  Proof.
    rewrite /eqm /eqmb => x y p.
    case Hxy: (x mod p == y mod p)%Z.
    - apply: ReflectT.
      apply/eqP.
      assumption.
    - apply: ReflectF.
      apply/eqP/negP.
      by rewrite Hxy.
  Qed.

  Lemma Zminus_mod_mod :
    forall x p : Z,
      p <> 0 ->
      (x - (x mod p)) mod p = 0.
  Proof.
    move=> x p Hp.
    rewrite Zminus_mod_idemp_r.
    rewrite Z.sub_diag.
    exact: Zmod_0_l.
  Qed.

  Lemma Zminus_mod_div_mul :
    forall x p : Z,
      p <> 0 ->
      (x - (x mod p)) / p * p = x - (x mod p).
  Proof.
    move=> x p Hp.
    rewrite (Z_div_exact_full_2 _ _ Hp (Zminus_mod_mod _ Hp)).
    move: (Zdiv_mult_cancel_l ((x - x mod p) / p) 1 p Hp) => Heq.
    rewrite Z.mul_1_r Z.div_1_r in Heq.
    rewrite Heq.
    rewrite Z.mul_comm.
    reflexivity.
  Qed.

  Lemma eqm_modulo :
    forall x y p : Z,
      p <> 0 -> eqm p x y -> modulo x y p.
  Proof.
    move=> x y p Hp Hm.
    exists ((x - (x mod p)) / p - (y - (y mod p)) / p).
    rewrite Z.mul_sub_distr_r 2!(Zminus_mod_div_mul _ Hp) Hm Zminus_plus_simpl_r.
    reflexivity.
  Qed.

  Lemma modulo_eqm :
    forall x y p : Z,
      p <> 0 -> modulo x y p -> eqm p x y.
  Proof.
    move=> x y p Hp [k Heq].
    move: (Zplus_eq_compat _ _ _ _ Heq (Logic.eq_refl y)) => {Heq}.
    rewrite (Z.add_comm (k * p) y) Zminus_plus => Heq.
    rewrite Heq /eqm Z_mod_plus_full.
    reflexivity.
  Qed.

  Lemma eqmb_modulo :
    forall x y p : Z,
      p <> 0 -> eqmb x y p -> modulo x y p.
  Proof.
    move=> x y p Hp Hm.
    move/eqmP: Hm.
    exact: eqm_modulo.
  Qed.

  Lemma modulo_eqmb :
    forall x y p : Z,
      p <> 0 -> modulo x y p -> eqmb x y p.
  Proof.
    move=> x y p Hp Hm.
    apply/eqmP.
    exact: modulo_eqm.
  Qed.

  Lemma modulo_inj : forall x y p z,
      (z <> 0)%Z ->
      modulo (z * x) (z * y) (z * p) ->
      modulo x y p.
  Proof.
    move=> x y p z Hz [k H].
    exists k.
    rewrite -Z.mul_sub_distr_l Z.mul_assoc (Z.mul_comm k z) -Z.mul_assoc in H.
    exact (Z.mul_reg_l _ _ z Hz H).
  Qed.

  Lemma modulo_plus x y a b p :
    modulo x a p -> modulo y b p ->
    modulo (x + y) (a + b) p.
  Proof.
    move=> [k1 H1] [k2 H2].
    exists (k1 + k2). lia.
  Qed.

End EqualityModulo.

Notation "x === y # p" := (eqmb x y p) (at level 70, no associativity).

(**
 * Prove
 *   forall x1 ... xn : Z,
 *     P1 -> ... -> Pn -> modulo f g p
 * with modulo_inj and another proved lemma H
 *   forall x1 ... xn y z : Z,
 *     P1 -> ... -> Pn -> y = z^2 + 1 -> modulo (y * f) (y * g) (y * p).
 *)
Ltac modulo_inj_pow2add1 H :=
  intros;
  apply (modulo_inj (z:=2%Z)); [
    discriminate |
    apply H with 1%Z; first [assumption | reflexivity]
  ].

From mathcomp Require Import seq.
From ssrlib Require Import Seqs.

(** Apply addition and multiplication to a list of integers. *)
Section ZaddsZmuls.

  Local Open Scope Z_scope.

  Local Notation seq := seq.seq.

  Definition zadds (zs : seq Z) : Z := foldl Z.add 0 zs.
  Definition zmuls (zs : seq Z) : Z := foldl Z.mul 1 zs.
  Definition zopps (zs : seq Z) : seq Z := map Z.opp zs.
  Fixpoint zadds2 (xs ys : seq Z) : seq Z :=
    match xs, ys with
    | [::], _ => ys
    | _, [::] => xs
    | x::xs, y::ys => (x + y)::(zadds2 xs ys)
    end.
  Fixpoint zsubs2 (xs ys : seq Z) : seq Z :=
    match xs, ys with
    | [::], _ => zopps ys
    | _, [::] => xs
    | x::xs, y::ys => (x - y)::(zsubs2 xs ys)
    end.
  Definition zmuls2 (xs ys : seq Z) : seq Z := map2 Z.mul xs ys.
  Definition zaddns (n : Z) (zs : seq Z) : seq Z := zadds2 (nseq (size zs) n) zs.
  Definition zsubns (n : Z) (zs : seq Z) : seq Z := zsubs2 (nseq (size zs) n) zs.
  Definition zmulns (n : Z) (zs : seq Z) : seq Z := zmuls2 (nseq (size zs) n) zs.


  Definition is_zero (n : Z) : bool := n == 0.

  Lemma nseqn0_all0 n : all is_zero (nseq n 0)%Z.
  Proof. by elim: n => //=. Qed.


  Lemma zopps_cons m ms : zopps (m::ms) = (-m)::(zopps ms).
  Proof. reflexivity. Qed.

  Lemma zopps_rcons ms m : zopps (rcons ms m) = rcons (zopps ms) (-m).
  Proof. rewrite /zopps map_rcons. reflexivity. Qed.

  Lemma zopps_cat ms ns : zopps (ms ++ ns) = zopps ms ++ zopps ns.
  Proof. rewrite /zopps map_cat. reflexivity. Qed.

  Lemma zopps_involutive ns : zopps (zopps ns) = ns.
  Proof.
    elim: ns => [| n ns IH] //=. rewrite Z.opp_involutive IH. reflexivity.
  Qed.


  Lemma zadds0 : zadds nil = 0.
  Proof. done. Qed.

  Lemma zadds_cons m ms : zadds (m::ms) = m + zadds ms.
  Proof.
    rewrite /zadds foldl_cons.
    - rewrite Z.add_comm. reflexivity.
    - move=> x y z. rewrite -Z.add_assoc (Z.add_comm x y) Z.add_assoc. reflexivity.
    - move=> x y zs => ->. reflexivity.
  Qed.

  Lemma zadds_rcons ms m : zadds (rcons ms m) = zadds ms + m.
  Proof. rewrite /zadds. rewrite foldl_rcons. reflexivity. Qed.

  Lemma zadds_cat ms ns : zadds (ms ++ ns) = zadds ms + zadds ns.
  Proof.
    elim: ms ns => [| m ms IHm] ns //=. rewrite !zadds_cons. rewrite IHm. ring.
  Qed.


  Lemma zmuls0 : zmuls nil = 1.
  Proof. reflexivity. Qed.

  Lemma zmuls_cons m ms : zmuls (m::ms) = m * zmuls ms.
  Proof.
    rewrite /zmuls foldl_cons; intros; subst; by ring.
  Qed.

  Lemma zmuls_rcons ms m : zmuls (rcons ms m) = zmuls ms * m.
  Proof. rewrite /zmuls. rewrite foldl_rcons. reflexivity. Qed.

  Lemma zmuls_cat ms ns : zmuls (ms ++ ns) = zmuls ms * zmuls ns.
  Proof.
    elim: ms ns => [| m ms IHm] ns.
    - rewrite cat0s zmuls0. ring.
    - rewrite cat_cons !zmuls_cons. rewrite IHm. ring.
  Qed.


  Lemma zadds2s0 xs : zadds2 xs nil = xs.
  Proof. by case: xs. Qed.

  Lemma zadds20s xs : zadds2 nil xs = xs.
  Proof. reflexivity. Qed.

  Lemma zadds2_cons x xs y ys : zadds2 (x::xs) (y::ys) = (x + y)::(zadds2 xs ys).
  Proof. reflexivity. Qed.

  Lemma zadds2_rcons xs x ys y :
    size xs = size ys ->
    zadds2 (rcons xs x) (rcons ys y) = rcons (zadds2 xs ys) (x + y).
  Proof.
    elim: xs x ys y => [| a xs IH] x ys y.
    - by case: ys => [| b ys] //=.
    - case: ys => [| b ys] //=. move=> /= /eq_add_S Hs.
      rewrite (IH _ _ _ Hs). reflexivity.
  Qed.

  Lemma zadds2_cat xs1 xs2 ys1 ys2 :
    size xs1 = size ys1 ->
    zadds2 (xs1 ++ xs2) (ys1 ++ ys2) = (zadds2 xs1 ys1) ++ (zadds2 xs2 ys2).
  Proof.
    elim: xs1 xs2 ys1 ys2 => [| x1 xs1 IH] xs2 [| y1 ys1] ys2 //=.
    move/eq_add_S => Hs. rewrite (IH _ _ _ Hs). reflexivity.
  Qed.

  Lemma zadds2_comm xs ys : zadds2 xs ys = zadds2 ys xs.
  Proof.
    elim: xs ys => [| x xs IH] [| y ys] //=. rewrite IH Z.add_comm. reflexivity.
  Qed.

  Lemma zadds2_assoc xs ys zs : zadds2 xs (zadds2 ys zs) = zadds2 (zadds2 xs ys) zs.
  Proof.
    elim: xs ys zs => [| x xs IH] [| y ys] [| z zs] //=.
    rewrite IH Z.add_assoc. reflexivity.
  Qed.


  Lemma zsubs2_zadds2_zopps xs ys : zsubs2 xs ys = zadds2 xs (zopps ys).
  Proof.
    elim: xs ys => [| x xs IH] [| y ys] //=. rewrite Z.add_opp_r IH.
    reflexivity.
  Qed.

  Lemma zsubs2s0 xs : zsubs2 xs nil = xs.
  Proof. by case: xs. Qed.

  Lemma zsubs20s xs : zsubs2 nil xs = zopps xs.
  Proof. reflexivity. Qed.

  Lemma zsubs2_cons x xs y ys : zsubs2 (x::xs) (y::ys) = (x - y)::(zsubs2 xs ys).
  Proof. reflexivity. Qed.

  Lemma zsubs2_rcons xs x ys y :
    size xs = size ys ->
    zsubs2 (rcons xs x) (rcons ys y) = rcons (zsubs2 xs ys) (x - y).
  Proof.
    elim: xs x ys y => [| a xs IH] x ys y.
    - by case: ys => [| b ys] //=.
    - case: ys => [| b ys] //=. move=> /= /eq_add_S Hs.
      rewrite (IH _ _ _ Hs). reflexivity.
  Qed.

  Lemma zsubs2_cat xs1 xs2 ys1 ys2 :
    size xs1 = size ys1 ->
    zsubs2 (xs1 ++ xs2) (ys1 ++ ys2) = (zsubs2 xs1 ys1) ++ (zsubs2 xs2 ys2).
  Proof.
    elim: xs1 xs2 ys1 ys2 => [| x1 xs1 IH] xs2 [| y1 ys1] ys2 //=.
    move/eq_add_S => Hs. rewrite (IH _ _ _ Hs). reflexivity.
  Qed.

  Lemma zopps_zsubs2 xs ys : zopps (zsubs2 ys xs) = zsubs2 xs ys.
  Proof.
    elim: xs ys => [| x xs IH] [| y ys] //=.
    - rewrite Z.opp_involutive zopps_involutive. reflexivity.
    - rewrite Z.opp_sub_distr Z.add_comm Z.add_opp_r IH. reflexivity.
  Qed.

  Lemma zsubs2_zopps_r xs ys : zsubs2 xs (zopps ys) = zadds2 xs ys.
  Proof.
    rewrite zsubs2_zadds2_zopps. rewrite zopps_involutive. reflexivity.
  Qed.

  Lemma zsubs2_zsubs2_distr xs ys zs :
    zsubs2 xs (zsubs2 ys zs) = zadds2 (zsubs2 xs ys) zs.
  Proof.
    elim: xs ys zs => [| x xs IH] [| y ys] [| z zs] //=.
    - rewrite Z.opp_involutive zopps_involutive. reflexivity.
    - rewrite zadds2_comm -zsubs2_zadds2_zopps zopps_zsubs2 Z.opp_sub_distr.
      reflexivity.
    - rewrite Z.sub_opp_r zsubs2_zopps_r. reflexivity.
    - rewrite Z.sub_sub_distr IH. reflexivity.
  Qed.


  Lemma zmuls2s0 xs : zmuls2 xs nil = nil.
  Proof. exact: map2s0. Qed.

  Lemma zmuls20s ys : zmuls2 nil ys = nil.
  Proof. exact: map20s. Qed.

  Lemma zmuls2_cons x xs y ys : zmuls2 (x::xs) (y::ys) = (x * y)::(zmuls2 xs ys).
  Proof. exact: map2_cons. Qed.

  Lemma zmuls2_rcons xs x ys y :
    size xs = size ys ->
    zmuls2 (rcons xs x) (rcons ys y) = rcons (zmuls2 xs ys) (x * y).
  Proof. exact: map2_rcons. Qed.

  Lemma zmuls2_cat xs1 xs2 ys1 ys2 :
    size xs1 = size ys1 ->
    zmuls2 (xs1 ++ xs2) (ys1 ++ ys2) = (zmuls2 xs1 ys1) ++ (zmuls2 xs2 ys2).
  Proof. exact: map2_cat. Qed.

  Lemma zmuls2_comm xs ys : zmuls2 xs ys = zmuls2 ys xs.
  Proof. apply: map2_comm. exact: Z.mul_comm. Qed.

  Lemma zmuls2_assoc xs ys zs : zmuls2 xs (zmuls2 ys zs) = zmuls2 (zmuls2 xs ys) zs.
  Proof. apply: map2_assoc. exact: Z.mul_assoc. Qed.


  Lemma size_zopps ms : size (zopps ms) = size ms.
  Proof. elim: ms => [| m ms IH] //=. rewrite IH. reflexivity. Qed.

  Lemma size_zadds2 ms ns : size (zadds2 ms ns) = maxn (size ms) (size ns).
  Proof.
    elim: ms ns => [| m ms IH] [| n ns] //=. rewrite IH maxnSS. reflexivity.
  Qed.

  Lemma size_zsubs2 ms ns : size (zsubs2 ms ns) = maxn (size ms) (size ns).
  Proof.
    elim: ms ns => [| m ms IH] [| n ns] //=.
    - rewrite size_zopps. rewrite /maxn. move/lt_ltn: (Nat.lt_0_succ (size ns)) => ->.
      reflexivity.
    - rewrite IH maxnSS. reflexivity.
  Qed.

  Lemma size_zmuls2 ms ns : size (zmuls2 ms ns) = minn (size ms) (size ns).
  Proof.
    elim: ms ns => [| m ms IH] [| n ns] //=. rewrite zmuls2_cons /=.
    rewrite IH. rewrite minnSS. reflexivity.
  Qed.

  Lemma size_zaddns x ys : size (zaddns x ys) = size ys.
  Proof. rewrite /zaddns size_zadds2 size_nseq maxnn. reflexivity. Qed.

  Lemma size_zsubns x ys : size (zsubns x ys) = size ys.
  Proof. rewrite /zsubns size_zsubs2 size_nseq maxnn. reflexivity. Qed.

  Lemma size_zmulns x ys : size (zmulns x ys) = size ys.
  Proof. rewrite /zmulns size_zmuls2 size_nseq minnn. reflexivity. Qed.


  Lemma zaddns0 x : zaddns x [::] = [::].
  Proof. reflexivity. Qed.

  Lemma zsubns0 x : zsubns x [::] = [::].
  Proof. reflexivity. Qed.

  Lemma zmulns0 x : zmulns x [::] = [::].
  Proof. reflexivity. Qed.

  Lemma zaddns_cons x y ys : zaddns x (y::ys) = (x + y)::(zaddns x ys).
  Proof. reflexivity. Qed.

  Lemma zsubns_cons x y ys : zsubns x (y::ys) = (x - y)::(zsubns x ys).
  Proof. reflexivity. Qed.

  Lemma zmulns_cons x y ys : zmulns x (y::ys) = (x * y)::(zmulns x ys).
  Proof. rewrite /zmulns /=. rewrite zmuls2_cons. reflexivity. Qed.

  Lemma zaddns_cat x ys zs : zaddns x (ys ++ zs) = zaddns x ys ++ zaddns x zs.
  Proof.
    rewrite /zaddns. rewrite size_cat nseq_addn. apply: zadds2_cat.
    rewrite size_nseq. reflexivity.
  Qed.

  Lemma zsubns_cat x ys zs : zsubns x (ys ++ zs) = zsubns x ys ++ zsubns x zs.
  Proof.
    rewrite /zsubns. rewrite size_cat nseq_addn. apply: zsubs2_cat.
    rewrite size_nseq. reflexivity.
  Qed.

  Lemma zmulns_cat x ys zs : zmulns x (ys ++ zs) = zmulns x ys ++ zmulns x zs.
  Proof.
    rewrite /zmulns. rewrite size_cat nseq_addn. apply: zmuls2_cat.
    rewrite size_nseq. reflexivity.
  Qed.

  Lemma zadds2_nseq n x y : zadds2 (nseq n x) (nseq n y) = nseq n (x + y).
  Proof. elim: n => [| n IH] //=. rewrite IH. reflexivity. Qed.

  Lemma zsubs2_nseq n x y : zsubs2 (nseq n x) (nseq n y) = nseq n (x - y).
  Proof. elim: n => [| n IH] //=. rewrite IH. reflexivity. Qed.

  Lemma zmuls2_nseq n x y : zmuls2 (nseq n x) (nseq n y) = nseq n (x * y).
  Proof. elim: n => [| n IH] //=. rewrite zmuls2_cons IH. reflexivity. Qed.

  Lemma zopps_nseq n x : zopps (nseq n x) = nseq n (-x).
  Proof. elim: n => [| n IH] //=. rewrite -IH; reflexivity. Qed.

  Lemma zaddns_comm x y zs : zaddns x (zaddns y zs) = zaddns y (zaddns x zs).
  Proof.
    rewrite /zaddns. rewrite !size_zadds2 !size_nseq !maxnn.
    rewrite zadds2_assoc (zadds2_comm (nseq (size zs) x)) -zadds2_assoc. reflexivity.
  Qed.

  Lemma zsubns_zsubns_distr x y zs : zsubns x (zsubns y zs) = zaddns (x - y) zs.
  Proof.
    rewrite /zsubns. rewrite !size_zsubs2 !size_nseq !maxnn.
    rewrite zsubs2_zsubs2_distr. rewrite zsubs2_nseq. reflexivity.
  Qed.

  Lemma zmulns_comm x y zs : zmulns x (zmulns y zs) = zmulns y (zmulns x zs).
  Proof.
    rewrite /zmulns. rewrite !size_zmuls2 !size_nseq !minnn.
    rewrite zmuls2_assoc (zmuls2_comm (nseq (size zs) x)) -zmuls2_assoc. reflexivity.
  Qed.


  Lemma zadds_zopps ms : zadds (zopps ms) = - zadds ms.
  Proof.
    elim: ms => [| m ms IH] //=. rewrite !zadds_cons. rewrite Z.opp_add_distr.
    rewrite -IH. reflexivity.
  Qed.

  Lemma zopps_zadds2 xs ys : zopps (zadds2 xs ys) = zadds2 (zopps xs) (zopps ys).
  Proof.
    elim: xs ys => [| x xs IHx] [| y ys] //=. rewrite IHx.
    rewrite Z.opp_add_distr. reflexivity.
  Qed.

  Lemma zopps_zmuls2_l xs ys : zopps (zmuls2 xs ys) = zmuls2 (zopps xs) ys.
  Proof.
    elim: xs ys => [| x xs IHx] [| y ys] //=. rewrite !zmuls2_cons zopps_cons IHx.
    rewrite Z.mul_opp_l. reflexivity.
  Qed.

  Lemma zopps_zmuls2_r xs ys : zopps (zmuls2 xs ys) = zmuls2 xs (zopps ys).
  Proof.
    elim: xs ys => [| x xs IHx] [| y ys] //=. rewrite !zmuls2_cons zopps_cons IHx.
    rewrite Z.mul_opp_r. reflexivity.
  Qed.

  Lemma zopps_zaddns x ys : zopps (zaddns x ys) = zaddns (- x) (zopps ys).
  Proof. rewrite /zaddns size_zopps zopps_zadds2 zopps_nseq. reflexivity. Qed.

  Lemma zopps_zsubns x ys : zopps (zsubns x ys) = zaddns (- x) ys.
  Proof.
    rewrite /zsubns zopps_zsubs2 zsubs2_zadds2_zopps zopps_nseq zadds2_comm.
    reflexivity.
  Qed.

  Lemma zopps_zmulns x ys : zopps (zmulns x ys) = zmulns x (zopps ys).
  Proof. rewrite /zmulns size_zopps zopps_zmuls2_r. reflexivity. Qed.


  Lemma zadds_zmuls2_comm xs ys : zadds (zmuls2 xs ys) = zadds (zmuls2 ys xs).
  Proof.
    elim: xs ys => [| x xs IHx] [| y ys] //=.
    rewrite !zmuls2_cons !zadds_cons IHx. rewrite Z.mul_comm. reflexivity.
  Qed.

  Lemma zadds_zmuls2_all0_r xs ys : all is_zero ys -> zadds (zmuls2 xs ys) = 0.
  Proof.
    elim: xs ys => [| x xs IHx] [| y ys] //=.
    move/andP => [Hy Hys]. rewrite zmuls2_cons zadds_cons. rewrite (IHx _ Hys) Z.add_0_r.
    rewrite (eqP Hy) Z.mul_0_r. reflexivity.
  Qed.

  Lemma zadds_zmuls2_all0_l xs ys : all is_zero xs -> zadds (zmuls2 xs ys) = 0.
  Proof.
    rewrite zadds_zmuls2_comm. exact: zadds_zmuls2_all0_r.
  Qed.

  Lemma zadds_zmuls2_cons x xs y ys :
    zadds (zmuls2 (x::xs) (y::ys)) = (x * y) + zadds (zmuls2 xs ys).
  Proof. rewrite zmuls2_cons zadds_cons. reflexivity. Qed.

  Lemma zadds_zmuls2_zadds xs1 xs2 ys :
    zadds (zmuls2 (zadds2 xs1 xs2) ys) =
      zadds (zmuls2 xs1 ys) + zadds (zmuls2 xs2 ys).
  Proof.
    elim: xs1 xs2 ys => [| x1 xs1 IH] [| x2 xs2] //=.
    - move=> ys. rewrite zmuls20s. reflexivity.
    - move=> ys. rewrite zmuls20s. rewrite zadds0. ring.
    - move=> ys. rewrite zmuls20s. rewrite zadds0. ring.
    - case=> [| y ys] //=. rewrite !zmuls2_cons !zadds_cons. rewrite IH. ring.
  Qed.

  Lemma zadds_zmuls2_zsubs xs1 xs2 ys :
    zadds (zmuls2 (zsubs2 xs1 xs2) ys) =
      zadds (zmuls2 xs1 ys) - zadds (zmuls2 xs2 ys).
  Proof.
    elim: xs1 xs2 ys => [| x1 xs1 IH] [| x2 xs2] //=.
    - move=> ys. rewrite zmuls20s. reflexivity.
    - move=> ys. rewrite zmuls20s. rewrite zadds0. case: ys => [| y ys] //=.
      rewrite !zmuls2_cons !zadds_cons. rewrite -zopps_zmuls2_l.
      rewrite zadds_zopps. ring.
    - move=> ys. rewrite zmuls20s. rewrite zadds0. ring.
    - case=> [| y ys] //=. rewrite !zmuls2_cons !zadds_cons. rewrite IH. ring.
  Qed.

  Lemma zadds_zmuls2_mul xs1 xs2 ys :
    exists cs,
      (zadds (zmuls2 xs1 ys)) * (zadds (zmuls2 xs2 ys)) = zadds (zmuls2 cs ys).
  Proof.
    elim: xs1 xs2 ys => [| x1 xs1 IH] xs2 ys.
    - exists [::]. rewrite !zmuls20s !zadds0. reflexivity.
    - case: ys => [| y ys] /=.
      + exists [::]. rewrite zmuls20s zadds0. reflexivity.
      + rewrite zmuls2_cons. case: xs2 => [| x2 xs2].
        * exists [::]. rewrite !zmuls20s zadds0. rewrite Z.mul_0_r. reflexivity.
        * rewrite zmuls2_cons !zadds_cons. move: (IH xs2 ys) => [cs H].
          exists ((x1 * zadds (zmuls2 xs2 ys) + x2 * zadds (zmuls2 xs1 ys) + x1 * x2 * y)::cs).
          rewrite zmuls2_cons zadds_cons. lia.
  Qed.

  Lemma zmuls2_nseq_size_gt n x ys :
    (size ys < n)%N -> zmuls2 (nseq n x) ys = zmuls2 (nseq (size ys) x) ys.
  Proof.
    rewrite /zmuls2 => Hs. rewrite map2_size_gt_l.
    - rewrite take_nseq. rewrite /minn Hs. reflexivity.
    - rewrite size_nseq. assumption.
  Qed.

  Lemma zmuls2_zmulns_r xs y zs : zmuls2 xs ((zmulns y) zs) = zmulns y (zmuls2 xs zs).
  Proof.
    rewrite /zmulns. rewrite size_zmuls2.
    rewrite (zmuls2_assoc xs). rewrite (zmuls2_comm _ (nseq (size zs) y)).
    rewrite -zmuls2_assoc. symmetry. rewrite -size_zmuls2.
    case Hs: (size zs == size (zmuls2 xs zs)).
    - move/eqP: Hs => <-. reflexivity.
    - symmetry. apply: zmuls2_nseq_size_gt. rewrite size_zmuls2 in Hs *.
      rewrite /minn. case Hsxz: (size xs < size zs)%N.
      + assumption.
      + apply: False_ind. move/negP: Hs; apply. rewrite /minn Hsxz. exact: eqxx.
  Qed.

  Lemma zmuls2_zmulns_l x ys zs : zmuls2 (zmulns x ys) zs = zmulns x (zmuls2 ys zs).
  Proof.
    rewrite zmuls2_comm. rewrite zmuls2_zmulns_r. rewrite zmuls2_comm. reflexivity.
  Qed.

  Lemma zmuls2_zadds2_distr_l xs ys zs :
    zmuls2 xs (zadds2 ys zs) = zadds2 (zmuls2 xs ys) (zmuls2 xs zs).
  Proof.
    elim: xs ys zs => [| x xs IH] [| y ys] [| z zs] //=.
    - rewrite zmuls2s0 zadds2s0. reflexivity.
    - rewrite !zmuls2_cons zadds2_cons. rewrite -IH.
      rewrite Z.mul_add_distr_l. reflexivity.
  Qed.

  Lemma zmuls2_zadds2_distr_r xs ys zs :
    zmuls2 (zadds2 ys zs) xs = zadds2 (zmuls2 ys xs) (zmuls2 zs xs).
  Proof.
    elim: xs ys zs => [| x xs IH] [| y ys] [| z zs] //=.
    - rewrite zmuls20s zadds2s0. reflexivity.
    - rewrite !zmuls2_cons zadds2_cons. rewrite -IH.
      rewrite Z.mul_add_distr_r. reflexivity.
  Qed.

  Lemma zmuls2_zsubs2_distr_l xs ys zs :
    zmuls2 xs (zsubs2 ys zs) = zsubs2 (zmuls2 xs ys) (zmuls2 xs zs).
  Proof.
    elim: xs ys zs => [| x xs IH] [| y ys] [| z zs] //=.
    - rewrite !zmuls2_cons zopps_cons zopps_zmuls2_r Z.mul_opp_r. reflexivity.
    - rewrite zmuls2s0 zsubs2s0. reflexivity.
    - rewrite !zmuls2_cons zsubs2_cons. rewrite -IH.
      rewrite Z.mul_sub_distr_l. reflexivity.
  Qed.

  Lemma zmuls2_zsubs2_distr_r xs ys zs :
    zmuls2 (zsubs2 ys zs) xs = zsubs2 (zmuls2 ys xs) (zmuls2 zs xs).
  Proof.
    elim: xs ys zs => [| x xs IH] [| y ys] [| z zs] //=.
    - rewrite !zmuls2_cons zopps_cons zopps_zmuls2_l Z.mul_opp_l. reflexivity.
    - rewrite zmuls20s zsubs2s0. reflexivity.
    - rewrite !zmuls2_cons zsubs2_cons. rewrite -IH.
      rewrite Z.mul_sub_distr_r. reflexivity.
  Qed.

  Lemma zadds_zmulns x ys : zadds (zmulns x ys) = x * zadds ys.
  Proof.
    elim: ys => [| y ys IH] //=.
    - rewrite zadds0. rewrite Z.mul_0_r. reflexivity.
    - rewrite zmulns_cons !zadds_cons IH. ring.
  Qed.

  Lemma zmulns_zadds2 x ys zs :
    zmulns x (zadds2 ys zs) = zadds2 (zmulns x ys) (zmulns x zs).
  Proof.
    elim: ys x zs => [| y ys IH] x [| z zs] //=.
    - rewrite zmulns0 zadds2s0. reflexivity.
    - rewrite !zmulns_cons zadds2_cons. rewrite Z.mul_add_distr_l -IH. reflexivity.
  Qed.

  Lemma zmulns_zsubs2 x ys zs :
    zmulns x (zsubs2 ys zs) = zsubs2 (zmulns x ys) (zmulns x zs).
  Proof.
    rewrite zsubs2_zadds2_zopps zmulns_zadds2 zsubs2_zadds2_zopps zopps_zmulns.
    reflexivity.
  Qed.

  Lemma zaddns_assoc x y zs : zaddns x (zaddns y zs) = zaddns (x + y) zs.
  Proof.
    rewrite /zaddns zadds2_assoc. rewrite size_zadds2 size_nseq maxnn.
    rewrite zadds2_nseq. reflexivity.
  Qed.

  Lemma zmulns_assoc x y zs : zmulns x (zmulns y zs) = zmulns (x * y) zs.
  Proof.
    elim: zs x y => [| z zs IH] x y //=. rewrite !zmulns_cons IH.
    rewrite Z.mul_assoc. reflexivity.
  Qed.

End ZaddsZmuls.


(**
 * Congruence modulo single modulus or multi-moduli.
 * In the single modulus case, x ≡ y (mod m) is definsed as `exists k, x - y == k * m`
 * such that we can find the witness of k with xchoose when its proof is given.
 *)
Section ZEQM.

  Local Open Scope Z_scope.

  (* congruence modulo single modulus *)

  Definition zeqm (x y m : Z) := exists k : Z, x - y == k * m.

  Definition xchoose_zeqm (x y m : Z) (ex : zeqm x y m) : Z :=
    xchoose ex.

  Lemma xchoose_zeqm_sound x y m (ex : zeqm x y m) :
    x - y = (xchoose_zeqm ex) * m.
  Proof. exact: (eqP (xchooseP ex)). Qed.


  (* congruence modulo multi-moduli *)

  Definition zeqms (x y : Z) (ms : seq Z) :=
    exists ks, x - y == zadds (zmuls2 ks ms).

  Lemma zeqms_refl x ms : zeqms x x ms.
  Proof.
    exists [::]. rewrite Z.sub_diag. rewrite zmuls20s zadds0. exact: eqxx.
  Qed.

  Lemma zeqms_comm x y ms : zeqms x y ms -> zeqms y x ms.
  Proof.
    move=> [ks H]. exists (map Z.opp ks). rewrite -(Z.opp_involutive (y - x)).
    rewrite Z.opp_sub_distr. rewrite Z.add_comm Z.add_opp_r.
    rewrite (eqP H). rewrite -zadds_zopps zopps_zmuls2_l. exact: eqxx.
  Qed.

  Lemma zeqms_trans x y z ms : zeqms x y ms -> zeqms y z ms -> zeqms x z ms.
  Proof.
    move=> [cxy /eqP /Zsub_l Hxy] [cyz /eqP /Zsub_r Hyx].
    exists (zadds2 cxy cyz). rewrite Hxy Hyx.
    rewrite zadds_zmuls2_zadds. apply/eqP. lia.
  Qed.

  Lemma zeqms_nil x y : zeqms x y [::] -> x = y.
  Proof.
    move=> [ks H]. rewrite zmuls2s0 zadds0 in H. apply: Zminus_eq.
    apply/eqP. assumption.
  Qed.

  Lemma zeqms_add a b c d ms :
    zeqms a b ms -> zeqms c d ms -> zeqms (a + c) (b + d) ms.
  Proof.
    move=> [ca /eqP Hab] [cc /eqP Hcd]. exists (zadds2 ca cc). apply/eqP.
    replace (a + c - (b + d))%Z with ((a - b) + (c - d))%Z by ring.
    rewrite Hab Hcd. rewrite -zadds_zmuls2_zadds. reflexivity.
  Qed.

  Lemma zeqms_sub a b c d ms :
    zeqms a b ms -> zeqms c d ms -> zeqms (a - c) (b - d) ms.
  Proof.
    move=> [ca /eqP Hab] [cc /eqP Hcd]. exists (zsubs2 ca cc). apply/eqP.
    replace (a - c - (b - d))%Z with ((a - b) - (c - d))%Z by ring.
    rewrite Hab Hcd. rewrite -zadds_zmuls2_zsubs. reflexivity.
  Qed.

  Lemma zeqms_mul a b c d ms :
    zeqms a b ms -> zeqms c d ms -> zeqms (a * c) (b * d) ms.
  Proof.
    move=> [ca /eqP Hab] [cc /eqP Hcd].
    move: (zadds_zmuls2_mul ca cc ms) => [cs Hcs].
    exists (zadds2 (zadds2 (zmulns b cc) (zmulns d ca)) cs).
    apply/eqP. move/Zsub_l: Hab => ->. move/Zsub_l: Hcd => ->.
    replace ((zadds (zmuls2 ca ms) + b) * (zadds (zmuls2 cc ms) + d) - b * d) with
      (b * zadds (zmuls2 cc ms) + d * zadds (zmuls2 ca ms) + zadds (zmuls2 ca ms) * zadds (zmuls2 cc ms)) by ring.
    rewrite !zadds_zmuls2_zadds. rewrite !zmuls2_zmulns_l. rewrite !zadds_zmulns.
    rewrite Hcs. reflexivity.
  Qed.

  Lemma zeqms0_add a b ms :
    zeqms a 0 ms -> zeqms b 0 ms -> zeqms (a + b) 0 ms.
  Proof.
    move=> Ha Hb. replace 0 with (0 + 0) by reflexivity.
    exact: (zeqms_add Ha Hb).
  Qed.

  Lemma zeqms0_sub a b ms :
    zeqms a 0 ms -> zeqms b 0 ms -> zeqms (a - b) 0 ms.
  Proof.
    move=> Ha Hb. replace 0 with (0 - 0) by reflexivity.
    exact: (zeqms_sub Ha Hb).
  Qed.

  Lemma zeqms_mul_0_l a b ms :
    zeqms a 0 ms -> zeqms (a * b) 0 ms.
  Proof.
    move=> [ca /eqP Ha]. rewrite Z.sub_0_r in Ha. exists (zmulns b ca).
    rewrite Z.sub_0_r . rewrite zmuls2_zmulns_l zadds_zmulns. rewrite -Ha. apply/eqP. lia.
  Qed.

  Lemma zeqms_mul_0_r a b ms :
    zeqms b 0 ms -> zeqms (a * b) 0 ms.
  Proof.
    rewrite Z.mul_comm. exact: zeqms_mul_0_l.
  Qed.

  Lemma zeqms0_mul a b ms :
    zeqms a 0 ms -> zeqms b 0 ms -> zeqms (a * b) 0 ms.
  Proof.
    move=> Ha Hb. replace 0 with (0 * 0) by reflexivity.
    exact: (zeqms_mul Ha Hb).
  Qed.

  Lemma zeqms1_mul a b ms :
    zeqms a 1 ms -> zeqms b 1 ms -> zeqms (a * b) 1 ms.
  Proof.
    move=> Ha Hb. replace 1 with (1 * 1) by reflexivity.
    exact: (zeqms_mul Ha Hb).
  Qed.

  Lemma zeqms_zopp x y ms : zeqms (- x) y ms <-> zeqms x (- y) ms.
  Proof.
    split; move=> [c /eqP Hc].
    - exists (zopps c). rewrite -zopps_zmuls2_l. rewrite zadds_zopps.
      apply/eqP. lia.
    - exists (zopps c). rewrite -zopps_zmuls2_l. rewrite zadds_zopps.
      apply/eqP. lia.
  Qed.

  Lemma zeqms_in_modulus m ns : m \in ns -> zeqms m 0 ns.
  Proof.
    elim: ns => [| n ns IH] //=. rewrite in_cons. case/orP=> Hin.
    - move/eqP: Hin => ?; subst. exists (1::nseq (size ns) 0).
      rewrite zmuls2_cons zadds_cons -/(zmulns 0 ns) zadds_zmulns. apply/eqP; lia.
    - move: (IH Hin) => [cs Hcs]. exists (0::cs). rewrite zmuls2_cons zadds_cons.
      rewrite Z.mul_0_l Z.add_0_l. assumption.
  Qed.

  Lemma zeqms_eq_some_modulus m ns : has (Z.eqb m) ns -> zeqms m 0 ns.
  Proof.
    move=> H. apply: zeqms_in_modulus. elim: ns H => [| n ns IH] H.
    - rewrite has_nil in H. discriminate.
    - rewrite /= in H. case/orP: H => H.
      + move/Z_eqP: H => ?; subst. exact: mem_head.
      + rewrite in_cons (IH H) orbT. reflexivity.
  Qed.

  Lemma zeqms_has_one m ns : has (Z.eqb 1) ns -> zeqms m 0 ns.
  Proof.
    elim: ns => [| n ns IH] //. case/orP => H.
    - move/Z_eqP: H => ?; subst. exists (m::(nseq (size ns) 0))%Z.
      apply/eqP. rewrite zmuls2_cons zadds_cons.
      rewrite (zadds_zmuls2_all0_l _ (nseqn0_all0 _)). lia.
    - rewrite -/(has (Z.eqb 1) ns) in H. move: (IH H) => {IH H} [cs Hcs].
      exists (0::cs)%Z. rewrite zmuls2_cons zadds_cons /=. assumption.
  Qed.

  Lemma zeqms_zopp_zopp x y ms :
    zeqms (- x) (- y) ms <-> zeqms x y ms.
  Proof.
    split.
    - move=> [cs /eqP H]. exists (zopps cs). rewrite -zopps_zmuls2_l zadds_zopps.
      apply/eqP. lia.
    - move=> [cs /eqP H]. exists (zopps cs). rewrite -zopps_zmuls2_l zadds_zopps.
      apply/eqP. lia.
  Qed.

  Lemma zeqms_pow x y n ms :
    0 <= n -> zeqms x y ms -> zeqms (x^n) (y^n) ms.
  Proof.
    move: n. apply: natlike_ind.
    - move=> _. exact: zeqms_refl.
    - move=> n Hn IH Heqm. rewrite !(Z.pow_succ_r _ _ Hn). apply: (zeqms_mul Heqm).
      exact: (IH Heqm).
  Qed.


  Definition xchoose_zeqms (x y : Z) (ms : seq Z) (ex : zeqms x y ms) : seq Z :=
    xchoose ex.

  Lemma xchoose_zeqms_sound x y ms (ex : zeqms x y ms) :
    x - y = zadds (zmuls2 (xchoose_zeqms ex) ms).
  Proof. exact: (eqP (xchooseP ex)). Qed.

  Definition xchoose_zeqms_ext (x y : Z) (ms : seq Z) (ex : zeqms x y ms) : seq Z :=
    extseq 0 (xchoose_zeqms ex) ms.

  Lemma zadds_zmuls2_extseq xs ys :
    zadds (zmuls2 (extseq 0 xs ys) ys) = zadds (zmuls2 xs ys).
  Proof.
    elim: xs ys => [| x xs IHx].
    - elim=> [| y ys IHy] //=. rewrite zadds_zmuls2_cons. rewrite IHy.
      rewrite !zmuls20s zadds0. ring.
    - case=> [| y ys] //=. rewrite !zadds_zmuls2_cons IHx. reflexivity.
  Qed.

  Lemma size_xchoose_zeqms_ext x y ms (ex : zeqms x y ms) :
    size (xchoose_zeqms_ext ex) = size ms.
  Proof. rewrite /xchoose_zeqms_ext. rewrite size_extseq. reflexivity. Qed.

  Lemma xchoose_zeqms_eqsize_ext x y ms (ex : zeqms x y ms) :
    x - y = zadds (zmuls2 (xchoose_zeqms_ext ex) ms).
  Proof.
    rewrite /xchoose_zeqms_ext. rewrite zadds_zmuls2_extseq.
    exact: xchoose_zeqms_sound.
  Qed.

  Lemma xchoose_zeqms_ext_sound x y ms (ex : zeqms x y ms) :
    x - y = zadds (zmuls2 (xchoose_zeqms_ext ex) ms).
  Proof.
    rewrite /xchoose_zeqms_ext zadds_zmuls2_extseq.
    exact: (eqP (xchooseP ex)).
  Qed.

End ZEQM.
