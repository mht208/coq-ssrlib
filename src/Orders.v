
From Coq Require Import OrderedType Bool Arith ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype order choice.
From ssrlib Require Import Types Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(** * Coq OrderedType as a structure orderedType *)

(** ** orderedType: OrderedType with decidable equality *)

Declare Scope ordered_scope.
Delimit Scope ordered_scope with OT.

Module OrderedType.

  Local Open Scope ordered_scope.

  Structure mixin_of (t : Type) :=
    Mixin { eq : t -> t -> Prop
          ; lt : t -> t -> Prop
          ; le : t -> t -> Prop
          ; eq_refl : forall x, eq x x
          ; eq_sym : forall x y, eq x y -> eq y x
          ; eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z
          ; lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z
          ; lt_not_eq : forall x y : t, lt x y -> ~ eq x y
          ; le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y
          ; compare : forall x y : t, Compare lt eq x y }.
  Notation class_of := mixin_of (only parsing).

  Section ClassDef.

    Structure type : Type := Pack { sort; _ : class_of sort }.

    Local Coercion sort : type >-> Sortclass.

    Variables (T : Type) (cT : type).

    Definition class := let: Pack _ c := cT return class_of cT in c.
    Definition clone := fun c & cT -> T & phant_id (@Pack T c) cT => Pack c.

  End ClassDef.

  Module Exports.
    Coercion sort : type >-> Sortclass.
    Notation orderedType := type.
    Notation OrderedTypeMixin := Mixin.
    Notation OrderedType t m := (@Pack t m).
    Notation "[ 'orderedTypeMixin' 'of' T ]" :=
      (class _ : mixin_of T)
        (at level 0, format "[ 'orderedTypeMixin'  'of'  T ]") : ordered_scope.
    Notation "[ 'orderedType' 'of' T 'for' C ]" :=
      (@clone T C _ idfun id)
        (at level 0, format "[ 'orderedType'  'of'  T  'for'  C ]") : ordered_scope.
    Notation "[ 'orderedType' 'of' T ]" :=
      (@clone T _ _ id id)
        (at level 0, format "[ 'orderedType'  'of'  T ]") : ordered_scope.

    Section Definitions.
      Context {t : orderedType}.
      Definition eq := eq (class t).
      Definition lt := lt (class t).
      Definition le := le (class t).
      Lemma eq_refl : forall x, eq x x.
      Proof. exact: eq_refl. Qed.
      Lemma eq_sym : forall x y, eq x y -> eq y x.
      Proof. exact: eq_sym. Qed.
      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof. exact: eq_trans. Qed.
      Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      Proof. exact: lt_trans. Qed.
      Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      Proof. exact: lt_not_eq. Qed.
      Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
      Proof. exact: le_lteq. Qed.
      Definition compare : forall x y : t, Compare lt eq x y.
      Proof. exact: compare. Defined.
    End Definitions.

    Module OrderedTypeNotations.
      Infix "==" := eq (at level 70, no associativity) : ordered_scope.
      Notation "x == y :> T" := ((x : T) == (y : T)) (at level 70, y at next level) : ordered_scope.
      Notation "x ~= y" := (~ (x == y)) (at level 70, no associativity) : ordered_scope.
      Notation "x ~= y :> T" := (~ (x == y :> T)) (at level 70, y at next level, no associativity) : ordered_scope.
      Infix "<" := lt : ordered_scope.
      Notation "x < y :> T" := ((x : T) < (y : T)) (at level 70, y at next level) : ordered_scope.
      Notation "x > y" := (y < x) (only parsing) : ordered_scope.
      Notation "x > y :> T" := (y < x :> T) (at level 70, y at next level, only parsing) : ordered_scope.
      Notation "x < y < z" := (x < y /\ y < z) : ordered_scope.
      Infix "<=" := le : ordered_scope.
      Notation "x <= y :> T" := ((x : T) <= (y : T)) (at level 70, y at next level) : ordered_scope.
      Notation "x >= y" := (y <= x) (only parsing) : ordered_scope.
      Notation "x >= y :> T" := (y <= x :> T) (at level 70, y at next level, only parsing) : ordered_scope.
      Notation "x <= y <= z" := (x <= y /\ y <= z) : ordered_scope.
      Notation "x <= y < z" := (x <= y /\ y < z) : ordered_scope.
      Notation "x < y <= z" := (x < y /\ y <= z) : ordered_scope.
      Infix "?=" := compare (at level 70, no associativity) : ordered_scope.
      Notation "x ?= y :> T" := (@compare (class T) x y) (at level 70, y at next level, no associativity) : ordered_scope.
    End OrderedTypeNotations.

    Global Hint Unfold Symmetric : ordered_type.
    Global Hint Immediate eq_sym : ordered_type.
    Global Hint Resolve eq_refl eq_trans lt_not_eq lt_trans le_lteq : ordered_type.

  End Exports.

End OrderedType.

Export OrderedType.Exports.
Export OrderedTypeNotations.

Notation oeq := OrderedType.Exports.eq (only parsing).
Notation olt := OrderedType.Exports.lt (only parsing).
Notation ole := OrderedType.Exports.le (only parsing).
Notation ogt := (flip OrderedType.Exports.lt) (only parsing).
Notation oge := (flip OrderedType.Exports.le) (only parsing).
Notation ocompare := (OrderedType.Exports.compare) (only parsing).


(** ** Lemmas about orderedType from OrdersTac, OrderedType, and OrdersFacts *)

Module OrderedTypeLemmas.

  Local Open Scope ordered_scope.

  (* Define the tactic [order] from OrdersTac. *)

  Section OrderFacts.

    Context {t : orderedType}.

    Lemma le_refl (x : t) : le x x.
    Proof. rewrite le_lteq. right. exact: eq_refl. Qed.

    Lemma lt_irrefl (x : t) : ~ lt x x.
    Proof. move=> H. move: (lt_not_eq H). apply; exact: eq_refl. Qed.

    Lemma le_antisym (x y : t) : x <= y -> y <= x -> x == y.
    Proof.
      rewrite !le_lteq. move=> [] H1 [] H2 //.
      - apply: False_ind. exact: (lt_irrefl (lt_trans H1 H2)).
      - apply: eq_sym. assumption.
    Qed.

    Global Instance eq_equiv : Equivalence (eq (t:=t)).
    Proof. split; [ exact eq_refl | exact eq_sym | exact eq_trans ]. Qed.

    Global Instance lt_strorder : StrictOrder (lt (t:=t)).
    Proof. split; [ exact lt_irrefl | exact lt_trans]. Qed.

    Lemma neq_sym (x y : t) : ~ x == y -> ~ y == x.
    Proof. by auto using eq_sym. Qed.

    Lemma lt_total (x y : t) : lt x y \/ eq x y \/ lt y x.
    Proof. by destruct (compare x y); auto. Qed.

    Lemma lt_eq (x y z : t) : lt x y -> eq y z -> lt x z.
    Proof.
      move=> H1 H2. destruct (compare x z) as [ Hlt | Heq | Hlt ]; auto.
      - elim: (lt_not_eq H1). exact: (eq_trans Heq (eq_sym H2)).
      - elim: (lt_not_eq (lt_trans Hlt H1)). exact: (eq_sym H2).
    Qed.

    Lemma eq_lt (x y z : t) : eq x y -> lt y z -> lt x z.
    Proof.
      move=> H1 H2. destruct (compare x z) as [ Hlt | Heq | Hlt ]; auto.
      - elim: (lt_not_eq H2). exact: (eq_trans (eq_sym H1) Heq).
      - elim: (lt_not_eq (lt_trans H2 Hlt)). exact: (eq_sym H1).
    Qed.

    Global Instance lt_compat : Proper (eq ==> (eq (t:=t)) ==> iff) lt.
    Proof.
      apply proper_sym_impl_iff_2; auto with *.
      move => x x' Hx y y' Hy H.
      apply eq_lt with x; first exact: (eq_sym Hx).
      by apply lt_eq with y; auto.
    Qed.

    Global Instance le_compat : Proper (eq ==> (eq (t:=t)) ==> iff) le.
    Proof.
      apply proper_sym_impl_iff_2; auto with *.
      move => x x' Hx y y' Hy H. rewrite !le_lteq in H *. case: H => H.
      - left. rewrite -Hx -Hy. assumption.
      - right. rewrite -Hx -Hy. assumption.
    Qed.

    Ltac subst_eqns :=
      match goal with
      | H : _ == _ |- _ => (rewrite H || rewrite <- H); clear H; subst_eqns
      | _ => idtac
      end.

    Definition interp_ord o :=
      match o with OEQ => eq (t:=t) | OLT => lt (t:=t) | OLE => le (t:=t) end.
    Local Infix "+" := trans_ord.
    Local Notation "#" := interp_ord.

    Lemma trans o o' x y z : #o x y -> #o' y z -> #(o + o') x z.
    Proof.
      by destruct o, o'; simpl;
      rewrite ?le_lteq; intuition auto;
      subst_eqns; eauto using (StrictOrder_Transitive x y z) with *.
    Qed.

    Definition eq_trans (x y z : t) : x == y -> y == z -> x == z := @trans OEQ OEQ x y z.
    Definition le_trans (x y z : t) : x <= y -> y <= z -> x <= z := @trans OLE OLE x y z.
    Definition lt_trans (x y z : t) : x < y -> y < z -> x < z := @trans OLT OLT x y z.
    Definition le_lt_trans (x y z : t) : x <= y -> y < z -> x < z := @trans OLE OLT x y z.
    Definition lt_le_trans (x y z : t) : x < y -> y <= z -> x < z := @trans OLT OLE x y z.
    Definition eq_le (x y z : t) : x == y -> y <= z -> x <= z := @trans OEQ OLE x y z.
    Definition le_eq (x y z : t) : x <= y -> y == z -> x <= z := @trans OLE OEQ x y z.

    Lemma eq_neq (x y z : t) : x == y -> ~ y == z -> ~ x == z.
    Proof. by eauto using eq_trans, eq_sym. Qed.

    Lemma neq_eq (x y z : t) : ~ x == y -> y == z -> ~ x == z.
    Proof. by eauto using eq_trans, eq_sym. Qed.

    Lemma not_neq_eq (x y : t) : ~ ~ x == y -> x == y.
    Proof.
      intros H. by destruct (lt_total x y) as [H'|[H'|H']]; auto;
                destruct H; intro H; rewrite H in H'; eapply lt_irrefl; eauto.
    Qed.

    Lemma not_ge_lt (x y : t) : ~ y <= x -> x < y.
    Proof.
      intros H. destruct (lt_total x y); auto.
      destruct H. rewrite le_lteq. intuition.
    Qed.

    Lemma not_gt_le (x y : t) : ~ y < x -> x <= y.
    Proof.
      intros H. rewrite le_lteq. by generalize (lt_total x y); intuition.
    Qed.

    Lemma le_neq_lt (x y : t) : x <= y -> ~ x == y -> x < y.
    Proof. by auto using not_ge_lt, le_antisym. Qed.

  End OrderFacts.

  Ltac order_rewr x eqn :=
    (* NB: we could use the real rewrite here, but proofs would be uglier. *)
    let rewr H t := generalize t; clear H; intro H
    in
    match goal with
    | H : x == _ |- _ => rewr H (eq_trans (eq_sym eqn) H); order_rewr x eqn
    | H : _ == x |- _ => rewr H (eq_trans H eqn); order_rewr x eqn
    | H : ~x == _ |- _ => rewr H (eq_neq (eq_sym eqn) H); order_rewr x eqn
    | H : ~_ == x |- _ => rewr H (neq_eq H eqn); order_rewr x eqn
    | H : x < _ |- _ => rewr H (eq_lt (eq_sym eqn) H); order_rewr x eqn
    | H : _ < x |- _ => rewr H (lt_eq H eqn); order_rewr x eqn
    | H : x <= _ |- _ => rewr H (eq_le (eq_sym eqn) H); order_rewr x eqn
    | H : _ <= x |- _ => rewr H (le_eq H eqn); order_rewr x eqn
    | _ => clear eqn
    end.

  Ltac order_eq x y eqn :=
    match x with
    | y => clear eqn
    | _ => change (interp_ord OEQ x y) in eqn; order_rewr x eqn
    end.

  Ltac order_prepare :=
    match goal with
    | H : ?A -> False |- _ => change (~A) in H; order_prepare
    | H : ~(?R ?x ?y) |- _ =>
        match R with
        | eq => fail 1 (* if already using [eq], we leave it this ways *)
        | _ => (change (~x==y) in H ||
                apply not_gt_le in H ||
                apply not_ge_lt in H ||
                clear H || fail 1); order_prepare
        end
    | H : ?R ?x ?y |- _ =>
        match R with
        | eq => fail 1
        | lt => fail 1
        | le => fail 1
        | _ => (change (x==y) in H ||
                change (x<y) in H ||
                change (x<=y) in H ||
                clear H || fail 1); order_prepare
        end
    | |- ~ _ => intro; order_prepare
    | |- _ ?x ?x =>
        exact (eq_refl x) || exact (le_refl x) || exfalso
    | _ =>
        (apply not_neq_eq; intro) ||
        (apply not_ge_lt; intro) ||
        (apply not_gt_le; intro) || exfalso
    end.

  Ltac order_loop :=
    match goal with
    (* First, successful situations *)
    | H : ?x < ?x |- _ => exact (lt_irrefl H)
    | H : ~ ?x == ?x |- _ => exact (H (eq_refl x))
    (* Second, useless hyps *)
    | H : ?x <= ?x |- _ => clear H; order_loop
    (* Third, we eliminate equalities *)
    | H : ?x == ?y |- _ => order_eq x y H; order_loop
    (* Simultaneous le and ge is eq *)
    | H1 : ?x <= ?y, H2 : ?y <= ?x |- _ =>
        generalize (le_antisym H1 H2); clear H1 H2; intro; order_loop
    (* Simultaneous le and ~eq is lt *)
    | H1: ?x <= ?y, H2: ~ ?x == ?y |- _ =>
        generalize (le_neq_lt H1 H2); clear H1 H2; intro; order_loop
    | H1: ?x <= ?y, H2: ~ ?y == ?x |- _ =>
        generalize (le_neq_lt H1 (neq_sym H2)); clear H1 H2; intro; order_loop
    (* Transitivity of lt and le *)
    | H1 : ?x < ?y, H2 : ?y < ?z |- _ =>
        match goal with
        | H : x < z |- _ => fail 1
        | _ => generalize (lt_trans H1 H2); intro; order_loop
        end
    | H1 : ?x <= ?y, H2 : ?y < ?z |- _ =>
        match goal with
        | H : x < z |- _ => fail 1
        | _ => generalize (le_lt_trans H1 H2); intro; order_loop
        end
    | H1 : ?x < ?y, H2 : ?y <= ?z |- _ =>
        match goal with
        | H : x < z |- _ => fail 1
        | _ => generalize (lt_le_trans H1 H2); intro; order_loop
        end
    | H1 : ?x <= ?y, H2 : ?y <= ?z |- _ =>
        match goal with
        | H : x <= z |- _ => fail 1
        | _ => generalize (le_trans H1 H2); intro; order_loop
        end
    | _ => idtac
    end.

  Ltac order :=
    intros; order_prepare; order_loop; fail "Order tactic unsuccessful".


  (* Lemmas from OrderedType *)

  Section OrderedType.

    Context {t : orderedType}.

    Definition eq_dec (x y : t) : {eq x y} + {~ eq x y}.
    Proof.
      case: (compare x y) => Hc.
      - right. exact: (lt_not_eq Hc).
      - by left.
      - right. move: (lt_not_eq Hc) => H1 H2. apply: H1. apply: eq_sym. assumption.
    Defined.

    Lemma le_neq (x y : t) : ~ lt x y -> ~ eq x y -> lt y x. Proof. order. Qed.
    Lemma lt_le (x y : t) : lt x y -> ~ lt y x. Proof. order. Qed.
    Lemma gt_not_eq (x y : t) : lt y x -> ~ eq x y. Proof. order. Qed.
    Lemma eq_not_lt (x y : t) : eq x y -> ~ lt x y. Proof. order. Qed.
    Lemma eq_not_gt (x y : t) : eq x y -> ~ lt y x. Proof. order. Qed.
    Lemma lt_not_gt (x y : t) : lt x y -> ~ lt y x. Proof. order. Qed.

  End OrderedType.

  Global Hint Resolve gt_not_eq eq_not_lt : ordered_type.
  Global Hint Immediate eq_lt lt_eq le_eq eq_le neq_eq eq_neq : ordered_type.
  Global Hint Resolve eq_not_gt lt_irrefl lt_not_gt : ordered_type.

  Section OrderedType.

    Context {t : orderedType}.

    Lemma elim_compare_eq :
      forall x y : t,
        eq x y -> exists H : eq x y, compare x y = EQ H.
    Proof.
      intros x y H; case (compare x y); intros H'; try (exfalso; order).
      by exists H'; auto.
    Qed.

    Lemma elim_compare_lt :
      forall x y : t,
        lt x y -> exists H : lt x y, compare x y = LT H.
    Proof.
      intros x y H; case (compare x y); intros H'; try (exfalso; order).
      by exists H'; auto.
    Qed.

    Lemma elim_compare_gt :
      forall x y : t,
        lt y x -> exists H : lt y x, compare x y = GT H.
    Proof.
      intros x y H; case (compare x y); intros H'; try (exfalso; order).
      by exists H'; auto.
    Qed.

  End OrderedType.

  Ltac elim_comp :=
    match goal with
    | |- ?e => match e with
               | context ctx [ compare ?a ?b ] =>
                   let H := fresh in
                   (destruct (compare a b) as [H|H|H]; try order)
               end
    end.

  Ltac elim_comp_eq x y :=
    elim (elim_compare_eq (x:=x) (y:=y));
     [ intros _1 _2; rewrite _2; clear _1 _2 | auto ].

  Ltac elim_comp_lt x y :=
    elim (elim_compare_lt (x:=x) (y:=y));
     [ intros _1 _2; rewrite _2; clear _1 _2 | auto ].

  Ltac elim_comp_gt x y :=
    elim (elim_compare_gt (x:=x) (y:=y));
    [ intros _1 _2; rewrite _2; clear _1 _2 | auto ].

  Section OrderedType.

    Context {t : orderedType}.

    Lemma lt_dec : forall x y : t, {lt x y} + {~ lt x y}.
    Proof.
      by intros x y; elim (compare x y); [ left | right | right ]; auto with ordered_type.
    Defined.

    Definition eqb (x y : t) : bool := if eq_dec x y then true else false.

    Lemma eqb_alt :
      forall x y, eqb x y = match compare x y with EQ _ => true | _ => false end.
    Proof.
      by unfold eqb; intros x y; destruct (eq_dec x y); elim_comp; auto.
    Qed.

    Lemma eqb_eq (x y : t) : eqb x y <-> eq x y.
    Proof. rewrite /eqb. by case: (eq_dec x y) => H //=. Qed.

  End OrderedType.

  Infix "=?" := eqb (at level 70, no associativity) : ordered_scope.
  Notation "x ~=? y" := (~~ eqb x y) (at level 70, no associativity) : ordered_scope.


  Section ForNotations.

    Context {t : orderedType}.

    Notation In := (InA (eq (t:=t))).
    Notation Inf := (lelistA (lt (t:=t))).
    Notation Sort := (sort (lt (t:=t))).
    Notation NoDup := (NoDupA (eq (t:=t))).

    Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
    Proof. exact (InA_eqA eq_equiv). Qed.

    Lemma ListIn_In : forall l x, List.In x l -> In x l.
    Proof. exact (In_InA eq_equiv). Qed.

    Lemma Inf_lt : forall l x y, lt x y -> Inf y l -> Inf x l.
    Proof. exact (InfA_ltA lt_strorder). Qed.

    Lemma Inf_eq : forall l x y, eq x y -> Inf y l -> Inf x l.
    Proof. exact (InfA_eqA eq_equiv lt_compat). Qed.

    Lemma Sort_Inf_In : forall l x a, Sort l -> Inf a l -> In x l -> lt a x.
    Proof. exact (SortA_InfA_InA eq_equiv lt_strorder lt_compat). Qed.

    Lemma ListIn_Inf : forall l x, (forall y, List.In y l -> lt x y) -> Inf x l.
    Proof. exact (@In_InfA t lt). Qed.

    Lemma In_Inf : forall l x, (forall y, In y l -> lt x y) -> Inf x l.
    Proof. exact (InA_InfA eq_equiv (ltA:=lt)). Qed.

    Lemma Inf_alt :
      forall l x, Sort l -> (Inf x l <-> (forall y, In y l -> lt x y)).
    Proof. exact (InfA_alt eq_equiv lt_strorder lt_compat). Qed.

    Lemma Sort_NoDup : forall l, Sort l -> NoDup l.
    Proof. exact (SortA_NoDupA eq_equiv lt_strorder lt_compat). Qed.

  End ForNotations.

  Global Hint Resolve ListIn_In Sort_NoDup Inf_lt : ordered_type.

  Global Hint Immediate In_eq Inf_lt : ordered_type.


  Module KeyOrderedType.

    Section Elt.

      Context {t : orderedType}.
      Variable elt : Type.

      Notation key := t.

      Definition eqk (p p' : key * elt) := eq (fst p) (fst p').

      Definition eqke (p p':key * elt) :=
        eq (fst p) (fst p') /\ (snd p) = (snd p').

      Definition ltk (p p' : key * elt) := lt (fst p) (fst p').

      #[local]
       Hint Unfold eqk eqke ltk : ordered_type.

      #[local]
       Hint Extern 2 (eqke ?a ?b) => split : ordered_type.

      Lemma eqke_eqk : forall x x', eqke x x' -> eqk x x'.
      Proof.
        unfold eqk, eqke; intuition.
      Qed.

      Lemma ltk_right_r : forall x k e e', ltk x (k,e) -> ltk x (k,e').
      Proof. auto. Qed.

      Lemma ltk_right_l : forall x k e e', ltk (k,e) x -> ltk (k,e') x.
      Proof. auto. Qed.

      #[local]
       Hint Immediate ltk_right_r ltk_right_l : ordered_type.

      Lemma eqk_refl : forall e, eqk e e.
      Proof. auto with ordered_type. Qed.

      Lemma eqke_refl : forall e, eqke e e.
      Proof. auto with ordered_type. Qed.

      Lemma eqk_sym : forall e e', eqk e e' -> eqk e' e.
      Proof. auto with ordered_type. Qed.

      Lemma eqke_sym : forall e e', eqke e e' -> eqke e' e.
      Proof. unfold eqke; intuition. Qed.

      Lemma eqk_trans : forall e e' e'', eqk e e' -> eqk e' e'' -> eqk e e''.
      Proof. eauto with ordered_type. Qed.

      Lemma eqke_trans : forall e e' e'', eqke e e' -> eqke e' e'' -> eqke e e''.
      Proof.
        unfold eqke; intuition; [ eauto with ordered_type | congruence ].
      Qed.

      Lemma ltk_trans : forall e e' e'', ltk e e' -> ltk e' e'' -> ltk e e''.
      Proof. eauto with ordered_type. Qed.

      Lemma ltk_not_eqk : forall e e', ltk e e' -> ~ eqk e e'.
      Proof. unfold eqk, ltk; auto with ordered_type. Qed.

      Lemma ltk_not_eqke : forall e e', ltk e e' -> ~eqke e e'.
      Proof.
        unfold eqke, ltk; intuition; simpl in *; subst.
        match goal with H : lt _ _, H1 : eq _ _ |- _ => exact (lt_not_eq H H1) end.
      Qed.

      #[local]
       Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl : ordered_type.
      #[local]
       Hint Resolve ltk_trans ltk_not_eqk ltk_not_eqke : ordered_type.
      #[local]
       Hint Immediate eqk_sym eqke_sym : ordered_type.

      Global Instance eqk_equiv : Equivalence eqk.
      Proof. constructor; eauto with ordered_type. Qed.

      Global Instance eqke_equiv : Equivalence eqke.
      Proof. split; eauto with ordered_type. Qed.

      Global Instance ltk_strorder : StrictOrder ltk.
      Proof. constructor; eauto with ordered_type. intros x; apply (irreflexivity (x:=fst x)). Qed.

      Global Instance ltk_compat : Proper (eqk==>eqk==>iff) ltk.
      Proof.
        intros (x,e) (x',e') Hxx' (y,f) (y',f') Hyy'; compute.
        compute in Hxx'; compute in Hyy'.
        rewrite -> Hxx', Hyy'; auto.
      Qed.

      Global Instance ltk_compat' : Proper (eqke==>eqke==>iff) ltk.
      Proof.
        intros (x,e) (x',e') (Hxx',_) (y,f) (y',f') (Hyy',_); compute.
        compute in Hxx'; compute in Hyy'. rewrite -> Hxx', Hyy'; auto.
      Qed.

      (* Additional facts *)

      Lemma eqk_not_ltk : forall x x', eqk x x' -> ~ltk x x'.
      Proof.
        unfold eqk, ltk; simpl; auto with ordered_type.
      Qed.

      Lemma ltk_eqk : forall e e' e'', ltk e e' -> eqk e' e'' -> ltk e e''.
      Proof. eauto with ordered_type. Qed.

      Lemma eqk_ltk : forall e e' e'', eqk e e' -> ltk e' e'' -> ltk e e''.
      Proof.
        intros (k,e) (k',e') (k'',e'').
        unfold ltk, eqk; simpl; eauto with ordered_type.
      Qed.

      #[local]
       Hint Resolve eqk_not_ltk : ordered_type.
      #[local]
       Hint Immediate ltk_eqk eqk_ltk : ordered_type.

      Lemma InA_eqke_eqk :
        forall x m, InA eqke x m -> InA eqk x m.
      Proof.
        unfold eqke; induction 1; intuition.
      Qed.

      #[local]
       Hint Resolve InA_eqke_eqk : ordered_type.

      Definition MapsTo (k : key) (e : elt) := InA eqke (k, e).

      Definition In k m := exists e : elt, MapsTo k e m.

      Notation Sort := (sort ltk).

      Notation Inf := (lelistA ltk).

      #[local]
       Hint Unfold MapsTo In : ordered_type.

      (* An alternative formulation for [In k l] is [exists e, InA eqk (k,e) l] *)

      Lemma In_alt : forall k l, In k l <-> exists e, InA eqk (k,e) l.
      Proof with auto with ordered_type.
        intros k l; split; intros [y H].
        exists y...
        induction H as [a l eq|a l H IH].
        destruct a as [k' y'].
        exists y'...
        destruct IH as [e H0].
        exists e...
      Qed.

      Lemma MapsTo_eq : forall l x y e, eq x y -> MapsTo x e l -> MapsTo y e l.
      Proof.
        intros l x y e **; unfold MapsTo in *; apply InA_eqA with (x,e); eauto with *.
      Qed.

      Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
      Proof.
        destruct 2 as (e,E); exists e; eapply MapsTo_eq; eauto.
      Qed.

      Lemma Inf_eq : forall l x x', eqk x x' -> Inf x' l -> Inf x l.
      Proof. exact (InfA_eqA eqk_equiv ltk_compat). Qed.

      Lemma Inf_lt : forall l x x', ltk x x' -> Inf x' l -> Inf x l.
      Proof. exact (InfA_ltA ltk_strorder). Qed.

      #[local]
       Hint Immediate Inf_eq : ordered_type.
      #[local]
       Hint Resolve Inf_lt : ordered_type.

      Lemma Sort_Inf_In :
        forall l p q, Sort l -> Inf q l -> InA eqk p l -> ltk q p.
      Proof.
        exact (SortA_InfA_InA eqk_equiv ltk_strorder ltk_compat).
      Qed.

      Lemma Sort_Inf_NotIn :
        forall l k e, Sort l -> Inf (k,e) l ->  ~In k l.
      Proof.
        intros l k e H H0; red; intros H1.
        destruct H1 as [e' H2].
        elim (@ltk_not_eqk (k,e) (k,e')).
        eapply Sort_Inf_In; eauto with ordered_type.
        red; simpl; auto with ordered_type.
      Qed.

      Lemma Sort_NoDupA: forall l, Sort l -> NoDupA eqk l.
      Proof.
        exact (SortA_NoDupA eqk_equiv ltk_strorder ltk_compat).
      Qed.

      Lemma Sort_In_cons_1 : forall e l e', Sort (e::l) -> InA eqk e' l -> ltk e e'.
      Proof.
        inversion 1; intros; eapply Sort_Inf_In; eauto.
      Qed.

      Lemma Sort_In_cons_2 : forall l e e', Sort (e::l) -> InA eqk e' (e::l) ->
                                            ltk e e' \/ eqk e e'.
      Proof.
        intros l; inversion_clear 2; auto with ordered_type.
        left; apply Sort_In_cons_1 with l; auto.
      Qed.

      Lemma Sort_In_cons_3 :
        forall x l k e, Sort ((k,e)::l) -> In x l -> ~eq x k.
      Proof.
        inversion_clear 1 as [|? ? H0 H1]; red; intros H H2.
        destruct (Sort_Inf_NotIn H0 H1 (In_eq H2 H)).
      Qed.

      Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> eq k k' \/ In k l.
      Proof.
        inversion 1 as [? H0].
        inversion_clear H0 as [? ? H1|]; eauto with ordered_type.
        destruct H1; simpl in *; intuition.
      Qed.

      Lemma In_inv_2 : forall k k' e e' l,
          InA eqk (k, e) ((k', e') :: l) -> ~ eq k k' -> InA eqk (k, e) l.
      Proof.
        inversion_clear 1 as [? ? H0|? ? H0]; compute in H0; intuition.
      Qed.

      Lemma In_inv_3 : forall x x' l,
          InA eqke x (x' :: l) -> ~ eqk x x' -> InA eqke x l.
      Proof.
        inversion_clear 1 as [? ? H0|? ? H0]; compute in H0; intuition.
      Qed.

    End Elt.

    #[global]
     Hint Unfold eqk eqke ltk : ordered_type.
    #[global]
     Hint Extern 2 (eqke ?a ?b) => split : ordered_type.
    #[global]
     Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl : ordered_type.
    #[global]
     Hint Resolve ltk_trans ltk_not_eqk ltk_not_eqke : ordered_type.
    #[global]
     Hint Immediate eqk_sym eqke_sym : ordered_type.
    #[global]
     Hint Resolve eqk_not_ltk : ordered_type.
    #[global]
     Hint Immediate ltk_eqk eqk_ltk : ordered_type.
    #[global]
     Hint Resolve InA_eqke_eqk : ordered_type.
    #[global]
     Hint Unfold MapsTo In : ordered_type.
    #[global]
     Hint Immediate Inf_eq : ordered_type.
    #[global]
     Hint Resolve Inf_lt : ordered_type.
    #[global]
     Hint Resolve Sort_Inf_NotIn : ordered_type.
    #[global]
     Hint Resolve In_inv_2 In_inv_3 : ordered_type.

  End KeyOrderedType.


  (* Lemmas from OrdersFacts *)

  Ltac iorder := intuition order.

  Section CompareFacts.

    Context {t : orderedType}.

    Definition compare' (x y : t) : comparison :=
      match compare x y with
      | LT _ => Lt
      | EQ _ => Eq
      | GT _ => Gt
      end.

    Local Infix "?=" := compare' (at level 70, no associativity).

    Lemma compare_spec : forall (x y : t), CompareSpec (x == y) (x < y) (y < x) (compare' x y).
    Proof.
      move=> x y. rewrite /compare'. case: (compare x y) => H.
      - by apply: CompLt.
      - by apply: CompEq.
      - by apply: CompGt.
    Qed.

    Lemma compare_eq_iff x y : (x ?= y) = Eq <-> x == y.
    Proof.
      by case compare_spec; intro H; split; try easy; intro EQ;
      contradict H; rewrite EQ; apply irreflexivity.
    Qed.

    Lemma compare_eq x y : (x ?= y) = Eq -> x == y.
    Proof. by apply compare_eq_iff. Qed.

    Lemma compare_lt_iff x y : (x ?= y) = Lt <-> x < y.
    Proof.
      by case compare_spec; intro H; split; try easy; intro LT;
      contradict LT; auto with ordered_type.
    Qed.

    Lemma compare_gt_iff x y : (x ?= y) = Gt <-> y < x.
    Proof.
      by case compare_spec; intro H; split; try easy; intro LT;
      contradict LT; auto with ordered_type.
    Qed.

    Lemma compare_nlt_iff x y : (x ?= y) <> Lt <-> ~ (x < y).
    Proof. by rewrite compare_lt_iff; intuition. Qed.

    Lemma compare_ngt_iff x y : (x ?= y) <> Gt <-> ~ (y < x).
    Proof. by rewrite compare_gt_iff; intuition. Qed.

    Hint Rewrite compare_eq_iff compare_lt_iff compare_gt_iff : order.

    Global Instance compare_compat : Proper (eq ==> eq ==> Logic.eq) compare'.
    Proof.
      intros x x' Hxx' y y' Hyy'.
      case (compare_spec x' y'); autorewrite with order; now rewrite -> Hxx', Hyy'.
    Qed.

    Lemma compare_refl x : (x ?= x) = Eq.
    Proof.
      case compare_spec; intros; trivial; now elim irreflexivity with x.
    Qed.

    Lemma compare_antisym x y : (y ?= x) = CompOpp (x ?= y).
    Proof.
      case (compare_spec x y); simpl; autorewrite with order;
        trivial; now symmetry.
    Qed.

  End CompareFacts.


  Section OrderedTypeFullFacts.

    Context {t : orderedType}.

    Global Instance le_preorder : PreOrder (le (t:=t)).
    Proof. by split; red; order. Qed.

    Global Instance le_order : PartialOrder eq (le (t:=t)).
    Proof. by compute; iorder. Qed.

    Lemma le_not_gt_iff : forall (x y : t), x <= y <-> ~ y < x.
    Proof. by iorder. Qed.

     Lemma lt_not_ge_iff : forall (x y : t), x < y <-> ~ y <= x.
     Proof. by iorder. Qed.

     Lemma le_or_gt : forall (x y : t), x <= y \/ y < x.
     Proof. intros x y. rewrite le_lteq; destruct (compare_spec x y); auto. Qed.

     Lemma lt_or_ge : forall (x y : t), x < y \/ y <= x.
     Proof. intros x y. rewrite le_lteq; destruct (compare_spec x y); iorder. Qed.

     Lemma eq_is_le_ge : forall (x y : t), x == y <-> x <= y /\ y <= x.
     Proof. iorder. Qed.

     Lemma compare_le_iff (x y : t) : compare' x y <> Gt <-> x <= y.
     Proof. rewrite le_not_gt_iff. apply compare_ngt_iff. Qed.

     Lemma compare_ge_iff (x y : t) : compare' x y <> Lt <-> y <= x.
     Proof. rewrite le_not_gt_iff. apply compare_nlt_iff. Qed.

  End OrderedTypeFullFacts.


  Section OrderedTypeFacts.

    Context {t : orderedType}.

    Tactic Notation "elim_compare" constr(x) constr(y) :=
      destruct (compare_spec x y).

    Tactic Notation "elim_compare" constr(x) constr(y) "as" ident(h) :=
      destruct (compare_spec x y) as [h|h|h].

    Lemma if_eq_dec (x y : t) (B : Type) (b b' : B) :
      (if eq_dec x y then b else b') =
        (match compare' x y with Eq => b | _ => b' end).
    Proof. destruct eq_dec; elim_compare x y; auto; order. Qed.

    Lemma eqb_alt' :
      forall (x y : t), eqb x y = match compare' x y with Eq => true | _ => false end.
    Proof. unfold eqb; intros; apply if_eq_dec. Qed.

    Global Instance eqb_compat : Proper (eq ==> (eq (t:=t)) ==> Logic.eq) eqb.
    Proof.
      intros x x' Hxx' y y' Hyy'.
      rewrite -> 2 eqb_alt', Hxx', Hyy'; auto.
    Qed.

  End OrderedTypeFacts.

End OrderedTypeLemmas.

Export OrderedTypeLemmas.

Notation oeqb := eqb (only parsing).
Notation oeq_dec := eq_dec (only parsing).
Notation oeq_ST := eq_equiv.


Section CompareBasedOrderFacts.

  Local Open Scope ordered_scope.

  Context {t : orderedType}.

  Infix "?=" := compare'.

  Lemma compare_nle_iff (x y : t) : (x ?= y) = Gt <-> ~ (x <= y).
  Proof.
    rewrite <- compare_le_iff.
    destruct compare'; split; easy || now destruct 1.
  Qed.

  Lemma compare_nge_iff (x y : t) : (x ?= y) = Lt <-> ~ (y <= x).
  Proof. now rewrite <- compare_nle_iff, compare_antisym, CompOpp_iff. Qed.

  Lemma lt_eq_cases (n m : t) : n <= m <-> n < m \/ n == m.
  Proof.
    rewrite <- compare_lt_iff, <- compare_le_iff, <- compare_eq_iff.
    destruct (n ?= m); now intuition.
  Qed.

End CompareBasedOrderFacts.


Section OtherOrderedTypeLemmas.

  Context {t : orderedType}.

  Local Open Scope ordered_scope.

  Lemma oeqP {x y : t} : reflect (eq x y) (eqb x y).
  Proof.
    rewrite /eqb. case: (eq_dec x y) => H /=.
    - by apply: ReflectT.
    - by apply: ReflectF.
  Qed.

  Lemma nlt_eqVlt_iff (x y : t) : (~ (x < y)) <-> ((x == y) \/ (y < x)).
  Proof.
    split; move=> H.
    - case/not_gt_le/lt_eq_cases: H => H.
      + by right.
      + left; by apply: eq_sym.
    - apply/le_not_gt_iff/lt_eq_cases. case: H => H.
      + right; by apply: eq_sym.
      + by left.
  Qed.

  Lemma lt_neqAlt_iff (x y : t) : (x < y) <-> (x ~= y) /\ (~ (y < x)).
  Proof.
    split; move=> H.
    - split. move: (gt_not_eq H).
      + exact: neq_sym.
      + exact: (lt_not_gt H).
    - case: H => [H1 H2]. exact: (le_neq H2 (neq_sym H1)).
  Qed.

  Section Injective.

    Context (A B : orderedType) (f : A -> B).

    Definition oinjective : Prop :=
      forall x y, oeq (f x) (f y) -> oeq x y.

  End Injective.

End OtherOrderedTypeLemmas.


(** ** OrderedType structure as OrderedType Module *)

Module Type HasSucc (Import T : Structures.OrderedType.OrderedType).
  Parameter succ : t -> t.
  Parameter lt_succ : forall (x : t), lt x (succ x).
End HasSucc.


Module Type Ordered <: Structures.OrderedType.OrderedType.
  Parameter T : orderedType.
  Definition t : Type := T.
  Definition eq : t -> t -> Prop := oeq.
  Definition lt : t -> t -> Prop := olt.
  Definition le : t -> t -> Prop := ole.
  Parameter eq_refl : forall x : t, eq x x.
  Parameter eq_sym : forall x y : t, eq x y -> eq y x.
  Parameter eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Parameter le_lteq : forall x y, le x y <-> lt x y \/ eq x y.
End Ordered.

Module Type OrderedWithDefaultSucc <: Ordered :=
  Ordered <+ HasDefault <+ HasSucc.


Module Type HasOrderedType.
  Parameter t : orderedType.
End HasOrderedType.

Module Type HasOrderedTypeWithDefaultSucc <: HasOrderedType.
  Parameter t : orderedType.
  Parameter default : t.
  Parameter succ : t -> t.
  Parameter lt_succ : forall (x : t), lt x (succ x).
End HasOrderedTypeWithDefaultSucc.


Module HOT_as_OT (O : HasOrderedType) <: Ordered.
  Definition T : orderedType := O.t.
  Definition t : Type := O.t.
  Definition eq : t -> t -> Prop := oeq.
  Definition lt : t -> t -> Prop := olt.
  Definition le : t -> t -> Prop := ole.
  Definition eq_refl : forall x : t, eq x x := eq_refl.
  Definition eq_sym : forall x y : t, eq x y -> eq y x := eq_sym.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := eq_trans.
  Definition eq_equiv : Equivalence eq := eq_equiv.
  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z := lt_trans.
  Definition lt_not_eq : forall x y : t, lt x y -> ~ eq x y := lt_not_eq.
  Definition le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y := le_lteq.
  Definition compare : forall x y : t, Compare lt eq x y := ocompare.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := eq_dec.
End HOT_as_OT.

Module HOT_as_OT_WDS (O : HasOrderedTypeWithDefaultSucc) : OrderedWithDefaultSucc.
  Definition T : orderedType := O.t.
  Definition t : Type := O.t.
  Definition eq : t -> t -> Prop := oeq.
  Definition lt : t -> t -> Prop := olt.
  Definition le : t -> t -> Prop := ole.
  Definition eq_refl : forall x : t, eq x x := eq_refl.
  Definition eq_sym : forall x y : t, eq x y -> eq y x := eq_sym.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := eq_trans.
  Definition eq_equiv : Equivalence eq := eq_equiv.
  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z := lt_trans.
  Definition lt_not_eq : forall x y : t, lt x y -> ~ eq x y := lt_not_eq.
  Definition le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y := le_lteq.
  Definition compare : forall x y : t, Compare lt eq x y := ocompare.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := eq_dec.
  Definition default : t := O.default.
  Definition succ : t -> t := O.succ.
  Definition lt_succ : forall (x : t), lt x (succ x) := O.lt_succ.
End HOT_as_OT_WDS.

Module HOT_as_OTF (O : HasOrderedType) <: Structures.Orders.OrderedTypeFull.
  Definition t : Type := O.t.
  Definition eq : t -> t -> Prop := oeq.
  Definition eq_equiv : Equivalence eq := eq_equiv.
  Definition lt : t -> t -> Prop := olt.
  Definition lt_strorder : StrictOrder lt := lt_strorder.
  Definition lt_compat : Proper (eq ==> eq ==> iff) lt := lt_compat.
  Definition compare : t -> t -> comparison := compare'.
  Definition compare_spec : forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y) := compare_spec.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := eq_dec.
  Definition le : t -> t -> Prop := ole.
  Definition le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y := le_lteq.
End HOT_as_OTF.


(** ** decidableOrderedType: OrderedType with decidable less-than and decidable less-than-or-equal-to *)

Module DecidableOrderedType.

  Structure mixin_of (t0 : Type) (o : OrderedType.class_of t0) (t := OrderedType.Pack o) :=
    Mixin { ltb : t -> t -> bool
          ; leb : t -> t -> bool
          ; ltb_lt : forall (x y : t), ltb x y <-> lt x y
          ; leb_le : forall (x y : t), leb x y <-> le x y }.

  Set Primitive Projections.
  Record class_of (T : Type) :=
    Class { base : OrderedType.class_of T
          ; mixin : mixin_of base; }.
  Unset Primitive Projections.

  Section ClassDef.

    Structure type : Type := Pack { sort; _ : class_of sort }.

    Local Coercion sort : type >-> Sortclass.
    Local Coercion base : class_of >-> OrderedType.class_of.

    Variables (T : Type) (cT : type).

    Definition class := let: Pack _ c := cT return class_of cT in c.
    Definition clone c of phant_id class c := @Pack T c.

    Definition pack :=
      fun bT b & phant_id (@OrderedType.class bT) b =>
      fun m => Pack (@Class T b m).

    Definition orderedType := @OrderedType.Pack cT class.

  End ClassDef.

  Module Exports.
    Coercion base : class_of >-> OrderedType.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion orderedType : type >-> OrderedType.type.
    Canonical orderedType.
    Notation decidableOrderedType := type.
    Notation DecidableOrderedTypeMixin := Mixin.
    Notation DecidableOrderedType T m := (@pack T _ _ _ m).

    Section Definitions.
      Context {t : decidableOrderedType}.
      Definition ltb := ltb (class t).
      Definition leb := leb (class t).
      Lemma ltb_lt : forall (x y : t), ltb x y <-> lt x y.
      Proof. exact: ltb_lt. Qed.
      Lemma leb_le : forall (x y : t), leb x y <-> le x y.
      Proof. exact: leb_le. Qed.
    End Definitions.

    Module DecidableOrderedTypeNotations.
      Local Open Scope ordered_scope.
      Infix "<?" := ltb (at level 70, no associativity) : ordered_scope.
      Notation "x >? y" := (y <? x) (only parsing, at level 70, no associativity) : ordered_scope.
      Notation "x <? y <? z" := (x <? y /\ y <? z) (at level 70, y at next level) : ordered_scope.
      Infix "<=?" := leb (at level 70, no associativity) : ordered_scope.
      Notation "x >=? y" := (y <=? x) (only parsing, at level 70, no associativity) : ordered_scope.
      Notation "x <=? y <=? z" := (x <=? y /\ y <=? z) (at level 70, y at next level) : ordered_scope.
      Notation "x <=? y <? z" := (x <=? y /\ y <? z) (at level 70, y at next level) : ordered_scope.
      Notation "x <? y <=? z" := (x <? y /\ y <=? z) (at level 70, y at next level) : ordered_scope.
    End DecidableOrderedTypeNotations.

  End Exports.

End DecidableOrderedType.

Export DecidableOrderedType.Exports.
Export DecidableOrderedTypeNotations.

Notation oltb := DecidableOrderedType.Exports.ltb (only parsing).
Notation oleb := DecidableOrderedType.Exports.leb (only parsing).
Notation ogtb := (flip DecidableOrderedType.Exports.ltb) (only parsing).
Notation ogeb := (flip DecidableOrderedType.Exports.leb) (only parsing).


(** ** Lemmas about decidableOrderedType *)

Section DecidableOrderedTypeLemmas.

  Local Open Scope ordered_scope.

  Context {t : decidableOrderedType}.

  Lemma ltP (x y : t) : reflect (lt x y) (ltb x y).
  Proof.
    case H: (ltb x y).
    - apply: ReflectT. by apply/ltb_lt.
    - apply: ReflectF. apply/ltb_lt. by apply/idP/negPf.
  Qed.

  Lemma leP (x y : t) : reflect (le x y) (leb x y).
  Proof.
    case H: (leb x y).
    - apply: ReflectT. by apply/leb_le.
    - apply: ReflectF. apply/leb_le. by apply/idP/negPf.
  Qed.

  Lemma leb_spec (x y : t) : BoolSpec (x <= y) (y < x) (x <=? y).
  Proof.
    case leP; constructor; trivial.
    now rewrite <- compare_lt_iff, compare_nge_iff.
  Qed.

  Lemma ltb_spec (x y : t) : BoolSpec (x<y) (y<=x) (x<?y).
  Proof.
    case ltP; constructor; trivial.
    now rewrite <- compare_le_iff, compare_ngt_iff.
  Qed.

  Lemma leb_nle (x y : t) : x <=? y = false <-> ~ (x <= y).
  Proof.
    now rewrite <- not_true_iff_false, <- leb_le.
  Qed.

  Lemma leb_gt (x y : t) : x <=? y = false <-> y < x.
  Proof.
    now rewrite -> leb_nle, <- compare_lt_iff, compare_nge_iff.
  Qed.

  Lemma ltb_nlt (x y : t) : x <? y = false <-> ~ (x < y).
  Proof.
    now rewrite <- not_true_iff_false, <- ltb_lt.
  Qed.

  Lemma ltb_ge (x y : t) : x <? y = false <-> y <= x.
  Proof.
    now rewrite -> ltb_nlt, <- compare_le_iff, compare_ngt_iff.
  Qed.

  Lemma leb_refl (x : t) : x <=? x.
  Proof. apply leb_le. apply lt_eq_cases. now right. Qed.

  Lemma leb_antisym (x y : t) : y <=? x = negb (x <? y).
  Proof.
    apply eq_true_iff_eq. fold (is_true (oleb y x)).
    now rewrite -> negb_true_iff, leb_le, ltb_ge.
  Qed.

  Lemma ltb_irrefl (x : t) : x <? x = false.
  Proof. apply ltb_ge. apply lt_eq_cases. now right. Qed.

  Lemma ltb_antisym (x y : t) : y <? x = negb (x <=? y).
  Proof.
    apply eq_true_iff_eq. fold (is_true (oltb y x)).
    now rewrite -> negb_true_iff, ltb_lt, leb_gt.
  Qed.

  Lemma eqb_compare (x y : t) :
    (x =? y) = match compare' x y with Eq => true | _ => false end.
  Proof.
    apply eq_true_iff_eq. fold (is_true (x =? y)).
    rewrite -> eqb_eq, <- compare_eq_iff.
    now destruct compare'.
  Qed.

  Lemma ltb_compare (x y : t) :
    (x <? y) = match compare' x y with Lt => true | _ => false end.
  Proof.
    apply eq_true_iff_eq. fold (is_true (oltb x y)).
    rewrite -> ltb_lt, <- compare_lt_iff.
    now destruct compare'.
  Qed.

  Lemma leb_compare (x y : t) :
    (x <=? y) = match compare' x y with Gt => false | _ => true end.
  Proof.
    apply eq_true_iff_eq. fold (is_true (oleb x y)).
    rewrite -> leb_le, <- compare_le_iff.
    now destruct compare'.
  Qed.

End DecidableOrderedTypeLemmas.


(** ** decidableOrderedType as Coq OrderedType module *)

Module Type HasDecidableLtLe (Import O : Ordered).
  Parameter ltb : t -> t -> bool.
  Parameter leb : t -> t -> bool.
  Axiom ltb_lt : forall (x y : t), ltb x y <-> lt x y.
  Axiom leb_le : forall (x y : t), leb x y <-> le x y.
End HasDecidableLtLe.

Module Type DecidableOrdered := Ordered <+ HasDecidableLtLe.

Module Type DecidableOrderedWithDefaultSucc <: DecidableOrdered :=
  DecidableOrdered <+ HasDefault <+ HasSucc.

Module Type HasDecidableOrderedType.
  Parameter t : decidableOrderedType.
End HasDecidableOrderedType.

Module Type HasDecidableOrderedTypeWithDefaultSucc <: HasDecidableOrderedType.
  Parameter t : decidableOrderedType.
  Parameter default : t.
  Parameter succ : t -> t.
  Parameter lt_succ : forall (x : t), lt x (succ x).
End HasDecidableOrderedTypeWithDefaultSucc.

Module HDOT_as_DOT (O : HasDecidableOrderedType) <: DecidableOrdered.
  Module H <: HasOrderedType.
    Definition t : orderedType := O.t.
  End H.
  Module M := HOT_as_OT H.
  Include M.
  Definition ltb : t -> t -> bool := oltb.
  Definition leb : t -> t -> bool := oleb.
  Definition ltb_lt : forall (x y : t), ltb x y <-> lt x y := ltb_lt.
  Definition leb_le : forall (x y : t), leb x y <-> le x y := leb_le.
End HDOT_as_DOT.

Module HDOT_as_DOT_WDS (O : HasDecidableOrderedTypeWithDefaultSucc) <: DecidableOrderedWithDefaultSucc.
  Module H <: HasOrderedType.
    Definition t : orderedType := O.t.
  End H.
  Module M := HOT_as_OT H.
  Include M.
  Definition ltb : t -> t -> bool := oltb.
  Definition leb : t -> t -> bool := oleb.
  Definition ltb_lt : forall (x y : t), ltb x y <-> lt x y := ltb_lt.
  Definition leb_le : forall (x y : t), leb x y <-> le x y := leb_le.
  Definition default : t := O.default.
  Definition succ : t -> t := O.succ.
  Definition lt_succ : forall (x : t), lt x (succ x) := O.lt_succ.
End HDOT_as_DOT_WDS.

Module HDOT_as_OTF (O : HasDecidableOrderedType) <: Structures.Orders.OrderedTypeFull.
  Definition t : Type := O.t.
  Definition eq : t -> t -> Prop := oeq.
  Definition eq_equiv : Equivalence eq := eq_equiv.
  Definition lt : t -> t -> Prop := olt.
  Definition lt_strorder : StrictOrder lt := lt_strorder.
  Definition lt_compat : Proper (eq ==> eq ==> iff) lt := lt_compat.
  Definition compare : t -> t -> comparison := compare'.
  Definition compare_spec : forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y) := compare_spec.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := eq_dec.
  Definition le : t -> t -> Prop := ole.
  Definition le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y := le_lteq.
End HDOT_as_OTF.


(** ** Product orders *)

Module ProdOrderedType.

  Section ProdOrderedTypeLemmas.

    Context {t1 t2 : orderedType}.

    Notation t := (prod t1 t2).

    Definition eq (x y : t) : Prop :=
      match x, y with
      | (x1, x2), (y1, y2) => oeq x1 y1 /\ oeq x2 y2
      end.

    Definition lt (x y : t) : Prop :=
      match x, y with
      | (x1, x2), (y1, y2) => olt x1 y1 \/ (oeq x1 y1 /\ olt x2 y2)
      end.

    Definition le (x y : t) : Prop :=
      match x, y with
      | (x1, x2), (y1, y2) => olt x1 y1 \/ (oeq x1 y1 /\ ole x2 y2)
      end.

    Lemma eq_refl : forall x : t, eq x x.
    Proof. case => x1 x2 /=. split; by auto with ordered_type. Qed.

    Lemma eq_sym : forall x y : t, eq x y -> eq y x.
    Proof. move=> [] x1 x2 [] y1 y2 /= [H1 H2]. split; by auto with ordered_type. Qed.

    Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    Proof. move=> [] x1 x2 [] y1 y2 [] z1 z2 /= [H1 H2] [H3 H4]. split; by order. Qed.

    Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Proof.
      move=> [] x1 x2 [] y1 y2 [] z1 z2 /=.
      case => [H1 | [H1 H2]]; case => [H3 | [H3 H4]]; by eauto with ordered_type.
    Qed.

    Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    Proof.
      move=> [] x1 x2 [] y1 y2 /=. case => [H1 | [H1 H2]] [H3 H4]; by order.
    Qed.

    Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
    Proof.
      move=> [] x1 x2 [] y1 y2 /=. rewrite le_lteq.
        case_all; by eauto with ordered_type.
    Qed.

    Definition compare : forall x y : t, Compare lt eq x y.
    Proof.
      move=> [] x1 x2 [] y1 y2. case: (ocompare x1 y1) => Hc1.
      - apply: LT; by left.
      - case: (ocompare x2 y2) => Hc2.
        + apply: LT; right; by auto.
        + apply: EQ; by split.
        + apply: GT; right; by eauto with ordered_type.
      - apply: GT; by left.
    Defined.

  End ProdOrderedTypeLemmas.

  Module Exports.

    Definition prodOrderedTypeMixin (t1 t2 : orderedType) :=
      @OrderedTypeMixin (prod t1 t2) eq lt le
                        eq_refl eq_sym eq_trans lt_trans
                        lt_not_eq le_lteq compare.

    Global Canonical prodOrderedType (t1 t2 : orderedType) :=
      Eval hnf in OrderedType (prod t1 t2) (prodOrderedTypeMixin t1 t2).

  End Exports.

End ProdOrderedType.

Export ProdOrderedType.Exports.


Module ProdDecidableOrderedType.

  Section ProdDecidableOrderedTypeLemmas.

    Context {t1 t2 : decidableOrderedType}.

    Notation t := (prod t1 t2).

    Definition ltb (x y : t) : bool :=
      match x, y with
      | (x1, x2), (y1, y2) => oltb x1 y1 || eqb x1 y1 && oltb x2 y2
      end.

    Definition leb (x y : t) : bool :=
      match x, y with
      | (x1, x2), (y1, y2) => oltb x1 y1 || eqb x1 y1 && oleb x2 y2
      end.

    Lemma ltb_lt : forall x y : t, ltb x y <-> lt x y.
    Proof.
      move=> [] x1 x2 [] y1 y2 /=. rewrite /olt /=. case_all.
      - left. rewrite <- ltb_lt. assumption.
      - right. rewrite <- eqb_eq, <- ltb_lt. tauto.
      - left. rewrite -> ltb_lt. assumption.
      - right. apply/andP; split;
          [rewrite -> eqb_eq | rewrite -> ltb_lt]; assumption.
    Qed.

    Lemma leb_le : forall x y : t, leb x y <-> le x y.
    Proof.
      move=> [] x1 x2 [] y1 y2 /=. rewrite /ole /=. case_all.
      - left. rewrite <- DecidableOrderedType.Exports.ltb_lt. assumption.
      - right. rewrite <- eqb_eq, <- DecidableOrderedType.Exports.leb_le. tauto.
      - left. rewrite -> DecidableOrderedType.Exports.ltb_lt. assumption.
      - right. apply/andP; split;
          [rewrite -> eqb_eq | rewrite -> DecidableOrderedType.Exports.leb_le]; assumption.
    Qed.

  End ProdDecidableOrderedTypeLemmas.

  Module Exports.

    Definition prodDecidableOrderedTypeMixin' (t1 t2 : decidableOrderedType) :=
      @DecidableOrderedTypeMixin (prod t1 t2) (prodOrderedTypeMixin t1 t2)
                                 ltb leb ltb_lt leb_le.

    Definition prodDecidableOrderedTypeMixin (t1 t2 : decidableOrderedType) :=
      {| DecidableOrderedType.base := prodOrderedTypeMixin t1 t2
      ; DecidableOrderedType.mixin := prodDecidableOrderedTypeMixin' t1 t2 |}.

    Canonical prodDecidableOrderedType (t1 t2 : decidableOrderedType) :=
      Eval hnf in DecidableOrderedType (prod t1 t2) (prodDecidableOrderedTypeMixin t1 t2).

  End Exports.

End ProdDecidableOrderedType.

Export ProdDecidableOrderedType.Exports.


(** * Sum orders *)

Module SumOrderedType.

  Section SumOrderedTypeLemmas.

    Context {t1 t2 : orderedType}.

    Notation t := (sum t1 t2).

    Definition eq (x y : t) : Prop :=
      match x, y with
      | inl x, inl y => oeq x y
      | inl _, inr _ => False
      | inr _, inl _ => False
      | inr x, inr y => oeq x y
      end.

    Definition lt (x y : t) : Prop :=
      match x, y with
      | inl x, inl y => olt x y
      | inl _, inr _ => True
      | inr _, inl _ => False
      | inr x, inr y => olt x y
      end.

    Definition le (x y : t) : Prop :=
      match x, y with
      | inl x, inl y => ole x y
      | inl _, inr _ => True
      | inr _, inl _ => False
      | inr x, inr y => ole x y
      end.

    Lemma eq_refl : forall x : t, eq x x.
    Proof. case => /=; by auto with ordered_type. Qed.

    Lemma eq_sym : forall x y : t, eq x y -> eq y x.
    Proof. move=> [] x [] y /=; by auto with ordered_type. Qed.

    Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    Proof. move=> [] x [] y [] z //= *; by order. Qed.

    Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Proof. move=> [] x [] y [] z //=; by eauto with ordered_type. Qed.

    Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    Proof. move=> [] x [] y //=; by eauto with ordered_type. Qed.

    Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
    Proof. move=> [] x [] y //=; by [ eauto with ordered_type | tauto ]. Qed.

    Definition compare : forall x y : t, Compare lt eq x y.
    Proof.
      move=> [] x [] y /=.
      - case: (ocompare x y) => Hc.
        + apply: LT; assumption.
        + apply: EQ; assumption.
        + apply: GT; assumption.
      - by apply: LT.
      - by apply: GT.
      - case: (ocompare x y) => Hc.
        + apply: LT; assumption.
        + apply: EQ; assumption.
        + apply: GT; assumption.
    Defined.

  End SumOrderedTypeLemmas.

  Module Exports.

    Definition sumOrderedTypeMixin (t1 t2 : orderedType) :=
      @OrderedTypeMixin (sum t1 t2) eq lt le
                        eq_refl eq_sym eq_trans lt_trans
                        lt_not_eq le_lteq compare.

    Global Canonical sumOrderedType (t1 t2 : orderedType) :=
      Eval hnf in OrderedType (sum t1 t2) (sumOrderedTypeMixin t1 t2).

  End Exports.

End SumOrderedType.

Export SumOrderedType.Exports.


Module SumDecidableOrderedType.

  Section SumDecidableOrderedTypeLemmas.

    Context {t1 t2 : decidableOrderedType}.

    Notation t := (sum t1 t2).

    Definition ltb (x y : t) : bool :=
      match x, y with
      | inl x, inl y => oltb x y
      | inl _, inr _ => true
      | inr _, inl _ => false
      | inr x, inr y => oltb x y
      end.

    Definition leb (x y : t) : bool :=
      match x, y with
      | inl x, inl y => oleb x y
      | inl _, inr _ => true
      | inr _, inl _ => false
      | inr x, inr y => oleb x y
      end.

    Lemma ltb_lt : forall x y : t, ltb x y <-> lt x y.
    Proof. move=> [] x [] y //=; exact: ltb_lt. Qed.

    Lemma leb_le : forall x y : t, leb x y <-> le x y.
    Proof. move=> [] x [] y //=; exact: leb_le. Qed.

  End SumDecidableOrderedTypeLemmas.

  Module Exports.

    Definition sumDecidableOrderedTypeMixin' (t1 t2 : decidableOrderedType) :=
      @DecidableOrderedTypeMixin (sum t1 t2) (sumOrderedTypeMixin t1 t2)
                                 ltb leb ltb_lt leb_le.

    Definition sumDecidableOrderedTypeMixin (t1 t2 : decidableOrderedType) :=
      {| DecidableOrderedType.base := sumOrderedTypeMixin t1 t2
      ; DecidableOrderedType.mixin := sumDecidableOrderedTypeMixin' t1 t2 |}.

    Global Canonical sumDecidableOrderedType (t1 t2 : decidableOrderedType) :=
      Eval hnf in DecidableOrderedType (sum t1 t2) (sumDecidableOrderedTypeMixin t1 t2).

  End Exports.

End SumDecidableOrderedType.

Export SumDecidableOrderedType.Exports.


(** * List of orderedType as predType *)

From ssrlib Require Import Lists.

Section ListPredType.

  Variable t : orderedType.

  Definition oin (s : list t) : pred t := fun x => existsb (oeqb x) s.
  Definition olist := list t.
  Identity Coercion list_of_olist : olist >-> list.
  Coercion pred_of_olist (s : olist) : {pred t} := oin s.
  Global Canonical olist_predType := PredType (pred_of_olist : list t -> pred t).
  Global Canonical oin_predType := PredType oin.

  Import seq.

  Ltac in2oin := rewrite /mem /= /in_mem /= /pred_of_olist /=.

  Lemma oin_cons x a s :
    x \in (a::s) = (oeqb x a) || (x \in s).
  Proof. reflexivity. Qed.

  Lemma oin_app x s1 s2 :
    x \in (s1 ++ s2) = (x \in s1) || (x \in s2).
  Proof. in2oin. rewrite /oin existsb_app. reflexivity. Qed.

  Lemma oin_rcons x s a :
    x \in (rcons s a) = (x \in s) || (oeqb x a).
  Proof. in2oin. by rewrite /oin existsb_rcons. Qed.

  Lemma inA_oin x s : (SetoidList.InA oeq x s) -> (x \in s).
  Proof.
    elim: s x => [| a s IH] x Hin /=.
    - by inversion Hin.
    - rewrite oin_cons. case/InA_cons: Hin => Hin.
      + by move/oeqP: Hin => ->.
      + by rewrite (IH _ Hin) orbT.
  Qed.

  Lemma oin_inA x s : (x \in s) -> (SetoidList.InA oeq x s).
  Proof.
    elim: s x => [| a s IH] x Hin //=. rewrite oin_cons in Hin.
    case/orP: Hin => Hin.
    - left. apply/oeqP; assumption.
    - right. exact: (IH _ Hin).
  Qed.

  Lemma oinP x s : reflect (SetoidList.InA oeq x s) (x \in s).
  Proof.
    case Hin: (x \in s).
    - apply: ReflectT. exact: (oin_inA Hin).
    - apply: ReflectF. move=> H. apply/negPf: Hin. exact: (inA_oin H).
  Qed.

End ListPredType.

Notation "x '\in' A :> T" :=  (in_mem x (mem (A : T)))
                                (at level 70, no associativity, only parsing, A at next level).


(** * mathcomp orderType as orderedType *)

Module MathCompOrderedType.

  Section MathCompOrderedTypeLemmas.

    Context {disp : unit}.
    Context {t : orderType disp}.

    Definition eq (x y : t) : Prop := eq_op x y.

    Definition lt (x y : t) : Prop := (x < y)%O.

    Definition le (x y : t) : Prop := (x <= y)%O.

    Definition ltb (x y : t) : bool := (x < y)%O.

    Definition leb (x y : t) : bool := (x <= y)%O.

    Definition eq_refl : forall x : t, eq x x := fun x : t => eqxx x.

    Lemma eq_sym : forall x y : t, eq x y -> eq y x.
    Proof. move=> x y H. rewrite /eq (eqtype.eq_sym). assumption. Qed.

    Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    Proof.
      rewrite /eq => x y z Hxy Hyz. rewrite (eqP Hxy) (eqP Hyz).
      exact: eqxx.
    Qed.

    Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Proof. rewrite /lt => x y z. exact: Order.POrderTheory.lt_trans. Qed.

    Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    Proof.
      rewrite /lt /eq => x y Hlt Heq. rewrite (eqP Heq) in Hlt.
      rewrite Order.POrderTheory.ltxx in Hlt. discriminate.
    Qed.

    Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
    Proof.
      rewrite /le /lt /eq => x y. rewrite Order.POrderTheory.le_eqVlt.
      case_all; by eauto.
    Qed.

    Definition compare : forall x y : t, Compare lt eq x y.
    Proof.
      rewrite /lt /eq => x y. case Heq: (x == y).
      - apply: EQ; assumption.
      - case Hlt: (x < y)%O.
        + apply: LT; assumption.
        + apply: GT. by rewrite Order.TotalTheory.ltNge Order.POrderTheory.le_eqVlt
                                negb_orb Heq Hlt.
    Defined.

    Lemma ltb_lt (x y : t) : ltb x y <-> lt x y.
    Proof. tauto. Qed.

    Lemma leb_le (x y : t) : leb x y <-> le x y.
    Proof. tauto. Qed.

  End MathCompOrderedTypeLemmas.

  Module Exports.

    Definition mathcompOrderedTypeMixin (disp : unit) (t : orderType disp) :=
      @OrderedTypeMixin t eq lt le
                        eq_refl eq_sym eq_trans lt_trans
                        lt_not_eq le_lteq compare.

    Canonical mathcompOrderedType (disp : unit) (t : orderType disp) :=
      Eval hnf in OrderedType t (mathcompOrderedTypeMixin t).

    Definition mathcompDecidableOrderedTypeMixin' (disp : unit) (t : orderType disp) :=
      @DecidableOrderedTypeMixin t (mathcompOrderedTypeMixin t)
                                 ltb leb ltb_lt leb_le.

    Definition mathcompDecidableOrderedTypeMixin (disp : unit) (t : orderType disp) :=
      {| DecidableOrderedType.base := mathcompOrderedTypeMixin t
      ; DecidableOrderedType.mixin := mathcompDecidableOrderedTypeMixin' t |}.

    Canonical mathcompDecidableOrderedType (disp : unit) (t : orderType disp) :=
      Eval hnf in DecidableOrderedType t (mathcompDecidableOrderedTypeMixin t).

  End Exports.

End MathCompOrderedType.

Export MathCompOrderedType.Exports.
Coercion MathCompOrderedType.Exports.mathcompOrderedType : orderType >-> orderedType.
Coercion MathCompOrderedType.Exports.mathcompDecidableOrderedType : orderType >-> decidableOrderedType.


(** ** Additional orderType Lemmas *)

Section OrderTypeLemmas.

  Context {disp : unit}.
  Context {t : orderType disp}.

  Local Open Scope order_scope.

  Lemma nlt_eqVlt (x y : t) : (~~ (x < y)) = ((x == y) || (y < x)).
  Proof.
    case Heq: (x == y) => /=.
    - apply/negP => Hlt. move: (Order.POrderTheory.lt_eqF Hlt). by rewrite Heq.
    - rewrite -Order.TotalTheory.leNgt Order.POrderTheory.le_eqVlt eqtype.eq_sym Heq /=.
      reflexivity.
  Qed.

  Lemma lt_neqAlt (x y : t) : (x < y) = (x != y) && (~~ (y < x)).
  Proof. rewrite -Order.TotalTheory.leNgt. exact: Order.POrderTheory.lt_neqAle. Qed.

End OrderTypeLemmas.


(** * Instances of orderedType, decidableOrderedType, Ordered, and DecidableOrdered *)

Module HasNatDecidableOrderedType <: HasDecidableOrderedType.
  Definition t : decidableOrderedType := Order.NatOrder.orderType.
End HasNatDecidableOrderedType.

Module NatOrdered := HDOT_as_DOT HasNatDecidableOrderedType.

(*
  Add the following coercion so that we can write [forall n : nat, (n <= n)%OT]
  instead of [forall n : nat, (n <= n :> mathcompOrderedType Order.NatOrder.orderType)%OT].
*)
Definition nat2orderedType : nat -> mathcompOrderedType Order.NatOrder.orderType := id.
Coercion nat2orderedType : nat >-> OrderedType.sort.


Module PositiveOrderedType.

  Definition positiveOrderedTypeMixin :=
    @OrderedTypeMixin positive Logic.eq Pos.lt Pos.le
                      Pos.eq_refl Pos.eq_sym Pos.eq_trans Pos.lt_trans
                      DecidableTypeEx.Positive_as_DT.lt_not_eq
                      Pos.le_lteq DecidableTypeEx.Positive_as_DT.compare.

  Canonical positiveOrderedType :=
    Eval hnf in OrderedType positive positiveOrderedTypeMixin.

  Definition positiveDecidableOrderedTypeMixin' :=
    @DecidableOrderedTypeMixin positive positiveOrderedTypeMixin
                               Pos.ltb Pos.leb Pos.ltb_lt Pos.leb_le.

  Definition positiveDecidableOrderedTypeMixin :=
    {| DecidableOrderedType.base := positiveOrderedTypeMixin
    ; DecidableOrderedType.mixin := positiveDecidableOrderedTypeMixin' |}.

  Canonical positiveDecidableOrderedType :=
    Eval hnf in DecidableOrderedType positive positiveDecidableOrderedTypeMixin.

End PositiveOrderedType.


Module NOrderedType.

  Definition NOrderedTypeMixin :=
    @OrderedTypeMixin N Logic.eq N.lt N.le
                      N.eq_refl N.eq_sym N.eq_trans N.lt_trans
                      DecidableTypeEx.N_as_DT.lt_not_eq
                      N.le_lteq DecidableTypeEx.N_as_DT.compare.

  Canonical NOrderedType :=
    Eval hnf in OrderedType N NOrderedTypeMixin.

  Definition NDecidableOrderedTypeMixin' :=
    @DecidableOrderedTypeMixin N NOrderedTypeMixin
                               N.ltb N.leb N.ltb_lt N.leb_le.

  Definition NDecidableOrderedTypeMixin :=
    {| DecidableOrderedType.base := NOrderedTypeMixin
    ; DecidableOrderedType.mixin := NDecidableOrderedTypeMixin' |}.

  Canonical NDecidableOrderedType :=
    Eval hnf in DecidableOrderedType N NDecidableOrderedTypeMixin.

End NOrderedType.


Module ZOrderedType.

  Definition ZOrderedTypeMixin :=
    @OrderedTypeMixin Z Logic.eq Z.lt Z.le
                      Z.eq_refl Z.eq_sym Z.eq_trans Z.lt_trans
                      DecidableTypeEx.Z_as_DT.lt_not_eq
                      Z.le_lteq DecidableTypeEx.Z_as_DT.compare.

  Canonical ZOrderedType :=
    Eval hnf in OrderedType Z ZOrderedTypeMixin.

  Definition ZDecidableOrderedTypeMixin' :=
    @DecidableOrderedTypeMixin Z ZOrderedTypeMixin
                               Z.ltb Z.leb Z.ltb_lt Z.leb_le.

  Definition ZDecidableOrderedTypeMixin :=
    {| DecidableOrderedType.base := ZOrderedTypeMixin
    ; DecidableOrderedType.mixin := ZDecidableOrderedTypeMixin' |}.

  Canonical ZDecidableOrderedType :=
    Eval hnf in DecidableOrderedType Z ZDecidableOrderedTypeMixin.

End ZOrderedType.
