
From Coq Require Import Arith FSets OrderedType Zerob.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From ssrlib Require Import Tactics Orders Seqs.

(**
   This file provides fsetType - a structure of finite sets with interface
   from FSetInterface.

   Below is a list of conversions between various membership tests:
<<
               memPs                        memP
  x \in s  ************    mem x s      ***********      In x s
                             *       *                *     *
                             *          *          * inPo   *
                             *             *    *           *
                       memPo *                *             * inPa
                             *             *     *          *
                             *    memPa *           *       *
                             *       *                 *    *
                    x \in (elements s)  ************  InA oeq x (elements s)
                                            oinP
>>
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Declare Scope fset_scope.
Delimit Scope fset_scope with FS.


(** * fsetType: a finite set as a structure *)

Module FSetType.

  Local Open Scope ordered_scope.

  Structure mixin_of (elt : orderedType) (t : Type) :=
    Mixin { In : elt -> t -> Prop
          ; Equal : t -> t -> Prop := fun (s s' : t) => forall (a : elt), In a s <-> In a s'
          ; Subset : t -> t -> Prop := fun (s s' : t) => forall (a : elt), In a s -> In a s'
          ; Empty : t -> Prop := fun (s : t) => forall (a : elt), ~ In a s
          ; For_all : (elt -> Prop) -> t -> Prop :=
              fun (P : elt -> Prop) (s : t) => forall (x : elt), In x s -> P x
          ; Exists : (elt -> Prop) -> t -> Prop :=
              fun (P : elt -> Prop) (s : t) => exists (x : elt), In x s /\ P x
          ; empty : t
          ; is_empty : t -> bool
          ; mem : elt -> t -> bool
          ; add : elt -> t -> t
          ; singleton : elt -> t
          ; remove : elt -> t -> t
          ; union : t -> t -> t
          ; inter : t -> t -> t
          ; diff : t -> t -> t
          ; eq : t -> t -> Prop := Equal
          ; eq_dec : forall s s', { eq s s' } + { ~ eq s s' }
          ; equal : t -> t -> bool
          ; subset : t -> t -> bool
          ; fold : forall A : Type, (elt -> A -> A) -> t -> A -> A
          ; for_all : (elt -> bool) -> t -> bool
          ; exists_ : (elt -> bool) -> t -> bool
          ; filter : (elt -> bool) -> t -> t
          ; partition : (elt -> bool) -> t -> t * t
          ; cardinal : t -> nat
          ; elements : t -> olist elt
          ; choose : t -> option elt
          ; In_1 : forall s x y, x == y -> In x s -> In y s
          ; eq_refl : forall s, eq s s
          ; eq_sym : forall s s', eq s s' -> eq s' s
          ; eq_trans : forall s s' s'', eq s s' -> eq s' s'' -> eq s s''
          ; mem_1 : forall s x, In x s -> mem x s = true
          ; mem_2 : forall s x, mem x s = true -> In x s
          ; equal_1 : forall s s', Equal s s' -> equal s s' = true
          ; equal_2 : forall s s', equal s s' = true -> Equal s s'
          ; subset_1 : forall s s', Subset s s' -> subset s s' = true
          ; subset_2 : forall s s', subset s s' = true -> Subset s s'
          ; empty_1 : Empty empty
          ; is_empty_1 : forall s, Empty s -> is_empty s = true
          ; is_empty_2 : forall s, is_empty s = true -> Empty s
          ; add_1 : forall s x y, x == y -> In y (add x s)
          ; add_2 : forall s x y, In y s -> In y (add x s)
          ; add_3 : forall s x y, ~ x == y -> In y (add x s) -> In y s
          ; remove_1 : forall s x y, x == y -> ~ In y (remove x s)
          ; remove_2 : forall s x y, ~ x == y -> In y s -> In y (remove x s)
          ; remove_3 : forall s x y, In y (remove x s) -> In y s
          ; singleton_1 : forall x y, In y (singleton x) -> x == y
          ; singleton_2 : forall x y, x == y -> In y (singleton x)
          ; union_1 : forall s s' x, In x (union s s') -> In x s \/ In x s'
          ; union_2 : forall s s' x, In x s -> In x (union s s')
          ; union_3 : forall  s s' x, In x s' -> In x (union s s')
          ; inter_1 : forall s s' x, In x (inter s s') -> In x s
          ; inter_2 : forall s s' x, In x (inter s s') -> In x s'
          ; inter_3 : forall s s' x, In x s -> In x s' -> In x (inter s s')
          ; diff_1 : forall s s' x, In x (diff s s') -> In x s
          ; diff_2 : forall s s' x, In x (diff s s') -> ~ In x s'
          ; diff_3 : forall s s' x, In x s -> ~ In x s' -> In x (diff s s')
          ; fold_1 : forall s (A : Type) (i : A) (f : elt -> A -> A),
              fold f s i = fold_left (fun a e => f e a) (elements s) i
          ; cardinal_1 : forall s, cardinal s = length (elements s)
          ; filter_1 : forall s x f, compat_bool oeq f -> In x (filter f s) -> In x s
          ; filter_2 : forall s x f, compat_bool oeq f -> In x (filter f s) -> f x = true
          ; filter_3 : forall s x f,
              compat_bool oeq f -> In x s -> f x = true -> In x (filter f s)
          ; for_all_1 : forall s f,
              compat_bool oeq f ->
              For_all (fun x => f x = true) s -> for_all f s = true
          ; for_all_2 : forall s f,
              compat_bool oeq f ->
              for_all f s = true -> For_all (fun x => f x = true) s
          ; exists_1 : forall s f,
              compat_bool oeq f ->
              Exists (fun x => f x = true) s -> exists_ f s = true
          ; exists_2 : forall s f,
              compat_bool oeq f ->
              exists_ f s = true -> Exists (fun x => f x = true) s
          ; partition_1 : forall s f,
              compat_bool oeq f -> Equal (fst (partition f s)) (filter f s)
          ; partition_2 : forall s f,
              compat_bool oeq f ->
              Equal (snd (partition f s)) (filter (fun x => negb (f x)) s)
          ; elements_1 : forall s x, In x s -> InA oeq x (elements s)
          ; elements_2 : forall s x, InA oeq x (elements s) -> In x s
          ; elements_3w : forall s, NoDupA oeq (elements s)
          ; choose_1 : forall s x, choose s = Some x -> In x s
          ; choose_2 : forall s, choose s = None -> Empty s
          ; lt : t -> t -> Prop
          ; compare : forall s s' : t, Compare lt eq s s'
          ; min_elt : t -> option elt
          ; max_elt : t -> option elt
          ; lt_trans : forall s s' s'', lt s s' -> lt s' s'' -> lt s s''
          ; lt_not_eq : forall s s', lt s s' -> ~ eq s s'
          ; elements_3 : forall s, sort olt (elements s)
          ; min_elt_1 : forall s x, min_elt s = Some x -> In x s
          ; min_elt_2 : forall s x y, min_elt s = Some x -> In y s -> ~ y < x
          ; min_elt_3 : forall s, min_elt s = None -> Empty s
          ; max_elt_1 : forall s x, max_elt s = Some x -> In x s
          ; max_elt_2 : forall s x y, max_elt s = Some x -> In y s -> ~ x < y
          ; max_elt_3 : forall s, max_elt s = None -> Empty s
          ; choose_3 : forall s s' x y,
              choose s = Some x -> choose s' = Some y ->
              Equal s s' -> x == y
      }.
  Notation class_of := mixin_of (only parsing).

  Section ClassDef.

    Structure type (elt : orderedType) : Type :=
      Pack { sort; _ : class_of elt sort }.

    Local Coercion sort : type >-> Sortclass.

    Variables (elt : orderedType) (cT : type elt).

    Definition class := let: Pack _ c := cT return class_of elt cT in c.

  End ClassDef.

  Module Exports.
    Coercion sort : type >-> Sortclass.
    Notation fsetType := type.
    Notation FSetMixin := Mixin.
    Notation FSetType elt set m := (@Pack elt set m).

    Section Definitions.
      Context {elt : orderedType}.
      Context {t : fsetType elt}.

      Definition In := In (class t).
      Definition Equal := fun (s s' : t) => forall (a : elt), In a s <-> In a s'.
      Definition Subset := fun (s s' : t) => forall (a : elt), In a s -> In a s'.
      Definition Empty := fun (s : t) => forall (a : elt), ~ In a s.
      Definition For_all := fun (P : elt -> Prop) (s : t) => forall (x : elt), In x s -> P x.
      Definition Exists := fun (P : elt -> Prop) (s : t) => exists (x : elt), In x s /\ P x.
      Definition empty := empty (class t).
      Definition is_empty := is_empty (class t).
      Definition mem := mem (class t).
      Definition add := add (class t).
      Definition singleton := singleton (class t).
      Definition remove := remove (class t).
      Definition union := union (class t).
      Definition inter := inter (class t).
      Definition diff := diff (class t).
      Definition eq := Equal.
      Definition eq_dec := eq_dec (class t).
      Definition equal := equal (class t).
      Definition subset := subset (class t).
      Definition fold := fold (class t).
      Definition for_all := for_all (class t).
      Definition exists_ := exists_ (class t).
      Definition filter := filter (class t).
      Definition partition := partition (class t).
      Definition cardinal := cardinal (class t).
      Definition elements := elements (class t).
      Definition choose := choose (class t).
      Lemma In_1 : forall s x y, x == y -> In x s -> In y s.
      Proof. exact: In_1. Qed.
      Lemma eq_refl : forall s, eq s s.
      Proof. exact: eq_refl. Qed.
      Lemma eq_sym : forall s s', eq s s' -> eq s' s.
      Proof. exact: eq_sym. Qed.
      Lemma eq_trans : forall s s' s'', eq s s' -> eq s' s'' -> eq s s''.
      Proof. exact: eq_trans. Qed.
      Lemma mem_1 : forall s x, In x s -> mem x s = true.
      Proof. exact: mem_1. Qed.
      Lemma mem_2 : forall s x, mem x s = true -> In x s.
      Proof. exact: mem_2. Qed.
      Lemma equal_1 : forall s s', Equal s s' -> equal s s' = true.
      Proof. exact: equal_1. Qed.
      Lemma equal_2 : forall s s', equal s s' = true -> Equal s s'.
      Proof. exact: equal_2. Qed.
      Lemma subset_1 : forall s s', Subset s s' -> subset s s' = true.
      Proof. exact: subset_1. Qed.
      Lemma subset_2 : forall s s', subset s s' = true -> Subset s s'.
      Proof. exact: subset_2. Qed.
      Lemma empty_1 : Empty empty.
      Proof. exact: empty_1. Qed.
      Lemma is_empty_1 : forall s, Empty s -> is_empty s = true.
      Proof. exact: is_empty_1. Qed.
      Lemma is_empty_2 : forall s, is_empty s = true -> Empty s.
      Proof. exact: is_empty_2. Qed.
      Lemma add_1 : forall s x y, x == y -> In y (add x s).
      Proof. exact: add_1. Qed.
      Lemma add_2 : forall s x y, In y s -> In y (add x s).
      Proof. exact: add_2. Qed.
      Lemma add_3 : forall s x y, ~ x == y -> In y (add x s) -> In y s.
      Proof. exact: add_3. Qed.
      Lemma remove_1 : forall s x y, x == y -> ~ In y (remove x s).
      Proof. exact: remove_1. Qed.
      Lemma remove_2 : forall s x y, ~ x == y -> In y s -> In y (remove x s).
      Proof. exact: remove_2. Qed.
      Lemma remove_3 : forall s x y, In y (remove x s) -> In y s.
      Proof. exact: remove_3. Qed.
      Lemma singleton_1 : forall x y, In y (singleton x) -> x == y.
      Proof. exact: singleton_1. Qed.
      Lemma singleton_2 : forall x y, x == y -> In y (singleton x).
      Proof. exact: singleton_2. Qed.
      Lemma union_1 : forall s s' x, In x (union s s') -> In x s \/ In x s'.
      Proof. exact: union_1. Qed.
      Lemma union_2 : forall s s' x, In x s -> In x (union s s').
      Proof. exact: union_2. Qed.
      Lemma union_3 : forall  s s' x, In x s' -> In x (union s s').
      Proof. exact: union_3. Qed.
      Lemma inter_1 : forall s s' x, In x (inter s s') -> In x s.
      Proof. exact: inter_1. Qed.
      Lemma inter_2 : forall s s' x, In x (inter s s') -> In x s'.
      Proof. exact: inter_2. Qed.
      Lemma inter_3 : forall s s' x, In x s -> In x s' -> In x (inter s s').
      Proof. exact: inter_3. Qed.
      Lemma diff_1 : forall s s' x, In x (diff s s') -> In x s.
      Proof. exact: diff_1. Qed.
      Lemma diff_2 : forall s s' x, In x (diff s s') -> ~ In x s'.
      Proof. exact: diff_2. Qed.
      Lemma diff_3 : forall s s' x, In x s -> ~ In x s' -> In x (diff s s').
      Proof. exact: diff_3. Qed.
      Lemma fold_1 :
        forall s (A : Type) (i : A) (f : elt -> A -> A),
          fold f s i = fold_left (fun a e => f e a) (elements s) i.
      Proof. exact: fold_1. Qed.
      Lemma cardinal_1 : forall s, cardinal s = length (elements s).
      Proof. exact: cardinal_1. Qed.
      Lemma filter_1 : forall s x f, compat_bool oeq f -> In x (filter f s) -> In x s.
      Proof. exact: filter_1. Qed.
      Lemma filter_2 : forall s x f, compat_bool oeq f -> In x (filter f s) -> f x = true.
      Proof. exact: filter_2. Qed.
      Lemma filter_3 :
        forall s x f,
          compat_bool oeq f -> In x s -> f x = true -> In x (filter f s).
      Proof. exact: filter_3. Qed.
      Lemma for_all_1 :
        forall s f,
          compat_bool oeq f ->
          For_all (fun x => f x = true) s -> for_all f s = true.
      Proof. exact: for_all_1. Qed.
      Lemma for_all_2 :
        forall s f,
          compat_bool oeq f ->
          for_all f s = true -> For_all (fun x => f x = true) s.
      Proof. exact: for_all_2. Qed.
      Lemma exists_1 :
        forall s f,
          compat_bool oeq f ->
          Exists (fun x => f x = true) s -> exists_ f s = true.
      Proof. exact: exists_1. Qed.
      Lemma exists_2 :
        forall s f,
          compat_bool oeq f ->
          exists_ f s = true -> Exists (fun x => f x = true) s.
      Proof. exact: exists_2. Qed.
      Lemma partition_1 :
        forall s f,
          compat_bool oeq f -> Equal (fst (partition f s)) (filter f s).
      Proof. exact: partition_1. Qed.
      Lemma partition_2 :
        forall s f,
          compat_bool oeq f ->
          Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
      Proof. exact: partition_2. Qed.
      Lemma elements_1 : forall s x, In x s -> InA oeq x (elements s).
      Proof. exact: elements_1. Qed.
      Lemma elements_2 : forall s x, InA oeq x (elements s) -> In x s.
      Proof. exact: elements_2. Qed.
      Lemma elements_3w : forall s, NoDupA oeq (elements s).
      Proof. exact: elements_3w. Qed.
      Lemma choose_1 : forall s x, choose s = Some x -> In x s.
      Proof. exact: choose_1. Qed.
      Lemma choose_2 : forall s, choose s = None -> Empty s.
      Proof. exact: choose_2. Qed.
      Definition lt := lt (class t).
      Lemma compare : forall s s', Compare lt eq s s'.
      Proof. exact: compare. Qed.
      Definition min_elt := min_elt (class t).
      Definition max_elt := max_elt (class t).
      Lemma lt_trans : forall s s' s'', lt s s' -> lt s' s'' -> lt s s''.
      Proof. exact: lt_trans. Qed.
      Lemma lt_not_eq : forall s s', lt s s' -> ~ eq s s'.
      Proof. exact: lt_not_eq. Qed.
      Lemma elements_3 : forall s, Sorting.Sorted.sort olt (elements s).
      Proof. exact: elements_3. Qed.
      Lemma min_elt_1 : forall s x, min_elt s = Some x -> In x s.
      Proof. exact: min_elt_1. Qed.
      Lemma min_elt_2 : forall s x y, min_elt s = Some x -> In y s -> ~ y < x.
      Proof. exact: min_elt_2. Qed.
      Lemma min_elt_3 : forall s, min_elt s = None -> Empty s.
      Proof. exact: min_elt_3. Qed.
      Lemma max_elt_1 : forall s x, max_elt s = Some x -> In x s.
      Proof. exact: max_elt_1. Qed.
      Lemma max_elt_2 : forall s x y, max_elt s = Some x -> In y s -> ~ x < y.
      Proof. exact: max_elt_2. Qed.
      Lemma max_elt_3 : forall s, max_elt s = None -> Empty s.
      Proof. exact: max_elt_3. Qed.
      Lemma choose_3 :
        forall s s' x y,
          choose s = Some x -> choose s' = Some y ->
          Equal s s' -> x == y.
      Proof. exact: choose_3. Qed.

    End Definitions.

    Notation "s [=] t" := (Equal s t) (at level 70, no associativity) : fset_scope.
    Notation "s [<=] t" := (Subset s t) (at level 70, no associativity) : fset_scope.
    Notation "s [=?] t" := (equal s t) (at level 70, no associativity) : fset_scope.
    Notation "s [<=?] t" := (subset s t) (at level 70, no associativity) : fset_scope.
    Notation "s [\] t" := (diff s t) (at level 70, no associativity) : fset_scope.
    Notation "s [+] t" := (union s t) (at level 70, no associativity) : fset_scope.
    Notation "s [*] t" := (inter s t) (at level 70, no associativity) : fset_scope.
    Notation "a [::] s" := (add a s) (at level 70, no associativity) : fset_scope.
    Notation "s [-] a" := (remove a s) (at level 70, no associativity) : fset_scope.

    Global Hint Resolve mem_1 equal_1 subset_1 empty_1
           is_empty_1 choose_1 choose_2 add_1 add_2 remove_1
           remove_2 singleton_2 union_1 union_2 union_3
           inter_3 diff_3 fold_1 filter_3 for_all_1 exists_1
           partition_1 partition_2 elements_1 elements_3w
      : set.

    Global Hint Immediate In_1 mem_2 equal_2 subset_2 is_empty_2 add_3
           remove_3 singleton_1 inter_1 inter_2 diff_1 diff_2
           filter_1 filter_2 for_all_2 exists_2 elements_2
      : set.

    Global Hint Resolve elements_3 : set.

    Global Hint Immediate
           min_elt_1 min_elt_2 min_elt_3 max_elt_1 max_elt_2 max_elt_3 : set.

  End Exports.

End FSetType.

Export FSetType.Exports.


(** * Lemmas from FSetFacts. *)

Module FSetTypeFacts.

  Local Open Scope ordered_scope.
  Local Open Scope fset_scope.

  Section IffSpec.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Variable s s' s'' : t.
    Variable x y z : elt.

    Lemma In_eq_iff : x == y -> (In x s <-> In y s).
    Proof. split; apply In_1; by order. Qed.

    Lemma mem_iff : In x s <-> mem x s = true.
    Proof. split; [by apply mem_1 | by apply mem_2]. Qed.

    Lemma not_mem_iff : ~ In x s <-> mem x s = false.
    Proof. rewrite mem_iff; destruct (mem x s); intuition. Qed.

    Lemma equal_iff : s[=]s' <-> equal s s' = true.
    Proof. split; [ by apply equal_1 | by apply equal_2 ]. Qed.

    Lemma subset_iff : s[<=]s' <-> subset s s' = true.
    Proof. split; [ by apply subset_1 | by apply subset_2 ]. Qed.

    Lemma empty_iff : In (t:=t) x empty <-> False.
    Proof. intuition; by apply (empty_1 H). Qed.

    Lemma is_empty_iff : Empty s <-> is_empty s = true.
    Proof. split; [ by apply is_empty_1 | by apply is_empty_2 ]. Qed.

    Lemma singleton_iff : In (t:=t) y (singleton x) <-> x == y.
    Proof.
      split => H; [ exact: (singleton_1 H)
                  | exact: (singleton_2 H) ].
    Qed.

    Lemma add_iff : In y (add x s) <-> x == y \/ In y s.
    Proof.
      split; [ | destruct 1; [ apply add_1 | apply add_2 ] ]; auto.
      destruct (OrderedTypeLemmas.eq_dec x y) as [ E | E ]; auto.
      intro H; right; exact (add_3 E H).
    Qed.

    Lemma add_neq_iff : ~ x == y -> (In y (add x s)  <-> In y s).
    Proof. by split; [ apply add_3 | apply add_2 ]; auto. Qed.

    Lemma remove_iff : In y (remove x s) <-> In y s /\ ~ x == y.
    Proof.
      split; [split; [apply remove_3 with x |] | destruct 1; apply remove_2]; auto.
      intro. by apply (remove_1 H0 H).
    Qed.

    Lemma remove_neq_iff : ~ x == y -> (In y (remove x s) <-> In y s).
    Proof. by split; [ apply remove_3 | apply remove_2 ]; auto. Qed.

    Lemma union_iff : In x (union s s') <-> In x s \/ In x s'.
    Proof.
      split; [apply union_1 | destruct 1; [apply union_2|apply union_3]]; auto.
    Qed.

    Lemma inter_iff : In x (inter s s') <-> In x s /\ In x s'.
    Proof.
      split; [split; [apply inter_1 with s' | apply inter_2 with s] | destruct 1; apply inter_3]; auto.
    Qed.

    Lemma diff_iff : In x (diff s s') <-> In x s /\ ~ In x s'.
    Proof.
      split; [split; [apply diff_1 with s' | apply diff_2 with s] | destruct 1; apply diff_3]; auto.
    Qed.

    Variable f : elt -> bool.

    Lemma filter_iff :  compat_bool oeq f -> (In x (filter f s) <-> In x s /\ f x = true).
    Proof.
      split; [split; [apply filter_1 with f | apply filter_2 with s] | destruct 1; apply filter_3]; auto.
    Qed.

    Lemma for_all_iff : compat_bool oeq f ->
                        (For_all (fun x => f x = true) s <-> for_all f s = true).
    Proof.
      split; [apply for_all_1 | apply for_all_2]; auto.
    Qed.

    Lemma exists_iff : compat_bool oeq f ->
                       (Exists (fun x => f x = true) s <-> exists_ f s = true).
    Proof.
      split; [apply exists_1 | apply exists_2]; auto.
    Qed.

    Lemma elements_iff : In x s <-> InA oeq x (elements s).
    Proof.
      split; [apply elements_1 | apply elements_2].
    Qed.

  End IffSpec.

  Ltac set_iff :=
    repeat (progress (
                rewrite add_iff || rewrite remove_iff || rewrite singleton_iff
                || rewrite union_iff || rewrite inter_iff || rewrite diff_iff
                || rewrite empty_iff)).

  Section BoolSpec.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Variable s s' s'' : t.
    Variable x y z : elt.

    Lemma mem_b : x == y -> mem x s = mem y s.
    Proof.
      intros.
      generalize (mem_iff s x) (mem_iff s y) (In_eq_iff s H).
      destruct (mem x s); destruct (mem y s); intuition.
    Qed.

    Lemma empty_b : mem (t:=t) y empty = false.
    Proof.
      generalize (empty_iff (t:=t) y) (mem_iff (t:=t) empty y).
      destruct (mem y empty); intuition.
    Qed.

    Lemma add_b : mem y (add x s) = eqb x y || mem y s.
    Proof.
      generalize (mem_iff (add x s) y) (mem_iff s y) (add_iff s x y); unfold eqb.
      destruct (OrderedTypeLemmas.eq_dec x y); destruct (mem y s); destruct (mem y (add x s)); intuition.
      by elim: (n H0).
    Qed.

    Lemma add_neq_b : ~ x == y -> mem y (add x s) = mem y s.
    Proof.
      intros; generalize (mem_iff (add x s) y) (mem_iff s y) (add_neq_iff s H).
      destruct (mem y s); destruct (mem y (add x s)); intuition.
    Qed.

    Lemma remove_b : mem y (remove x s) = mem y s && negb (eqb x y).
    Proof.
      generalize (mem_iff (remove x s) y) (mem_iff s y) (remove_iff s x y); unfold eqb.
      destruct (OrderedTypeLemmas.eq_dec x y); destruct (mem y s); destruct (mem y (remove x s)); simpl; intuition.
    Qed.

    Lemma remove_neq_b : ~ x == y -> mem y (remove x s) = mem y s.
    Proof.
      intros; generalize (mem_iff (remove x s) y) (mem_iff s y) (remove_neq_iff s H).
      destruct (mem y s); destruct (mem y (remove x s)); intuition.
    Qed.

    Lemma singleton_b : mem (t:=t) y (singleton x) = eqb x y.
    Proof.
      generalize (mem_iff (t:=t) (singleton x) y) (singleton_iff (t:=t) x y); unfold eqb.
      destruct (OrderedTypeLemmas.eq_dec x y); destruct (mem y (singleton x)); intuition.
      by elim: (n H1).
    Qed.

    Lemma union_b : mem x (union s s') = mem x s || mem x s'.
    Proof.
      generalize (mem_iff (union s s') x) (mem_iff s x) (mem_iff s' x) (union_iff s s' x).
      destruct (mem x s); destruct (mem x s'); destruct (mem x (union s s')); intuition.
    Qed.

    Lemma inter_b : mem x (inter s s') = mem x s && mem x s'.
    Proof.
      generalize (mem_iff (inter s s') x) (mem_iff s x) (mem_iff s' x) (inter_iff s s' x).
      destruct (mem x s); destruct (mem x s'); destruct (mem x (inter s s')); intuition.
    Qed.

    Lemma diff_b : mem x (diff s s') = mem x s && negb (mem x s').
    Proof.
      generalize (mem_iff (diff s s') x) (mem_iff s x) (mem_iff s' x) (diff_iff s s' x).
      destruct (mem x s); destruct (mem x s'); destruct (mem x (diff s s')); simpl; intuition.
    Qed.

    Lemma elements_b : mem x s = existsb (eqb x) (elements s).
    Proof.
      generalize (mem_iff s x) (elements_iff s x) (existsb_exists (eqb x) (elements s)).
      rewrite InA_alt.
      destruct (mem x s); destruct (existsb (eqb x) (elements s)); auto; intros.
      symmetry.
      rewrite H1.
      destruct H0 as (H0,_).
      destruct H0 as (a,(Ha1,Ha2)); [ intuition |].
      exists a; intuition.
      unfold eqb; destruct (OrderedTypeLemmas.eq_dec x a); auto.
      rewrite <- H.
      rewrite H0.
      destruct H1 as (H1,_).
      destruct H1 as (a,(Ha1,Ha2)); [intuition|].
      exists a; intuition.
      unfold eqb in *; destruct (OrderedTypeLemmas.eq_dec x a); auto; discriminate.
    Qed.

    Variable f : elt -> bool.

    Lemma filter_b : compat_bool oeq f -> mem x (filter f s) = mem x s && f x.
    Proof.
      intros.
      generalize (mem_iff (filter f s) x) (mem_iff s x) (filter_iff s x H).
      destruct (mem x s); destruct (mem x (filter f s)); destruct (f x); simpl; intuition.
    Qed.

    Lemma for_all_b : compat_bool oeq f ->
                      for_all f s = forallb f (elements s).
    Proof.
      intros.
      generalize (forallb_forall f (elements s)) (for_all_iff s H) (elements_iff s).
      unfold For_all.
      destruct (forallb f (elements s)); destruct (for_all f s); auto; intros.
      - rewrite <- H1; intros.
        destruct H0 as (H0,_).
        rewrite (H2 x0) in H3.
        rewrite (InA_alt oeq x0 (elements s)) in H3.
        destruct H3 as (a,(Ha1,Ha2)).
        rewrite (H _ _ Ha1).
        apply H0; auto.
      - symmetry.
        rewrite H0; intros.
        destruct H1 as (_,H1).
        apply H1; auto.
        rewrite H2.
        rewrite InA_alt.
        exists x0. split; auto. exact: OrderedType.eq_refl.
    Qed.

    Lemma exists_b : compat_bool oeq f ->
                     exists_ f s = existsb f (elements s).
    Proof.
      intros.
      generalize (existsb_exists f (elements s)) (exists_iff s H) (elements_iff s).
      unfold Exists.
      destruct (existsb f (elements s)); destruct (exists_ f s); auto; intros.
      - rewrite <- H1; intros.
        destruct H0 as (H0,_).
        destruct H0 as (a,(Ha1,Ha2)); auto.
        exists a; split; auto.
        rewrite H2; rewrite InA_alt.
        exists a.
        split; auto. exact: OrderedType.eq_refl.
      - symmetry.
        rewrite H0.
        destruct H1 as (_,H1).
        destruct H1 as (a,(Ha1,Ha2)); auto.
        rewrite (H2 a) in Ha1.
        rewrite (InA_alt oeq a (elements s)) in Ha1.
        destruct Ha1 as (b,(Hb1,Hb2)).
        exists b; auto.
        rewrite <- (H _ _ Hb1); auto.
    Qed.

  End BoolSpec.

  Section Setoid.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Global Instance Equal_ST : Equivalence (Equal (t:=t)).
    Proof.
      constructor ; red; [apply eq_refl | apply eq_sym | apply eq_trans].
    Qed.

    Global Instance In_m : Proper (oeq ==> Equal (t:=t) ==> iff) In.
    Proof.
      unfold Equal; intros x y H s s' H0.
      rewrite (In_eq_iff s H); auto.
    Qed.

    Global Instance is_empty_m : Proper (Equal (t:=t) ==> Logic.eq) is_empty.
    Proof.
      unfold Equal; intros s s' H.
      generalize (is_empty_iff s) (is_empty_iff s').
      destruct (is_empty s); destruct (is_empty s');
        unfold Empty; auto; intros.
      - symmetry.
        rewrite <- H1; intros a Ha.
        rewrite <- (H a) in Ha.
        destruct H0 as (_,H0).
        exact (H0 Logic.eq_refl _ Ha).
      - rewrite <- H0; intros a Ha.
        rewrite (H a) in Ha.
        destruct H1 as (_,H1).
        exact (H1 Logic.eq_refl _ Ha).
    Qed.

    Global Instance Empty_m : Proper (Equal (t:=t) ==> iff) Empty.
    Proof.
      repeat red; intros; do 2 rewrite is_empty_iff; rewrite H; intuition.
    Qed.

    Global Instance mem_m : Proper (oeq ==> Equal (t:=t) ==> Logic.eq) mem.
    Proof.
      unfold Equal; intros x y H s s' H0.
      generalize (H0 x); clear H0; rewrite (In_eq_iff s' H).
      generalize (mem_iff s x) (mem_iff s' y).
      destruct (mem x s); destruct (mem y s'); intuition.
    Qed.

    Global Instance singleton_m : Proper (oeq ==> Equal (t:=t)) singleton.
    Proof.
      unfold Equal; intros x y H a.
      do 2 rewrite singleton_iff; split; intros.
      - exact: (OrderedType.eq_trans (OrderedType.eq_sym H) H0).
      - exact: (OrderedType.eq_trans H H0).
    Qed.

    Global Instance add_m : Proper (oeq ==> Equal (t:=t) ==> Equal) add.
    Proof.
      unfold Equal; intros x y H s s' H0 a.
      do 2 rewrite add_iff; rewrite H; rewrite H0; intuition.
    Qed.

    Global Instance remove_m : Proper (oeq ==> Equal (t:=t) ==> Equal) remove.
    Proof.
      unfold Equal; intros x y H s s' H0 a.
      do 2 rewrite remove_iff; rewrite H; rewrite H0; intuition.
    Qed.

    Global Instance union_m : Proper (Equal (t:=t) ==> Equal ==> Equal) union.
    Proof.
      unfold Equal; intros s s' H s'' s''' H0 a.
      do 2 rewrite union_iff; rewrite H; rewrite H0; intuition.
    Qed.

    Global Instance inter_m : Proper (Equal (t:=t) ==> Equal ==> Equal) inter.
    Proof.
      unfold Equal; intros s s' H s'' s''' H0 a.
      do 2 rewrite inter_iff; rewrite H; rewrite H0; intuition.
    Qed.

    Global Instance diff_m : Proper (Equal (t:=t) ==> Equal ==> Equal) diff.
    Proof.
      unfold Equal; intros s s' H s'' s''' H0 a.
      do 2 rewrite diff_iff; rewrite H; rewrite H0; intuition.
    Qed.

    Global Instance Subset_m : Proper (Equal (t:=t) ==> Equal ==> iff) Subset.
    Proof.
      unfold Equal, Subset; firstorder.
    Qed.

    Global Instance subset_m : Proper (Equal (t:=t) ==> Equal ==> Logic.eq) subset.
    Proof.
      intros s s' H s'' s''' H0.
      generalize (subset_iff s s'') (subset_iff s' s''').
      destruct (subset s s''); destruct (subset s' s'''); auto; intros.
      rewrite H in H1; rewrite H0 in H1; intuition.
      rewrite H in H1; rewrite H0 in H1; intuition.
    Qed.

    Global Instance equal_m : Proper (Equal (t:=t) ==> Equal ==> Logic.eq) equal.
    Proof.
      intros s s' H s'' s''' H0.
      generalize (equal_iff s s'') (equal_iff s' s''').
      destruct (equal s s''); destruct (equal s' s'''); auto; intros.
      rewrite H in H1; rewrite H0 in H1; intuition.
      rewrite H in H1; rewrite H0 in H1; intuition.
    Qed.

    Lemma Subset_refl : forall (s : t), s [<=] s.
    Proof. red; auto. Qed.

    Lemma Subset_trans : forall (s s' s'' : t), s [<=] s' -> s' [<=] s'' -> s [<=] s''.
    Proof. unfold Subset; eauto. Qed.

    Add Relation t Subset
        reflexivity proved by Subset_refl
        transitivity proved by Subset_trans
        as SubsetSetoid.

    Global Instance In_s_m : Morphisms.Proper (oeq ==> Subset (t:=t) ++> Basics.impl) In | 1.
    Proof.
      move=> x y Hxy s u Hsu Hxs. rewrite <- Hxy. exact: (Hsu _ Hxs).
    Qed.

    Add Morphism Empty with signature Subset (t:=t) --> Basics.impl as Empty_s_m.
    Proof.
      unfold Subset, Empty, Basics.impl; firstorder.
    Qed.

    Add Morphism add with signature oeq ==> Subset ++> Subset (t:=t) as add_s_m.
    Proof.
      unfold Subset; intros x y H s s' H0 a.
      do 2 rewrite add_iff; rewrite H; intuition.
    Qed.

    Add Morphism remove with signature oeq ==> Subset ++> Subset (t:=t) as remove_s_m.
    Proof.
      unfold Subset; intros x y H s s' H0 a.
      do 2 rewrite remove_iff; rewrite H; intuition.
    Qed.

    Add Morphism union with signature Subset ++> Subset ++> Subset (t:=t) as union_s_m.
    Proof.
      unfold Equal; intros s s' H s'' s''' H0 a.
      do 2 rewrite union_iff; intuition.
    Qed.

    Add Morphism inter with signature Subset ++> Subset ++> Subset (t:=t) as inter_s_m.
    Proof.
      unfold Equal; intros s s' H s'' s''' H0 a.
      do 2 rewrite inter_iff; intuition.
    Qed.

    Add Morphism diff with signature Subset ++> Subset --> Subset (t:=t) as diff_s_m.
    Proof.
      unfold Subset; intros s s' H s'' s''' H0 a.
      do 2 rewrite diff_iff; intuition.
    Qed.

    Lemma filter_equal : forall f, compat_bool oeq f ->
                                   forall (s s' : t), s [=] s' -> filter f s [=] filter f s'.
    Proof.
      unfold Equal; intros; repeat rewrite filter_iff; auto; rewrite H0; tauto.
    Qed.

    Lemma filter_ext : forall f f', compat_bool oeq f -> (forall x, f x = f' x) ->
                                    forall (s s' : t), s [=] s' -> filter f s [=] filter f' s'.
    Proof.
      intros f f' Hf Hff' s s' Hss' x. do 2 (rewrite filter_iff; auto).
      rewrite -> Hff', Hss'; intuition.
      repeat red; intros; rewrite <- 2 Hff'; auto.
    Qed.

    Lemma filter_subset : forall f, compat_bool oeq f ->
                                    forall (s s' : t), s [<=] s' -> filter f s [<=] filter f s'.
    Proof.
      unfold Subset; intros; rewrite -> filter_iff in *; intuition.
    Qed.

  End Setoid.

  Global Hint Resolve add_neq_b : set.

End FSetTypeFacts.

Export FSetTypeFacts.


(** * Tactics from FSetDecide *)

From Coq Require Import Decidable.

Module FSetTypeDecide.

  Local Open Scope fset_scope.

  Tactic Notation "fold" "any" "not" :=
    repeat (
        match goal with
        | H: context [?P -> False] |- _ =>
            fold (~ P) in H
        | |- context [?P -> False] =>
            fold (~ P)
        end).

    Ltac or_not_l_iff P Q tac :=
      (rewrite -> (or_not_l_iff_1 P Q) by tac) ||
      (rewrite -> (or_not_l_iff_2 P Q) by tac).

    Ltac or_not_r_iff P Q tac :=
      (rewrite -> (or_not_r_iff_1 P Q) by tac) ||
      (rewrite -> (or_not_r_iff_2 P Q) by tac).

    Ltac or_not_l_iff_in P Q H tac :=
      (rewrite -> (or_not_l_iff_1 P Q) in H by tac) ||
      (rewrite -> (or_not_l_iff_2 P Q) in H by tac).

    Ltac or_not_r_iff_in P Q H tac :=
      (rewrite -> (or_not_r_iff_1 P Q) in H by tac) ||
      (rewrite -> (or_not_r_iff_2 P Q) in H by tac).

    Tactic Notation "push" "not" "using" ident(db) :=
      let dec := solve_decidable using db in
      unfold not, iff;
      repeat (
        match goal with
        | |- context [True -> False] => rewrite not_true_iff
        | |- context [False -> False] => rewrite not_false_iff
        | |- context [(?P -> False) -> False] => rewrite -> (not_not_iff P) by dec
        | |- context [(?P -> False) -> (?Q -> False)] =>
            rewrite -> (contrapositive P Q) by dec
        | |- context [(?P -> False) \/ ?Q] => or_not_l_iff P Q dec
        | |- context [?P \/ (?Q -> False)] => or_not_r_iff P Q dec
        | |- context [(?P -> False) -> ?Q] => rewrite -> (imp_not_l P Q) by dec
        | |- context [?P \/ ?Q -> False] => rewrite (not_or_iff P Q)
        | |- context [?P /\ ?Q -> False] => rewrite (not_and_iff P Q)
        | |- context [(?P -> ?Q) -> False] => rewrite -> (not_imp_iff P Q) by dec
        end);
      fold any not.

    Tactic Notation "push" "not" :=
      push not using core.

    Tactic Notation
      "push" "not" "in" "*" "|-" "using" ident(db) :=
      let dec := solve_decidable using db in
      unfold not, iff in * |-;
      repeat (
        match goal with
        | H: context [True -> False] |- _ => rewrite not_true_iff in H
        | H: context [False -> False] |- _ => rewrite not_false_iff in H
        | H: context [(?P -> False) -> False] |- _ =>
          rewrite -> (not_not_iff P) in H by dec
        | H: context [(?P -> False) -> (?Q -> False)] |- _ =>
          rewrite -> (contrapositive P Q) in H by dec
        | H: context [(?P -> False) \/ ?Q] |- _ => or_not_l_iff_in P Q H dec
        | H: context [?P \/ (?Q -> False)] |- _ => or_not_r_iff_in P Q H dec
        | H: context [(?P -> False) -> ?Q] |- _ =>
          rewrite -> (imp_not_l P Q) in H by dec
        | H: context [?P \/ ?Q -> False] |- _ => rewrite (not_or_iff P Q) in H
        | H: context [?P /\ ?Q -> False] |- _ => rewrite (not_and_iff P Q) in H
        | H: context [(?P -> ?Q) -> False] |- _ =>
          rewrite -> (not_imp_iff P Q) in H by dec
        end);
      fold any not.

    Tactic Notation "push" "not" "in" "*" "|-"  :=
      push not in * |- using core.

    Tactic Notation "push" "not" "in" "*" "using" ident(db) :=
      push not using db; push not in * |- using db.
    Tactic Notation "push" "not" "in" "*" :=
      push not in * using core.

    Lemma test_push : forall P Q R : Prop,
      decidable P ->
      decidable Q ->
      (~ True) ->
      (~ False) ->
      (~ ~ P) ->
      (~ (P /\ Q) -> ~ R) ->
      ((P /\ Q) \/ ~ R) ->
      (~ (P /\ Q) \/ R) ->
      (R \/ ~ (P /\ Q)) ->
      (~ R \/ (P /\ Q)) ->
      (~ P -> R) ->
      (~ ((R -> P) \/ (Q -> R))) ->
      (~ (P /\ R)) ->
      (~ (P -> R)) ->
      True.
    Proof.
      intros. push not in *.
       (* note that ~(R->P) remains (since R isn't decidable) *)
      tauto.
    Qed.

    Tactic Notation "pull" "not" "using" ident(db) :=
      let dec := solve_decidable using db in
      unfold not, iff;
      repeat (
        match goal with
        | |- context [True -> False] => rewrite not_true_iff
        | |- context [False -> False] => rewrite not_false_iff
        | |- context [(?P -> False) -> False] => rewrite -> (not_not_iff P) by dec
        | |- context [(?P -> False) -> (?Q -> False)] =>
          rewrite -> (contrapositive P Q) by dec
        | |- context [(?P -> False) \/ ?Q] => or_not_l_iff P Q dec
        | |- context [?P \/ (?Q -> False)] => or_not_r_iff P Q dec
        | |- context [(?P -> False) -> ?Q] => rewrite -> (imp_not_l P Q) by dec
        | |- context [(?P -> False) /\ (?Q -> False)] =>
          rewrite <- (not_or_iff P Q)
        | |- context [?P -> ?Q -> False] => rewrite <- (not_and_iff P Q)
        | |- context [?P /\ (?Q -> False)] => rewrite <- (not_imp_iff P Q) by dec
        | |- context [(?Q -> False) /\ ?P] =>
          rewrite <- (not_imp_rev_iff P Q) by dec
        end);
      fold any not.

    Tactic Notation "pull" "not" :=
      pull not using core.

    Tactic Notation
      "pull" "not" "in" "*" "|-" "using" ident(db) :=
      let dec := solve_decidable using db in
      unfold not, iff in * |-;
      repeat (
        match goal with
        | H: context [True -> False] |- _ => rewrite not_true_iff in H
        | H: context [False -> False] |- _ => rewrite not_false_iff in H
        | H: context [(?P -> False) -> False] |- _ =>
          rewrite -> (not_not_iff P) in H by dec
        | H: context [(?P -> False) -> (?Q -> False)] |- _ =>
          rewrite -> (contrapositive P Q) in H by dec
        | H: context [(?P -> False) \/ ?Q] |- _ => or_not_l_iff_in P Q H dec
        | H: context [?P \/ (?Q -> False)] |- _ => or_not_r_iff_in P Q H dec
        | H: context [(?P -> False) -> ?Q] |- _ =>
          rewrite -> (imp_not_l P Q) in H by dec
        | H: context [(?P -> False) /\ (?Q -> False)] |- _ =>
          rewrite <- (not_or_iff P Q) in H
        | H: context [?P -> ?Q -> False] |- _ =>
          rewrite <- (not_and_iff P Q) in H
        | H: context [?P /\ (?Q -> False)] |- _ =>
          rewrite <- (not_imp_iff P Q) in H by dec
        | H: context [(?Q -> False) /\ ?P] |- _ =>
          rewrite <- (not_imp_rev_iff P Q) in H by dec
        end);
      fold any not.

    Tactic Notation "pull" "not" "in" "*" "|-"  :=
      pull not in * |- using core.

    Tactic Notation "pull" "not" "in" "*" "using" ident(db) :=
      pull not using db; pull not in * |- using db.
    Tactic Notation "pull" "not" "in" "*" :=
      pull not in * using core.

    Lemma test_pull : forall P Q R : Prop,
      decidable P ->
      decidable Q ->
      (~ True) ->
      (~ False) ->
      (~ ~ P) ->
      (~ (P /\ Q) -> ~ R) ->
      ((P /\ Q) \/ ~ R) ->
      (~ (P /\ Q) \/ R) ->
      (R \/ ~ (P /\ Q)) ->
      (~ R \/ (P /\ Q)) ->
      (~ P -> R) ->
      (~ (R -> P) /\ ~ (Q -> R)) ->
      (~ P \/ ~ R) ->
      (P /\ ~ R) ->
      (~ R /\ P) ->
      True.
    Proof.
      intros. pull not in *. tauto.
    Qed.

    Ltac no_logical_interdep :=
      match goal with
        | H : ?P |- _ =>
          match type of P with
            | Prop =>
              match goal with H' : context [ H ] |- _ => clear dependent H' end
            | _ => fail
          end; no_logical_interdep
        | _ => idtac
      end.

    Ltac abstract_term t :=
      tryif (is_var t) then fail "no need to abstract a variable"
      else (let x := fresh "x" in set (x := t) in *; try clearbody x).

    Ltac abstract_elements :=
      repeat
        (match goal with
           | |- context [ singleton ?t ] => abstract_term t
           | _ : context [ singleton ?t ] |- _ => abstract_term t
           | |- context [ add ?t _ ] => abstract_term t
           | _ : context [ add ?t _ ] |- _ => abstract_term t
           | |- context [ remove ?t _ ] => abstract_term t
           | _ : context [ remove ?t _ ] |- _ => abstract_term t
           | |- context [ In ?t _ ] => abstract_term t
           | _ : context [ In ?t _ ] |- _ => abstract_term t
         end).

    Tactic Notation "prop" constr(P) "holds" "by" tactic(t) :=
      let H := fresh in
      assert P as H by t;
      clear H.

    Tactic Notation "assert" "new" constr(e) "by" tactic(t) :=
      match goal with
      | H: e |- _ => fail 1
      | _ => assert e by t
      end.

    Tactic Notation "subst" "++" :=
      repeat (
        match goal with
        | x : _ |- _ => subst x
        end);
      cbv zeta beta in *.

    Tactic Notation "decompose" "records" :=
      repeat (
        match goal with
        | H: _ |- _ => progress (decompose record H); clear H
        end).

    Section FSetDecideAuxiliary.

      Context {elt : orderedType}.
      Context {t : fsetType elt}.

      Inductive FSet_elt_Prop : Prop -> Prop :=
      | eq_Prop : forall (S : Type) (x y : S),
          FSet_elt_Prop (x = y)
      | eq_elt_prop : forall (x y : elt),
          FSet_elt_Prop (oeq x y)
      | In_elt_prop : forall (x : elt) (s : t),
          FSet_elt_Prop (In x s)
      | True_elt_prop :
        FSet_elt_Prop True
      | False_elt_prop :
        FSet_elt_Prop False
      | conj_elt_prop : forall P Q,
          FSet_elt_Prop P ->
          FSet_elt_Prop Q ->
          FSet_elt_Prop (P /\ Q)
      | disj_elt_prop : forall P Q,
          FSet_elt_Prop P ->
          FSet_elt_Prop Q ->
          FSet_elt_Prop (P \/ Q)
      | impl_elt_prop : forall P Q,
          FSet_elt_Prop P ->
          FSet_elt_Prop Q ->
          FSet_elt_Prop (P -> Q)
      | not_elt_prop : forall P,
          FSet_elt_Prop P ->
          FSet_elt_Prop (~ P).

      Inductive FSet_Prop : Prop -> Prop :=
      | elt_FSet_Prop : forall P,
          FSet_elt_Prop P ->
          FSet_Prop P
      | Empty_FSet_Prop : forall (s : t),
          FSet_Prop (Empty s)
      | Subset_FSet_Prop : forall (s1 s2 : t),
          FSet_Prop (Subset s1 s2)
      | Equal_FSet_Prop : forall (s1 s2 : t),
          FSet_Prop (Equal s1 s2).

      Lemma eq_refl_iff (x : elt) : oeq x x <-> True.
      Proof. now split. Qed.

      Lemma dec_In : forall x (s : t),
          decidable (In x s).
      Proof.
        red; intros; generalize (mem_iff s x); case (mem x s); intuition.
      Qed.

      Lemma dec_eq : forall (x y : elt),
          decidable (oeq x y).
      Proof.
        red; intros x y; destruct (OrderedTypeLemmas.eq_dec x y); auto.
      Qed.

    End FSetDecideAuxiliary.

    Global Hint Constructors FSet_elt_Prop FSet_Prop : FSet_Prop.

    Ltac discard_nonFSet :=
      repeat (
        match goal with
        | t : fsetType ?elt, H : context [ @Logic.eq ?T ?x ?y ] |- _ =>
          tryif (change T with elt in H) then fail
          else tryif (change T with t in H) then fail
          else clear H
        | t : fsetType ?elt, H : ?P |- _ =>
          tryif prop (FSet_Prop (t:=t) P) holds by
            (auto 100 with FSet_Prop)
          then fail
          else clear H
        end).

    Global Hint Rewrite
           @empty_iff @singleton_iff @add_iff @remove_iff
           @union_iff @inter_iff @diff_iff
      : set_simpl.

    Global Hint Rewrite @eq_refl_iff : set_eq_simpl.
    Global Hint Resolve dec_In dec_eq : FSet_decidability.

    Ltac change_to_E_t :=
      repeat (
        match goal with
        | t : fsetType ?elt, H : ?T |- _ =>
          progress (change T with elt in H);
          repeat (
            match goal with
            | J : _ |- _ => progress (change T with elt in J)
            | |- _ => progress (change T with elt)
            end )
        | t :fsetType ?elt, H : forall x : ?T, _ |- _ =>
          progress (change T with elt in H);
          repeat (
            match goal with
            | J : _ |- _ => progress (change T with elt in J)
            | |- _ => progress (change T with elt)
            end )
        end).

    Ltac Logic_eq_to_E_eq :=
      repeat (
        match goal with
        | t : fsetType ?elt, H: _ |- _ =>
          progress (change (@Logic.eq elt) with oeq in H)
        | t : fsetType ?elt |- _ =>
          progress (change (@Logic.eq elt) with oeq)
        end).

    Ltac E_eq_to_Logic_eq :=
      repeat (
        match goal with
        | t : fsetType ?elt, H: _ |- _ =>
          progress (change oeq with (@Logic.eq elt) in H)
        | t : fsetType ?elt |- _ =>
          progress (change oeq with (@Logic.eq elt))
        end).

    Ltac substFSet :=
      repeat (
        match goal with
        | H: (?x == ?x)%OT |- _ => clear H
        | H: (?x == ?y)%OT |- _ => rewrite -> H in *; clear H
        | H: (oeq ?x ?x)%OT |- _ => clear H
        | H: (oeq ?x ?y)%OT |- _ => rewrite -> H in *; clear H
        end);
      autorewrite with set_eq_simpl in *.

    Ltac assert_decidability :=
      repeat (
        match goal with
        | H: context [~ oeq ?x ?y] |- _ =>
          assert new (oeq x y \/ ~ oeq x y) by (apply dec_eq)
        | H: context [~ (?x == ?y)%OT] |- _ =>
          assert new (oeq x y \/ ~ oeq x y) by (apply dec_eq)
        | H: context [~ In ?x ?s] |- _ =>
          assert new (In x s \/ ~ In x s) by (apply dec_In)
        | |- context [~ oeq ?x ?y] =>
          assert new (oeq x y \/ ~ oeq x y) by (apply dec_eq)
        | |- context [~ (?x == ?y)%OT] =>
          assert new (oeq x y \/ ~ oeq x y) by (apply dec_eq)
        | |- context [~ In ?x ?s] =>
          assert new (In x s \/ ~ In x s) by (apply dec_In)
        end);
      repeat (
        match goal with
        | _: ~ ?P, H : ?P \/ ~ ?P |- _ => clear H
        end).

    Ltac inst_FSet_hypotheses :=
      repeat (
        match goal with
        | t : fsetType ?elt, H : forall a : OrderedType.sort ?elt, _,
          _ : context [ In ?x _ ] |- _ =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        | t : fsetType ?elt, H : forall a : OrderedType.sort ?elt, _
          |- context [ In ?x _ ] =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        | t : fsetType ?elt, H : forall a : OrderedType.sort ?elt, _,
          _ : context [ oeq ?x _ ] |- _ =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        | t : fsetType ?elt, H : forall a : OrderedType.sort ?elt, _,
          _ : context [ (?x == _)%OT ] |- _ =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        | t : fsetType ?elt, H : forall a : OrderedType.sort ?elt, _
          |- context [ oeq ?x _ ] =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        | t : fsetType ?elt, H : forall a : OrderedType.sort ?elt, _
          |- context [ (?x == _)%OT ] =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        | t : fsetType ?elt, H : forall a : OrderedType.sort ?elt, _,
          _ : context [ oeq _ ?x ] |- _ =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        | t : fsetType ?elt, H : forall a : OrderedType.sort ?elt, _,
          _ : context [ (_ == ?x)%OT ] |- _ =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        | t : fsetType ?elt, H : forall a : OrderedType.sort ?elt, _
          |- context [ oeq _ ?x ] =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        | t : fsetType ?elt, H : forall a : OrderedType.sort ?elt, _
          |- context [ (_ == ?x)%OT ] =>
          let P := type of (H x) in
          assert new P by (exact (H x))
        end);
      repeat (
        match goal with
        | t : fsetType ?elt, H : forall a : OrderedType.sort ?elt, _ |- _ =>
          clear H
        end).

    Ltac fsetdec_rec := progress substFSet; intuition fsetdec_rec.

    Ltac fsetdec_body :=
      autorewrite with set_eq_simpl in *;
      inst_FSet_hypotheses;
      autorewrite with set_simpl set_eq_simpl in *;
      push not in * using FSet_decidability;
      substFSet;
      assert_decidability;
      auto;
      (intuition fsetdec_rec) ||
      fail 1
      "because the goal is beyond the scope of this tactic".

    Ltac fsetdec :=
      unfold iff in *;
      fold any not; intros;
      abstract_elements;
      no_logical_interdep;
      decompose records;
      discard_nonFSet;
      unfold Empty, Subset, Equal in *; intros;
      change_to_E_t; E_eq_to_Logic_eq; subst++; Logic_eq_to_E_eq;
      pull not using FSet_decidability;
      unfold not in *;
      match goal with
      | H: (In ?x ?r) -> False |- (In ?x ?s) -> False =>
          contradict H; fsetdec_body
      | H: (In ?x ?r) -> False |- (oeq ?x ?y) -> False =>
          contradict H; fsetdec_body
      | H: (In ?x ?r) -> False |- (?x == ?y)%OT -> False =>
          contradict H; fsetdec_body
      | H: (In ?x ?r) -> False |- (oeq ?y ?x) -> False =>
          contradict H; fsetdec_body
      | H: (In ?x ?r) -> False |- (?y == ?x)%OT -> False =>
          contradict H; fsetdec_body
      | t : fsetType ?elt, H: ?P -> False |- ?Q -> False =>
          tryif prop (FSet_elt_Prop (t:=t) P) holds by
            (auto 100 with FSet_Prop)
          then (contradict H; fsetdec_body)
          else fsetdec_body
      | |- _ =>
          fsetdec_body
      end.

    Module FSetDecideTestCases.

      Section FSetDecideTestCases.

        Context {elt : orderedType}.
        Context {t : fsetType elt}.

        Lemma test_eq_trans_1 : forall x y z (s : t),
            oeq x y ->
            ~ ~ oeq z y ->
            In x s ->
            In z s.
        Proof. fsetdec. Qed.

        Lemma test_eq_trans_2 : forall x y z (r s : t),
            In (t:=t) x (singleton y) ->
            ~ In z r ->
            ~ ~ In z (add y r) ->
            In x s ->
            In z s.
        Proof. fsetdec. Qed.

        Lemma test_eq_neq_trans_1 : forall w x y z (s : t),
            oeq x w ->
            ~ ~ oeq x y ->
            ~ oeq y z ->
            In w s ->
            In w (remove z s).
        Proof. fsetdec. Qed.

        Lemma test_eq_neq_trans_2 : forall w x y z (r1 r2 s : t),
            In (t:=t) x (singleton w) ->
            ~ In x r1 ->
            In x (add y r1) ->
            In y r2 ->
            In y (remove z r2) ->
            In w s ->
            In w (remove z s).
        Proof. fsetdec. Qed.

        Lemma test_In_singleton : forall x,
            In (t:=t) x (singleton x).
        Proof. fsetdec. Qed.

        Lemma test_add_In : forall x y (s : t),
            In x (add y s) ->
            ~ oeq x y ->
            In x s.
        Proof. fsetdec. Qed.

        Lemma test_Subset_add_remove : forall x (s : t),
            s [<=] (add x (remove x s)).
        Proof. fsetdec. Qed.

        Lemma test_eq_disjunction : forall w x y z,
            In (t:=t) w (add x (add y (singleton z))) ->
            oeq w x \/ oeq w y \/ oeq w z.
        Proof. fsetdec. Qed.

        Lemma test_not_In_disj : forall x y (s1 s2 s3 s4 : t),
            ~ In x (union s1 (union s2 (union s3 (add y s4)))) ->
            ~ (In x s1 \/ In x s4 \/ oeq y x).
        Proof. fsetdec. Qed.

        Lemma test_not_In_conj : forall x y (s1 s2 s3 s4 : t),
            ~ In x (union s1 (union s2 (union s3 (add y s4)))) ->
            ~ In x s1 /\ ~ In x s4 /\ ~ oeq y x.
        Proof. fsetdec. Qed.

        Lemma test_iff_conj : forall a x (s s' : t),
            (In a s' <-> oeq x a \/ In a s) ->
            (In a s' <-> In a (add x s)).
        Proof. fsetdec. Qed.

        Lemma test_set_ops_1 : forall x (q r s : t),
            (singleton x) [<=] s ->
            Empty (union q r) ->
            Empty (inter (diff s q) (diff s r)) ->
            ~ In x s.
        Proof. fsetdec. Qed.

        Lemma eq_chain_test : forall x1 x2 x3 x4 (s1 s2 s3 s4 : t),
            Empty s1 ->
            In x2 (add x1 s1) ->
            In x3 s2 ->
            ~ In x3 (remove x2 s2) ->
            ~ In x4 s3 ->
            In x4 (add x3 s3) ->
            In x1 s4 ->
            Subset (add x4 s4) s4.
        Proof. fsetdec. Qed.

        Lemma test_too_complex : forall x y z (r s : t),
            oeq x y ->
            (In (t:=t) x (singleton y) -> r [<=] s) ->
            In z r ->
            In z s.
        Proof.
          (** [fsetdec] is not intended to solve this directly. *)
          intros until s; intros Heq H Hr; lapply H; fsetdec.
        Qed.

        Lemma function_test_1 :
          forall (f : t -> t),
          forall (g : elt -> elt),
          forall (s1 s2 : t),
          forall (x1 x2 : elt),
            Equal s1 (f s2) ->
            oeq x1 (g (g x2)) ->
            In x1 s1 ->
            In (g (g x2)) (f s2).
        Proof. fsetdec. Qed.

        Lemma function_test_2 :
          forall (f : t -> t),
          forall (g : elt -> elt),
          forall (s1 s2 : t),
          forall (x1 x2 : elt),
            Equal s1 (f s2) ->
            oeq x1 (g x2) ->
            In x1 s1 ->
            g x2 = g (g x2) ->
            In (g (g x2)) (f s2).
        Proof.
          (** [fsetdec] is not intended to solve this directly. *)
          intros until 3. intros g_eq. rewrite <- g_eq. fsetdec.
        Qed.

        Lemma test_baydemir :
          forall (f : t -> t),
          forall (s : t),
          forall (x y : elt),
            In x (add y (f s)) ->
            ~ oeq x y ->
            In x (f s).
        Proof.
          fsetdec.
        Qed.

      End FSetDecideTestCases.

    End FSetDecideTestCases.

End FSetTypeDecide.

Export FSetTypeDecide.


(** * Lemmas from FSetProperties *)

Module FSetTypeWProperties.

  Local Open Scope fset_scope.

  Global Hint Unfold transpose compat_op Proper respectful : fset.
  Global Hint Extern 1 (Equivalence _) => constructor; congruence : fset.

  Section WProperties.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Lemma In_dec : forall x (s : t), {In x s} + {~ In x s}.
    Proof.
      intros; generalize (mem_iff s x); case (mem x s); intuition.
    Qed.

    Definition Add x (s s' : t) := forall y, In y s' <-> oeq x y \/ In y s.

    Lemma Add_Equal : forall x s s', Add x s s' <-> s' [=] add x s.
    Proof.
      unfold Add.
      split; intros.
      red; intros.
      rewrite H; clear H.
      fsetdec.
      fsetdec.
    Qed.

  End WProperties.

  Ltac expAdd := repeat rewrite -> Add_Equal.

  Section BasicProperties.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Variable s s' s'' s1 s2 s3 : t.
    Variable x x' : elt.

    Lemma Equal_refl : s[=]s.
    Proof. fsetdec. Qed.

    Lemma Equal_sym : s[=]s' -> s'[=]s.
    Proof. fsetdec. Qed.

    Lemma Equal_trans : s1[=]s2 -> s2[=]s3 -> s1[=]s3.
    Proof. fsetdec. Qed.

    Lemma Subset_refl : s[<=]s.
    Proof. fsetdec. Qed.

    Lemma Subset_trans : s1[<=]s2 -> s2[<=]s3 -> s1[<=]s3.
    Proof. fsetdec. Qed.

    Lemma Subset_antisym : s[<=]s' -> s'[<=]s -> s[=]s'.
    Proof. fsetdec. Qed.

    Lemma subset_equal : s[=]s' -> s[<=]s'.
    Proof. fsetdec. Qed.

    Lemma subset_empty : empty[<=]s.
    Proof. fsetdec. Qed.

    Lemma subset_remove_3 : s1[<=]s2 -> remove x s1 [<=] s2.
    Proof. fsetdec. Qed.

    Lemma subset_diff : s1[<=]s3 -> diff s1 s2 [<=] s3.
    Proof. fsetdec. Qed.

    Lemma subset_add_3 : In x s2 -> s1[<=]s2 -> add x s1 [<=] s2.
    Proof. fsetdec. Qed.

    Lemma subset_add_2 : s1[<=]s2 -> s1[<=] add x s2.
    Proof. fsetdec. Qed.

    Lemma in_subset : In x s1 -> s1[<=]s2 -> In x s2.
    Proof. fsetdec. Qed.

    Lemma double_inclusion : s1[=]s2 <-> s1[<=]s2 /\ s2[<=]s1.
    Proof. intuition fsetdec. Qed.

    Lemma empty_is_empty_1 : Empty s -> s[=]empty.
    Proof. fsetdec. Qed.

    Lemma empty_is_empty_2 : s[=]empty -> Empty s.
    Proof. fsetdec. Qed.

    Lemma add_Equal : In x s -> add x s [=] s.
    Proof. fsetdec. Qed.

    Lemma add_add : add x (add x' s) [=] add x' (add x s).
    Proof. fsetdec. Qed.

    Lemma remove_Equal : ~ In x s -> remove x s [=] s.
    Proof. fsetdec. Qed.

    Lemma Equal_remove : s[=]s' -> remove x s [=] remove x s'.
    Proof. fsetdec. Qed.

    Lemma add_remove : In x s -> add x (remove x s) [=] s.
    Proof. fsetdec. Qed.

    Lemma remove_add : ~In x s -> remove x (add x s) [=] s.
    Proof. fsetdec. Qed.

    Lemma singleton_equal_add : singleton x [=] add x (empty (t:=t)).
    Proof. fsetdec. Qed.

    Lemma remove_singleton_empty :
      In x s -> remove x s [=] empty -> singleton x [=] s.
    Proof. fsetdec. Qed.

    Lemma union_sym : union s s' [=] union s' s.
    Proof. fsetdec. Qed.

    Lemma union_Subset_Equal : s[<=]s' -> union s s' [=] s'.
    Proof. fsetdec. Qed.

    Lemma union_Equal_1 : s[=]s' -> union s s'' [=] union s' s''.
    Proof. fsetdec. Qed.

    Lemma union_Equal_2 : s'[=]s'' -> union s s' [=] union s s''.
    Proof. fsetdec. Qed.

    Lemma union_assoc : union (union s s') s'' [=] union s (union s' s'').
    Proof. fsetdec. Qed.

    Lemma add_union_singleton : add x s [=] union (singleton x) s.
    Proof. fsetdec. Qed.

    Lemma union_add : union (add x s) s' [=] add x (union s s').
    Proof. fsetdec. Qed.

    Lemma union_remove_add_1 :
      union (remove x s) (add x s') [=] union (add x s) (remove x s').
    Proof. fsetdec. Qed.

    Lemma union_remove_add_2 : In x s ->
                               union (remove x s) (add x s') [=] union s s'.
    Proof. fsetdec. Qed.

    Lemma union_Subset_1 : s [<=] union s s'.
    Proof. fsetdec. Qed.

    Lemma union_Subset_2 : s' [<=] union s s'.
    Proof. fsetdec. Qed.

    Lemma union_Subset_3 : s[<=]s'' -> s'[<=]s'' -> union s s' [<=] s''.
    Proof. fsetdec. Qed.

    Lemma union_Subset_4 : s[<=]s' -> union s s'' [<=] union s' s''.
    Proof. fsetdec. Qed.

    Lemma union_Subset_5 : s[<=]s' -> union s'' s [<=] union s'' s'.
    Proof. fsetdec. Qed.

    Lemma empty_union_1 : Empty s -> union s s' [=] s'.
    Proof. fsetdec. Qed.

    Lemma empty_union_2 : Empty s -> union s' s [=] s'.
    Proof. fsetdec. Qed.

    Lemma not_in_union : ~In x s -> ~In x s' -> ~In x (union s s').
    Proof. fsetdec. Qed.

    Lemma inter_sym : inter s s' [=] inter s' s.
    Proof. fsetdec. Qed.

    Lemma inter_Subset_Equal : s[<=]s' -> inter s s' [=] s.
    Proof. fsetdec. Qed.

    Lemma inter_Equal_1 : s[=]s' -> inter s s'' [=] inter s' s''.
    Proof. fsetdec. Qed.

    Lemma inter_Equal_2 : s'[=]s'' -> inter s s' [=] inter s s''.
    Proof. fsetdec. Qed.

    Lemma inter_assoc : inter (inter s s') s'' [=] inter s (inter s' s'').
    Proof. fsetdec. Qed.

    Lemma union_inter_1 : inter (union s s') s'' [=] union (inter s s'') (inter s' s'').
    Proof. fsetdec. Qed.

    Lemma union_inter_2 : union (inter s s') s'' [=] inter (union s s'') (union s' s'').
    Proof. fsetdec. Qed.

    Lemma inter_add_1 : In x s' -> inter (add x s) s' [=] add x (inter s s').
    Proof. fsetdec. Qed.

    Lemma inter_add_2 : ~ In x s' -> inter (add x s) s' [=] inter s s'.
    Proof. fsetdec. Qed.

    Lemma empty_inter_1 : Empty s -> Empty (inter s s').
    Proof. fsetdec. Qed.

    Lemma empty_inter_2 : Empty s' -> Empty (inter s s').
    Proof. fsetdec. Qed.

    Lemma inter_Subset_1 : inter s s' [<=] s.
    Proof. fsetdec. Qed.

    Lemma inter_Subset_2 : inter s s' [<=] s'.
    Proof. fsetdec. Qed.

    Lemma inter_Subset_3 :
      s''[<=]s -> s''[<=]s' -> s''[<=] inter s s'.
    Proof. fsetdec. Qed.

    Lemma empty_diff_1 : Empty s -> Empty (diff s s').
    Proof. fsetdec. Qed.

    Lemma empty_diff_2 : Empty s -> diff s' s [=] s'.
    Proof. fsetdec. Qed.

    Lemma diff_Subset : diff s s' [<=] s.
    Proof. fsetdec. Qed.

    Lemma diff_Subset_Equal : s[<=]s' -> diff s s' [=] empty.
    Proof. fsetdec. Qed.

    Lemma remove_diff_singleton :
      remove x s [=] diff s (singleton x).
    Proof. fsetdec. Qed.

    Lemma diff_inter_empty : inter (diff s s') (inter s s') [=] empty.
    Proof. fsetdec. Qed.

    Lemma diff_inter_all : union (diff s s') (inter s s') [=] s.
    Proof. fsetdec. Qed.

    Lemma Add_add : Add x s (add x s).
    Proof. expAdd; fsetdec. Qed.

    Lemma Add_remove : In x s -> Add x (remove x s) s.
    Proof. expAdd; fsetdec. Qed.

    Lemma union_Add : Add x s s' -> Add x (union s s'') (union s' s'').
    Proof. expAdd; fsetdec. Qed.

    Lemma inter_Add :
      In x s'' -> Add x s s' -> Add x (inter s s'') (inter s' s'').
    Proof. expAdd; fsetdec. Qed.

    Lemma union_Equal :
      In x s'' -> Add x s s' -> union s s'' [=] union s' s''.
    Proof. expAdd; fsetdec. Qed.

    Lemma inter_Add_2 :
      ~In x s'' -> Add x s s' -> inter s s'' [=] inter s' s''.
    Proof. expAdd; fsetdec. Qed.

  End BasicProperties.

  Global Hint Immediate Equal_sym add_remove remove_add union_sym inter_sym: set.
  Global Hint Resolve Equal_refl Equal_trans Subset_refl subset_equal Subset_antisym
         Subset_trans subset_empty subset_remove_3 subset_diff subset_add_3
         subset_add_2 in_subset empty_is_empty_1 empty_is_empty_2 add_Equal
         remove_Equal singleton_equal_add union_Subset_Equal union_Equal_1
         union_Equal_2 union_assoc add_union_singleton union_add union_Subset_1
         union_Subset_2 union_Subset_3 inter_Subset_Equal inter_Equal_1 inter_Equal_2
         inter_assoc union_inter_1 union_inter_2 inter_add_1 inter_add_2
         empty_inter_1 empty_inter_2 empty_union_1 empty_union_2 empty_diff_1
         empty_diff_2 union_Add inter_Add union_Equal inter_Add_2 not_in_union
         inter_Subset_1 inter_Subset_2 inter_Subset_3 diff_Subset diff_Subset_Equal
         remove_diff_singleton diff_inter_empty diff_inter_all Add_add Add_remove
         Equal_remove add_add : set.

  Section Properties.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Lemma elements_Empty : forall (s : t), Empty s <-> elements s = nil.
    Proof.
      intros.
      unfold Empty.
      split; intros.
      assert (forall a, ~ List.In a (elements s)).
      red; intros.
      apply (H a).
      rewrite elements_iff.
      rewrite InA_alt; exists a; split; auto with ordered_type.
      destruct (elements s); auto.
      elim (H0 s0); simpl; auto.
      red; intros.
      rewrite elements_iff in H0.
      rewrite InA_alt in H0; destruct H0.
      rewrite H in H0; destruct H0 as (_,H0); inversion H0.
    Qed.

    Lemma elements_empty : elements (t:=t) empty = nil.
    Proof.
      rewrite <- elements_Empty; auto with set.
    Qed.

    Definition of_list (l : list elt) := List.fold_right add (empty (t:=t)) l.

    Definition to_list := elements (t:=t).

    Lemma of_list_1 : forall l x, In x (of_list l) <-> InA oeq x l.
    Proof.
      induction l; simpl; intro x.
      rewrite -> empty_iff, InA_nil. intuition.
      rewrite -> add_iff, InA_cons, IHl. intuition.
    Qed.

    Lemma of_list_2 : forall l, equivlistA oeq (to_list (of_list l)) l.
    Proof.
      unfold to_list; red; intros.
      rewrite <- elements_iff; apply of_list_1.
    Qed.

    Lemma of_list_3 : forall s, of_list (to_list s) [=] s.
    Proof.
      unfold to_list; red; intros.
      rewrite of_list_1; symmetry; apply elements_iff.
    Qed.

    Section Fold.

      Lemma fold_spec_right (s:t) (A:Type) (i:A) (f : elt -> A -> A) :
        fold f s i = List.fold_right f i (List.rev (elements s)).
      Proof.
        rewrite fold_1. symmetry. apply fold_left_rev_right.
      Qed.

      Notation NoDup := (NoDupA oeq).
      Notation InA := (InA oeq).

      Theorem fold_rec :
        forall (A:Type) (P : t -> A -> Type) (f : elt -> A -> A) (i:A) (s:t),
          (forall s', Empty s' -> P s' i) ->
          (forall x a s' s'', In x s -> ~In x s' -> Add x s' s'' ->
                              P s' a -> P s'' (f x a)) ->
          P s (fold f s i).
      Proof.
        intros A P f i s Pempty Pstep.
        rewrite fold_spec_right. set (l:=List.rev (elements s)).
        assert (Pstep' : forall x a s' s'', InA x l -> ~In x s' -> Add x s' s'' ->
                                            P s' a -> P s'' (f x a)).
        intros; eapply Pstep; eauto.
        rewrite -> elements_iff, <- InA_rev; auto.
        assert (Hdup : NoDup l);
          first unfold l; eauto using elements_3w, NoDupA_rev with *.
        assert (Hsame : forall x, In x s <-> InA x l) by
          (unfold l; intros; rewrite -> elements_iff, InA_rev; intuition).
        clear Pstep; clearbody l; revert s Hsame; induction l.
        (* empty *)
        intros s Hsame; simpl.
        apply Pempty. intro x. rewrite -> Hsame, InA_nil; intuition.
        (* step *)
        intros s Hsame; simpl.
        apply Pstep' with (of_list l); auto with *.
        inversion_clear Hdup; rewrite of_list_1; auto.
        red. intros. rewrite -> Hsame, of_list_1, InA_cons; intuition.
        apply IHl.
        intros; eapply Pstep'; eauto.
        inversion_clear Hdup; auto.
        exact (of_list_1 l).
      Qed.

      Theorem fold_rec_bis :
        forall (A:Type) (P : t -> A -> Type) (f : elt -> A -> A) (i:A) (s:t),
          (forall s s' a, s[=]s' -> P s a -> P s' a) ->
          (P empty i) ->
          (forall x a s', In x s -> ~In x s' -> P s' a -> P (add x s') (f x a)) ->
          P s (fold f s i).
      Proof.
        intros A P f i s Pmorphism Pempty Pstep.
        apply fold_rec; intros.
        apply Pmorphism with empty; auto with set.
        rewrite -> Add_Equal in H1; auto with set.
        apply Pmorphism with (add x s'); auto with set.
      Qed.

      Lemma fold_rec_nodep :
        forall (A:Type) (P : A -> Type) (f : elt -> A -> A) (i:A) (s:t),
          P i -> (forall x a, In x s -> P a -> P (f x a)) ->
          P (fold f s i).
      Proof.
        intros; apply fold_rec_bis with (P:=fun _ => P); auto.
      Qed.

      Lemma fold_rec_weak :
        forall (A:Type) (P : t -> A -> Type) (f : elt -> A -> A) (i:A),
          (forall s s' a, s[=]s' -> P s a -> P s' a) ->
          P empty i ->
          (forall x a s, ~In x s -> P s a -> P (add x s) (f x a)) ->
          forall s, P s (fold f s i).
      Proof.
        intros; apply fold_rec_bis; auto.
      Qed.

      Lemma fold_rel :
        forall (A B:Type) (R : A -> B -> Type)
               (f : elt -> A -> A) (g : elt -> B -> B) (i : A) (j : B) (s : t),
          R i j ->
          (forall x a b, In x s -> R a b -> R (f x a) (g x b)) ->
          R (fold f s i) (fold g s j).
      Proof.
        intros A B R f g i j s Rempty Rstep.
        rewrite -> 2 fold_spec_right. set (l:=List.rev (elements s)).
        assert (Rstep' : forall x a b, InA x l -> R a b -> R (f x a) (g x b)) by
          (intros; apply Rstep; auto; rewrite -> elements_iff, <- InA_rev; auto).
        clearbody l; clear Rstep s.
        induction l; simpl; auto with *.
      Qed.

      Lemma set_induction :
        forall P : t -> Type,
          (forall s, Empty s -> P s) ->
          (forall s s', P s -> forall x, ~In x s -> Add x s s' -> P s') ->
          forall s, P s.
      Proof.
        intros. apply (@fold_rec _ (fun s _ => P s) (fun _ _ => tt) tt s); eauto.
      Qed.

      Lemma set_induction_bis :
        forall P : t -> Type,
          (forall s s', s [=] s' -> P s -> P s') ->
          P empty ->
          (forall x s, ~In x s -> P s -> P (add x s)) ->
          forall s, P s.
      Proof.
        intros.
        apply (@fold_rec_bis _ (fun s _ => P s) (fun _ _ => tt) tt s); eauto.
      Qed.

      Lemma fold_identity : forall (s : t), fold add s empty [=] s.
      Proof.
        intros.
        apply fold_rec with (P:=fun s acc => acc[=]s); auto with set.
        intros. rewrite H2; rewrite Add_Equal in H1; auto with set.
      Qed.

      Lemma fold_0 :
        forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
        exists l : list elt,
          NoDup l /\
            (forall x : elt, In x s <-> InA x l) /\
            fold f s i = fold_right f i l.
      Proof.
        intros; exists (List.rev (elements s)); split.
        apply NoDupA_rev. auto with typeclass_instances. auto with set.
        split; intros.
        rewrite elements_iff; do 2 rewrite InA_alt.
        split; destruct 1; generalize (List.In_rev (elements s) x0); exists x0; intuition.
        apply fold_spec_right.
      Qed.

      Lemma fold_1 :
        forall (s : t) (A : Type) (eqA : A -> A -> Prop)
               (st : Equivalence eqA) (i : A) (f : elt -> A -> A),
          Empty s -> eqA (fold f s i) i.
      Proof.
        unfold Empty; intros; destruct (fold_0 s i f) as (l,(H1, (H2, H3))).
        rewrite H3; clear H3.
        generalize H H2; clear H H2; case l; simpl; intros.
        reflexivity.
        elim (H s0).
        elim (H2 s0); intuition.
      Qed.

      Lemma fold_2 :
        forall (s s' : t) x (A : Type) (eqA : A -> A -> Prop)
               (st : Equivalence eqA) (i : A) (f : elt -> A -> A),
          compat_op oeq eqA f ->
          transpose eqA f ->
          ~ In x s -> Add x s s' -> eqA (fold f s' i) (f x (fold f s i)).
      Proof.
        intros; destruct (fold_0 s i f) as (l,(Hl, (Hl1, Hl2)));
          destruct (fold_0 s' i f) as (l',(Hl', (Hl'1, Hl'2))).
        rewrite Hl2; rewrite Hl'2; clear Hl2 Hl'2.
        apply fold_right_add with (eqA:=oeq)(eqB:=eqA). auto with typeclass_instances. 1-5: auto.
        rewrite <- Hl1; auto.
        intros a; rewrite InA_cons; rewrite <- Hl1; rewrite <- Hl'1;
          rewrite (H2 a); intuition.
      Qed.

      Lemma fold_1b :
        forall (s : t) (A : Type)(i : A) (f : elt -> A -> A),
          Empty s -> (fold f s i) = i.
      Proof.
        intros.
        rewrite FSetType.Exports.fold_1.
        rewrite elements_Empty in H; rewrite H; simpl; auto.
      Qed.

      Section Fold_More.

        Variables (A:Type) (eqA:A->A->Prop) (st:Equivalence eqA).
        Variables (f:elt->A->A) (Comp:compat_op oeq eqA f) (Ass:transpose eqA f).

        Lemma fold_commutes : forall i (s : t) x,
            eqA (fold f s (f x i)) (f x (fold f s i)).
        Proof.
          intros.
          apply fold_rel with (R:=fun u v => eqA u (f x v)); intros.
          reflexivity.
          transitivity (f x0 (f x b)); auto. apply Comp; auto with *.
        Qed.

        Lemma fold_init : forall i i' (s : t), eqA i i' ->
                                               eqA (fold f s i) (fold f s i').
        Proof.
          intros. apply fold_rel with (R:=eqA); auto.
          intros; apply Comp; auto with *.
        Qed.

        Lemma fold_Equal :
          forall i (s s' : t), s[=]s' -> eqA (fold f s i) (fold f s' i).
        Proof.
          intros i s; pattern s; apply set_induction; clear s; intros.
          transitivity i.
          apply fold_1; auto.
          symmetry; apply fold_1; auto.
          rewrite <- H0; auto.
          transitivity (f x (fold f s i)).
          apply fold_2 with (eqA := eqA); auto.
          symmetry; apply fold_2 with (eqA := eqA); auto.
          unfold Add in *; intros.
          rewrite <- H2; auto.
        Qed.

        Lemma fold_empty : forall i, fold (t:=t) f empty i = i.
        Proof.
          intros i; apply fold_1b; auto with set.
        Qed.

        Lemma fold_add : forall i (s : t) x, ~In x s ->
                                             eqA (fold f (add x s) i) (f x (fold f s i)).
        Proof.
          intros; apply fold_2 with (eqA := eqA); auto with set.
        Qed.

        Lemma add_fold : forall i (s : t) x, In x s ->
                                             eqA (fold f (add x s) i) (fold f s i).
        Proof.
          intros; apply fold_Equal; auto with set.
        Qed.

        Lemma remove_fold_1: forall i (s : t) x, In x s ->
                                                 eqA (f x (fold f (remove x s) i)) (fold f s i).
        Proof.
          intros.
          symmetry.
          apply fold_2 with (eqA:=eqA); auto with *.
        Qed.

        Lemma remove_fold_2: forall i (s : t) x, ~In x s ->
                                                 eqA (fold f (remove x s) i) (fold f s i).
        Proof.
          intros.
          apply fold_Equal; auto with set.
        Qed.

        Lemma fold_union_inter : forall i (s s' : t),
            eqA (fold f (union s s') (fold f (inter s s') i))
                (fold f s (fold f s' i)).
        Proof.
          intros; pattern s; apply set_induction; clear s; intros.
          transitivity (fold f s' (fold f (inter s s') i)).
          apply fold_Equal; auto with set.
          transitivity (fold f s' i).
          apply fold_init; auto.
          apply fold_1; auto with set.
          symmetry; apply fold_1; auto.
          rename s'0 into s''.
          destruct (In_dec x s').
          (* In x s' *)
          transitivity (fold f (union s'' s') (f x (fold f (inter s s') i))); auto with set.
          apply fold_init; auto.
          apply fold_2 with (eqA:=eqA); auto with set.
          rewrite inter_iff; intuition.
          transitivity (f x (fold f s (fold f s' i))).
          transitivity (fold f (union s s') (f x (fold f (inter s s') i))).
          apply fold_Equal; auto.
          apply Equal_sym; apply union_Equal with x; auto with set.
          transitivity (f x (fold f (union s s') (fold f (inter s s') i))).
          apply fold_commutes; auto.
          apply Comp; auto with *.
          symmetry; apply fold_2 with (eqA:=eqA); auto.
          (* ~(In x s') *)
          transitivity (f x (fold f (union s s') (fold f (inter s'' s') i))).
          apply fold_2 with (eqA:=eqA); auto with set.
          transitivity (f x (fold f (union s s') (fold f (inter s s') i))).
          apply Comp;auto with *.
          apply fold_init;auto.
          apply fold_Equal;auto.
          apply Equal_sym; apply inter_Add_2 with x; auto with set.
          transitivity (f x (fold f s (fold f s' i))).
          apply Comp; auto with *.
          symmetry; apply fold_2 with (eqA:=eqA); auto.
        Qed.

        Lemma fold_diff_inter : forall i (s s' : t),
            eqA (fold f (diff s s') (fold f (inter s s') i)) (fold f s i).
        Proof.
          intros.
          transitivity (fold f (union (diff s s') (inter s s'))
                             (fold f (inter (diff s s') (inter s s')) i)).
          symmetry; apply fold_union_inter; auto.
          transitivity (fold f s (fold f (inter (diff s s') (inter s s')) i)).
          apply fold_Equal; auto with set.
          apply fold_init; auto.
          apply fold_1; auto with set.
        Qed.

        Lemma fold_union: forall i (s s' : t),
            (forall x, ~(In x s/\In x s')) ->
            eqA (fold f (union s s') i) (fold f s (fold f s' i)).
        Proof.
          intros.
          transitivity (fold f (union s s') (fold f (inter s s') i)).
          apply fold_init; auto.
          symmetry; apply fold_1; auto with set.
          unfold Empty; intro a; generalize (H a); set_iff; tauto.
          apply fold_union_inter; auto.
        Qed.

      End Fold_More.

      Lemma fold_plus :
        forall (s : t) p, fold (fun _ => S) s p = fold (fun _ => S) s 0 + p.
      Proof.
        intros. apply fold_rel with (R:=fun u v => u = v + p); simpl; auto.
        intros. rewrite -(addn1 a) -(addn1 b). rewrite H0. ring.
      Qed.

    End Fold.

    Lemma cardinal_fold : forall (s : t), cardinal s = fold (fun _ => S) s 0.
    Proof.
      intros; rewrite cardinal_1; rewrite FSetType.Exports.fold_1; auto with *.
      symmetry; apply fold_left_length; auto.
    Qed.

    Lemma cardinal_0 :
      forall (s : t), exists l : list elt,
        NoDupA oeq l /\
          (forall x : elt, In x s <-> InA oeq x l) /\
          cardinal s = length l.
    Proof.
      intros; exists (elements s); intuition; apply cardinal_1.
    Qed.

    Lemma cardinal_1 : forall (s : t), Empty s -> cardinal s = 0.
    Proof.
      intros; rewrite cardinal_fold; apply fold_1; auto with fset.
    Qed.

    Lemma cardinal_2 :
      forall (s s' : t) x, ~ In x s -> Add x s s' -> cardinal s' = S (cardinal s).
    Proof.
      intros; do 2 rewrite cardinal_fold.
      change S with ((fun _ => S) x).
      apply fold_2; auto with fset.
    Qed.

    Lemma cardinal_Empty : forall (s : t), Empty s <-> cardinal s = 0.
    Proof.
      intros.
      rewrite -> elements_Empty, FSetType.Exports.cardinal_1.
      destruct (elements s); intuition; discriminate.
    Qed.

    Lemma cardinal_inv_1 : forall (s : t), cardinal s = 0 -> Empty s.
    Proof.
      intros; rewrite cardinal_Empty; auto.
    Qed.

  End Properties.

  Global Hint Resolve cardinal_inv_1 : fset.

  Section Properties.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Lemma cardinal_inv_2 :
      forall (s : t) n, cardinal s = S n -> { x : elt | In x s }.
    Proof.
      intros; rewrite FSetType.Exports.cardinal_1 in H.
      generalize (elements_2 (s:=s)).
      destruct (elements s); try discriminate.
      exists s0; auto with *.
    Qed.

    Lemma cardinal_inv_2b :
      forall (s : t), cardinal s <> 0 -> { x : elt | In x s }.
    Proof.
      intro; generalize (@cardinal_inv_2 s); destruct cardinal;
        [intuition|eauto].
    Qed.

    Lemma Equal_cardinal : forall (s s' : t), s[=]s' -> cardinal s = cardinal s'.
    Proof.
      symmetry.
      remember (cardinal s) as n; symmetry in Heqn; revert s s' Heqn H.
      induction n; intros.
      apply cardinal_1; rewrite <- H; auto with fset.
      destruct (cardinal_inv_2 Heqn) as (x,H2).
      revert Heqn.
      rewrite (cardinal_2 (s:=remove x s) (s':=s) (x:=x)); auto with *.
      rewrite (cardinal_2 (s:=remove x s') (s':=s') (x:=x)); eauto with *.
    Qed.

    Global Add Morphism cardinal with signature (Equal (t:=t) ==> Logic.eq) as cardinal_m.
    Proof.
      exact Equal_cardinal.
    Qed.

    Lemma empty_cardinal : cardinal (t:=t) empty = 0.
    Proof.
      rewrite cardinal_fold; apply fold_1; auto with set fset.
    Qed.

  End Properties.

  Global Hint Resolve Add_add Add_remove Equal_remove cardinal_inv_1 Equal_cardinal : fset.

  Global Hint Immediate empty_cardinal cardinal_1 : set.

  Section Properties.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Lemma singleton_cardinal : forall x, cardinal (t:=t) (singleton x) = 1.
    Proof.
      intros.
      rewrite (singleton_equal_add x).
      replace 0 with (cardinal (t:=t) empty); auto with *.
      apply cardinal_2 with x; auto with set fset.
      fsetdec.
    Qed.

  End Properties.

  Global Hint Resolve singleton_cardinal: set.

  Section Properties.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Lemma diff_inter_cardinal :
      forall (s s' : t), cardinal (diff s s') + cardinal (inter s s') = cardinal s .
    Proof.
      intros; do 3 rewrite cardinal_fold.
      rewrite <- fold_plus.
      apply fold_diff_inter with (eqA:=@Logic.eq nat); auto with fset.
    Qed.

    Lemma union_cardinal:
      forall (s s' : t), (forall x, ~(In x s/\In x s')) ->
                         cardinal (union s s')=cardinal s+cardinal s'.
    Proof.
      intros; do 3 rewrite cardinal_fold.
      rewrite <- fold_plus.
      apply fold_union; auto with fset.
    Qed.

    Lemma subset_cardinal :
      forall (s s' : t), s[<=]s' -> cardinal s <= cardinal s' .
    Proof.
      intros.
      rewrite <- (diff_inter_cardinal s' s).
      rewrite (inter_sym s' s).
      rewrite (inter_Subset_Equal H).
      exact: leq_addl.
    Qed.

    Lemma subset_cardinal_lt :
      forall (s s' : t) x, s[<=]s' -> In x s' -> ~In x s -> cardinal s < cardinal s'.
    Proof.
      intros.
      rewrite <- (diff_inter_cardinal s' s).
      rewrite (inter_sym s' s).
      rewrite (inter_Subset_Equal H).
      generalize (@cardinal_inv_1 _ _ (diff s' s)).
      destruct (cardinal (diff s' s)).
      intro H2; destruct (H2 Logic.eq_refl x).
      set_iff; auto.
      intros _.
      change (0 + cardinal s < S n + cardinal s).
      rewrite ltn_add2r. done.
    Qed.

    Theorem union_inter_cardinal :
      forall (s s' : t),
        cardinal (union s s') + cardinal (inter s s')  = cardinal s  + cardinal s' .
    Proof.
      intros.
      do 4 rewrite cardinal_fold.
      do 2 rewrite <- fold_plus.
      apply fold_union_inter with (eqA:=@Logic.eq nat); auto with fset.
    Qed.

    Lemma union_cardinal_inter :
      forall (s s' : t),
        cardinal (union s s') = cardinal s + cardinal s' - cardinal (inter s s').
    Proof.
      intros.
      rewrite <- union_inter_cardinal, Nat.add_sub.
      reflexivity.
    Qed.

    Lemma union_cardinal_le :
      forall (s s' : t), cardinal (union s s') <= cardinal s  + cardinal s'.
    Proof.
      intros; generalize (union_inter_cardinal s s').
      intros; rewrite <- H. exact: leq_addr.
    Qed.

    Lemma add_cardinal_1 :
      forall (s : t) x, In x s -> cardinal (add x s) = cardinal s.
    Proof.
      auto with set fset.
    Qed.

    Lemma add_cardinal_2 :
      forall (s : t) x, ~In x s -> cardinal (add x s) = S (cardinal s).
    Proof.
      intros.
      do 2 rewrite cardinal_fold.
      change S with ((fun _ => S) x);
        apply fold_add with (eqA:=@Logic.eq nat); auto with fset.
    Qed.

    Lemma remove_cardinal_1 :
      forall (s : t) x, In x s -> S (cardinal (remove x s)) = cardinal s.
    Proof.
      intros.
      do 2 rewrite cardinal_fold.
      change S with ((fun _ =>S) x).
      apply remove_fold_1 with (eqA:=@Logic.eq nat); auto with fset.
    Qed.

    Lemma remove_cardinal_2 :
      forall (s : t) x, ~In x s -> cardinal (remove x s) = cardinal s.
    Proof.
      auto with set fset.
    Qed.

  End Properties.

  Global Hint Resolve subset_cardinal union_cardinal add_cardinal_1 add_cardinal_2 : fset.

End FSetTypeWProperties.

Export FSetTypeWProperties.


Module FSetTypeOrdProperties.

  Local Open Scope fset_scope.

  Import FSetTypeWProperties.

  Section OrdProperties.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Lemma sort_equivlistA_eqlistA : forall l l' : list elt,
        sort olt l -> sort olt l' -> equivlistA oeq l l' -> eqlistA oeq l l'.
    Proof.
      apply SortA_equivlistA_eqlistA; auto with typeclass_instances.
    Qed.

    Definition gtb (x y : elt) := match OrderedType.Exports.compare x y with GT _ => true | _ => false end.
    Definition leb x := fun y => negb (gtb x y).

    Definition elements_lt x (s : t) := List.filter (gtb x) (elements s).
    Definition elements_ge x (s : t) := List.filter (leb x) (elements s).

    Lemma gtb_1 : forall x y, gtb x y = true <-> olt y x.
    Proof.
      intros; unfold gtb; destruct (OrderedType.Exports.compare x y); intuition; try discriminate; order.
    Qed.

    Lemma leb_1 : forall x y, leb x y = true <-> ~olt y x.
    Proof.
      intros; unfold leb, gtb; destruct (OrderedType.Exports.compare x y); intuition; try discriminate; order.
    Qed.

    Lemma gtb_compat : forall x, Proper (oeq==>Logic.eq) (gtb x).
    Proof.
      red; intros x a b H.
      generalize (gtb_1 x a)(gtb_1 x b); destruct (gtb x a); destruct (gtb x b); auto.
      intros.
      symmetry; rewrite H1.
      apply eq_lt with a; auto with ordered_type.
      rewrite <- H0; auto.
      intros.
      rewrite H0.
      apply eq_lt with b; auto.
      rewrite <- H1; auto.
    Qed.

    Lemma leb_compat : forall x, Proper (oeq==>Logic.eq) (leb x).
    Proof.
      red; intros x a b H; unfold leb.
      f_equal; apply gtb_compat; auto.
    Qed.

  End OrdProperties.

  Global Hint Resolve gtb_compat leb_compat : fset.

  Section OrdProperties.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Lemma elements_split : forall x (s : t),
        elements s = elements_lt x s ++ elements_ge x s.
    Proof.
      unfold elements_lt, elements_ge, leb; intros.
      eapply (@filter_split _ oeq _ olt). 1-2: auto with typeclass_instances. 2: auto with set.
      intros.
      rewrite gtb_1 in H.
      assert (~olt y x).
      unfold gtb in *; destruct (OrderedType.Exports.compare x y); intuition;
        try discriminate; order.
      order.
    Qed.

    Lemma elements_Add : forall (s s' : t) x,
        ~In x s -> Add x s s' ->
        eqlistA oeq (elements s') (elements_lt x s ++ x :: elements_ge x s).
    Proof.
      intros; unfold elements_ge, elements_lt.
      apply sort_equivlistA_eqlistA; auto with set.
      apply (@SortA_app _ oeq). auto with typeclass_instances.
      apply (@filter_sort _ oeq). 1-3: auto with typeclass_instances. auto with set.
      constructor; auto.
      apply (@filter_sort _ oeq). 1-3: auto with typeclass_instances. auto with set.
      rewrite -> Inf_alt by (apply (@filter_sort _ oeq); auto with set typeclass_instances).
      intros.
      rewrite -> filter_InA in H1 by auto with fset. destruct H1.
      rewrite leb_1 in H2.
      rewrite <- elements_iff in H1.
      assert (~oeq x y).
      contradict H; rewrite H; auto.
      order.
      intros.
      rewrite -> filter_InA in H1 by auto with fset. destruct H1.
      rewrite gtb_1 in H3.
      inversion_clear H2.
      order.
      rewrite -> filter_InA in H4 by auto with fset. destruct H4.
      rewrite leb_1 in H4.
      order.
      red; intros a.
      rewrite -> InA_app_iff, InA_cons, !filter_InA, <-elements_iff,
        leb_1, gtb_1, (H0 a) by auto with fset.
      intuition.
      destruct (OrderedType.Exports.compare a x); intuition.
      fold (~olt a x); auto with ordered_type set.
    Qed.

    Definition Above x (s : t) := forall y, In y s -> olt y x.
    Definition Below x (s : t) := forall y, In y s -> olt x y.

    Lemma elements_Add_Above : forall (s s' : t) x,
        Above x s -> Add x s s' ->
        eqlistA oeq (elements s') (elements s ++ x::nil).
    Proof.
      intros.
      apply sort_equivlistA_eqlistA. auto with set.
      apply (@SortA_app _ oeq). auto with typeclass_instances. auto with set. auto.
      intros.
      inversion_clear H2.
      rewrite <- elements_iff in H1.
      apply lt_eq with x; auto with ordered_type.
      inversion H3.
      red; intros a.
      rewrite -> InA_app_iff, InA_cons, InA_nil.
      do 2 rewrite <- elements_iff; rewrite (H0 a); intuition.
    Qed.

    Lemma elements_Add_Below : forall (s s' : t) x,
        Below x s -> Add x s s' ->
        eqlistA oeq (elements s') (x::elements s).
    Proof.
      intros.
      apply sort_equivlistA_eqlistA. auto with set.
      change (sort olt ((x::nil) ++ elements s)).
      apply (@SortA_app _ oeq). auto with typeclass_instances. auto. auto with set.
      intros.
      inversion_clear H1.
      rewrite <- elements_iff in H2.
      apply eq_lt with x; auto.
      inversion H3.
      red; intros a.
      rewrite InA_cons.
      do 2 rewrite <- elements_iff; rewrite (H0 a); intuition.
    Qed.

    Lemma set_induction_max :
      forall P : t -> Type,
        (forall s : t, Empty s -> P s) ->
        (forall s s', P s -> forall x, Above x s -> Add x s s' -> P s') ->
        forall s : t, P s.
    Proof.
      intros; remember (cardinal s) as n; revert s Heqn; induction n; intros; auto with fset.
      case_eq (max_elt s); intros.
      apply X0 with (remove s0 s) s0; auto with set.
      apply IHn.
      assert (S n = S (cardinal (remove s0 s))).
      rewrite Heqn; apply cardinal_2 with s0; auto with set ordered_type.
      inversion H0; auto.
      red; intros.
      rewrite remove_iff in H0; destruct H0.
      generalize (@max_elt_2 _ _ s s0 y H H0); order.

      assert (H0:=max_elt_3 H).
      rewrite -> cardinal_Empty in H0; rewrite H0 in Heqn; inversion Heqn.
    Qed.

    Lemma set_induction_min :
      forall P : t -> Type,
        (forall s : t, Empty s -> P s) ->
        (forall s s', P s -> forall x, Below x s -> Add x s s' -> P s') ->
        forall s : t, P s.
    Proof.
      intros; remember (cardinal s) as n; revert s Heqn; induction n; intros; auto with fset.
      case_eq (min_elt s); intros.
      apply X0 with (remove s0 s) s0; auto with set.
      apply IHn.
      assert (S n = S (cardinal (remove s0 s))).
      rewrite Heqn; apply cardinal_2 with s0; auto with set ordered_type.
      inversion H0; auto.
      red; intros.
      rewrite remove_iff in H0; destruct H0.
      generalize (@min_elt_2 _ _ s s0 y H H0); order.

      assert (H0:=min_elt_3 H).
      rewrite -> cardinal_Empty in H0; auto; rewrite H0 in Heqn; inversion Heqn.
    Qed.

    Lemma fold_3 :
      forall s s' x (A : Type) (eqA : A -> A -> Prop)
             (st : Equivalence eqA) (i : A) (f : elt -> A -> A),
        compat_op oeq eqA f ->
        Above x s -> Add x s s' -> eqA (fold f s' i) (f x (fold f s i)).
    Proof.
      intros.
      rewrite -> 2 fold_spec_right.
      change (f x (fold_right f i (List.rev (elements s)))) with
        (fold_right f i (List.rev (x::nil)++List.rev (elements s))).
      apply (@fold_right_eqlistA elt oeq A eqA st); auto.
      rewrite <- distr_rev.
      apply eqlistA_rev.
      apply elements_Add_Above; auto.
    Qed.

    Lemma fold_4 :
      forall s s' x (A : Type) (eqA : A -> A -> Prop)
             (st : Equivalence eqA) (i : A) (f : elt -> A -> A),
        compat_op oeq eqA f ->
        Below x s -> Add x s s' -> eqA (fold f s' i) (fold f s (f x i)).
    Proof.
      intros.
      rewrite -> 2 FSetType.Exports.fold_1.
      set (g:=fun (a : A) (e : elt) => f e a).
      change (eqA (fold_left g (elements s') i) (fold_left g (x::elements s) i)).
      unfold g.
      rewrite <- 2 fold_left_rev_right.
      apply (@fold_right_eqlistA elt oeq A eqA st); auto.
      apply eqlistA_rev.
      apply elements_Add_Below; auto.
    Qed.

    Section FoldOpt.

      Variables (A:Type) (eqA:A->A->Prop) (st:Equivalence eqA).
      Variables (f:elt->A->A) (Comp:compat_op oeq eqA f).

      Lemma fold_Equal :
        forall i (s s' : t), s[=]s' -> eqA (fold f s i) (fold f s' i).
      Proof.
        intros. rewrite -> 2 fold_spec_right.
        apply (@fold_right_eqlistA elt oeq A eqA st); auto.
        apply eqlistA_rev.
        apply sort_equivlistA_eqlistA; auto with set.
        red; intro a; do 2 rewrite <- elements_iff; auto.
      Qed.

      Lemma add_fold : forall i (s : t) x,
          In x s ->
          eqA (fold f (add x s) i) (fold f s i).
      Proof.
        intros; apply fold_Equal; auto with set.
      Qed.

      Lemma remove_fold_2 : forall i (s : t) x,
          ~In x s ->
          eqA (fold f (remove x s) i) (fold f s i).
      Proof.
        intros.
        apply fold_Equal; auto with set.
      Qed.

    End FoldOpt.

    Lemma choose_equal : forall (s s' : t),
        Equal s s' ->
        match choose s, choose s' with
        | Some x, Some x' => oeq x x'
        | None, None => True
        | _, _ => False
        end.
    Proof.
      intros s s' H;
        generalize (@choose_1 _ _ s) (@choose_2 _ _ s)
                   (@choose_1 _ _ s') (@choose_2 _ _ s') (@choose_3 _ _ s s');
        destruct (choose s); destruct (choose s'); simpl; intuition.
      apply H5 with s0; rewrite <-H; auto.
      apply H5 with s0; rewrite H; auto.
    Qed.

  End OrdProperties.

End FSetTypeOrdProperties.

Export FSetTypeOrdProperties.


(** * Lemmas from FSetEqProperties *)

Module FSetTypeEqProperties.

  Section BasicProperties.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Variable s s' s'' : t.
    Variable x y z : elt.

    Lemma mem_eq:
      oeq x y -> mem x s=mem y s.
    Proof.
      intro H; rewrite H; auto.
    Qed.

    Lemma equal_mem_1:
      (forall a, mem a s=mem a s') -> equal s s'=true.
    Proof.
      intros; apply equal_1; unfold Equal; intros.
      do 2 rewrite mem_iff; rewrite H; tauto.
    Qed.

    Lemma equal_mem_2:
      equal s s'=true -> forall a, mem a s=mem a s'.
    Proof.
      intros; rewrite (equal_2 H); auto.
    Qed.

    Lemma subset_mem_1:
      (forall a, mem a s=true->mem a s'=true) -> subset s s'=true.
    Proof.
      intros; apply subset_1; unfold Subset; intros a.
      do 2 rewrite mem_iff; auto.
    Qed.

    Lemma subset_mem_2:
      subset s s'=true -> forall a, mem a s=true -> mem a s'=true.
    Proof.
      intros H a; do 2 rewrite <- mem_iff; apply subset_2; auto.
    Qed.

    Lemma empty_mem: mem (t:=t) x empty=false.
    Proof.
      rewrite <- not_mem_iff. fsetdec.
    Qed.

    Lemma is_empty_equal_empty: is_empty s = equal s empty.
    Proof.
      apply bool_1; split; intros.
      auto with set.
      rewrite <- is_empty_iff; auto with set.
    Qed.

    Lemma choose_mem_1: choose s=Some x -> mem x s=true.
    Proof.
      auto with set.
    Qed.

    Lemma choose_mem_2: choose s=None -> is_empty s=true.
    Proof.
      auto with set.
    Qed.

    Lemma add_mem_1: mem x (add x s)=true.
    Proof.
      auto with set ordered_type.
    Qed.

    Lemma add_mem_2: ~ oeq x y -> mem y (add x s)=mem y s.
    Proof.
      apply add_neq_b.
    Qed.

    Lemma remove_mem_1: mem x (remove x s)=false.
    Proof.
      rewrite <- not_mem_iff; auto with set ordered_type.
    Qed.

    Lemma remove_mem_2: ~ oeq x y -> mem y (remove x s)=mem y s.
    Proof.
      apply remove_neq_b.
    Qed.

    Lemma singleton_equal_addb:
      equal (t:=t) (singleton x) (add x empty)=true.
    Proof.
      rewrite (singleton_equal_add x); auto with set.
    Qed.

    Lemma union_mem:
      mem x (union s s')=mem x s || mem x s'.
    Proof.
      apply union_b.
    Qed.

    Lemma inter_mem:
      mem x (inter s s')=mem x s && mem x s'.
    Proof.
      apply inter_b.
    Qed.

    Lemma diff_mem:
      mem x (diff s s')=mem x s && negb (mem x s').
    Proof.
      apply diff_b.
    Qed.

    Lemma mem_3 : ~In x s -> mem x s=false.
    Proof.
      intros; rewrite <- not_mem_iff; auto.
    Qed.

    Lemma mem_4 : mem x s=false -> ~In x s.
    Proof.
      intros; rewrite not_mem_iff; auto.
    Qed.

    Lemma equal_refl: equal s s=true.
    Proof.
      auto with set.
    Qed.

    Lemma equal_sym: equal s s'=equal s' s.
    Proof.
      intros; apply bool_1; do 2 rewrite <- equal_iff; intuition.
    Qed.

    Lemma equal_trans:
      equal s s'=true -> equal s' s''=true -> equal s s''=true.
    Proof.
      intros; rewrite (equal_2 H); auto.
    Qed.

    Lemma equal_equal:
      equal s s'=true -> equal s s''=equal s' s''.
    Proof.
      intros; rewrite (equal_2 H); auto.
    Qed.

    Lemma equal_cardinal:
      equal s s'=true -> cardinal s=cardinal s'.
    Proof.
      auto with set fset.
    Qed.

    Lemma subset_refl: subset s s=true.
    Proof.
      auto with set.
    Qed.

    Lemma subset_antisym:
      subset s s'=true -> subset s' s=true -> equal s s'=true.
    Proof.
      auto with set.
    Qed.

    Lemma subset_trans:
      subset s s'=true -> subset s' s''=true -> subset s s''=true.
    Proof.
      do 3 rewrite <- subset_iff; intros.
      apply Subset_trans with s'; auto.
    Qed.

    Lemma subset_equal:
      equal s s'=true -> subset s s'=true.
    Proof.
      auto with set.
    Qed.

    Lemma choose_mem_3:
      is_empty s=false -> {x:elt|choose s=Some x /\ mem x s=true}.
    Proof.
      intros.
      generalize (@choose_1 elt t s) (@choose_2 elt t s).
      destruct (choose s);intros.
      exists s0;auto with set.
      generalize (H1 Logic.eq_refl); clear H1.
      intros; rewrite (is_empty_1 H1) in H; discriminate.
    Qed.

    Lemma choose_mem_4: choose (t:=t) empty=None.
    Proof.
      generalize (@choose_1 elt t empty).
      case (@choose elt t empty);intros;auto.
      elim (@empty_1 elt t s0); auto.
    Qed.

    Lemma add_mem_3:
      mem y s=true -> mem y (add x s)=true.
    Proof.
      auto with set.
    Qed.

    Lemma add_equal:
      mem x s=true -> equal (add x s) s=true.
    Proof.
      auto with set.
    Qed.

    Lemma remove_mem_3:
      mem y (remove x s)=true -> mem y s=true.
    Proof.
      rewrite remove_b; intros H;destruct (andb_prop _ _ H); auto.
    Qed.

    Lemma remove_equal:
      mem x s=false -> equal (remove x s) s=true.
    Proof.
      intros; apply equal_1; apply remove_Equal.
      rewrite not_mem_iff; auto.
    Qed.

    Lemma add_remove_equal:
      mem x s=true -> equal (add x (remove x s)) s=true.
    Proof.
      intros; apply equal_1; apply add_remove; auto with set.
    Qed.

    Lemma remove_add_equal:
      mem x s=false -> equal (remove x (add x s)) s=true.
    Proof.
      intros; apply equal_1; apply remove_add; auto.
      rewrite not_mem_iff; auto.
    Qed.

    Lemma is_empty_cardinal : is_empty s = zerob (cardinal s).
    Proof.
      intros; apply bool_1; split; intros.
      rewrite cardinal_1; simpl; auto with set.
      assert (cardinal s = 0) by (apply zerob_true_elim; auto).
      auto with set fset.
    Qed.

    Lemma singleton_mem_1: mem (t:=t) x (singleton x)=true.
    Proof.
      auto with set ordered_type.
    Qed.

    Lemma singleton_mem_2: ~ oeq x y -> mem (t:=t) y (singleton x)=false.
    Proof.
      intros; rewrite singleton_b.
      unfold eqb; destruct (OrderedTypeLemmas.eq_dec x y); intuition.
    Qed.

    Lemma singleton_mem_3: mem (t:=t) y (singleton x)=true -> oeq x y.
    Proof.
      intros; apply: singleton_1; eauto with set fset ordered_type.
    Qed.

    Lemma union_sym_equal:
      equal (union s s') (union s' s)=true.
    Proof.
      auto with set.
    Qed.

    Lemma union_subset_equal :
      subset s s'=true -> equal (union s s') s'=true.
    Proof.
      auto with set.
    Qed.

    Lemma union_equal_1:
      equal s s'=true-> equal (union s s'') (union s' s'')=true.
    Proof.
      auto with set.
    Qed.

    Lemma union_equal_2:
      equal s' s''=true-> equal (union s s') (union s s'')=true.
    Proof.
      auto with set.
    Qed.

    Lemma union_assoc_equal:
      equal (union (union s s') s'') (union s (union s' s''))=true.
    Proof.
      auto with set.
    Qed.

    Lemma add_union_singleton_equal :
      equal (add x s) (union (singleton x) s)=true.
    Proof.
      auto with set.
    Qed.

    Lemma union_add_equal :
      equal (union (add x s) s') (add x (union s s'))=true.
    Proof.
      auto with set.
    Qed.

    Lemma union_subset_1 : subset s (union s s')=true.
    Proof.
      auto with set.
    Qed.

    Lemma union_subset_2 : subset s' (union s s')=true.
    Proof.
      auto with set.
    Qed.

    Lemma union_subset_3:
      subset s s''=true -> subset s' s''=true ->
      subset (union s s') s''=true.
    Proof.
      intros; apply subset_1; apply union_Subset_3; auto with set.
    Qed.

    Lemma inter_sym_equal : equal (inter s s') (inter s' s)=true.
    Proof.
      auto with set.
    Qed.

    Lemma inter_subset_equal :
      subset s s'=true -> equal (inter s s') s=true.
    Proof.
      auto with set.
    Qed.

    Lemma inter_equal_1 :
      equal s s'=true -> equal (inter s s'') (inter s' s'')=true.
    Proof.
      auto with set.
    Qed.

    Lemma inter_equal_2 :
      equal s' s''=true -> equal (inter s s') (inter s s'')=true.
    Proof.
      auto with set.
    Qed.

    Lemma inter_assoc_equal :
      equal (inter (inter s s') s'') (inter s (inter s' s''))=true.
    Proof.
      auto with set.
    Qed.

    Lemma union_inter_1_equal :
      equal (inter (union s s') s'') (union (inter s s'') (inter s' s''))=true.
    Proof.
      auto with set.
    Qed.

    Lemma union_inter_2_equal :
      equal (union (inter s s') s'') (inter (union s s'') (union s' s''))=true.
    Proof.
      auto with set.
    Qed.

    Lemma inter_add_1_equal : mem x s'=true ->
                              equal (inter (add x s) s') (add x (inter s s'))=true.
    Proof.
      auto with set.
    Qed.

    Lemma inter_add_2_eqaul : mem x s'=false ->
                              equal (inter (add x s) s') (inter s s')=true.
    Proof.
      intros; apply equal_1; apply inter_add_2.
      rewrite not_mem_iff; auto.
    Qed.

    Lemma inter_subset_1: subset (inter s s') s=true.
    Proof.
      auto with set.
    Qed.

    Lemma inter_subset_2: subset (inter s s') s'=true.
    Proof.
      auto with set.
    Qed.

    Lemma inter_subset_3:
      subset s'' s=true -> subset s'' s'=true ->
      subset s'' (inter s s')=true.
    Proof.
      intros; apply subset_1; apply inter_Subset_3; auto with set.
    Qed.

    Lemma diff_subset: subset (diff s s') s=true.
    Proof.
      auto with set.
    Qed.

    Lemma diff_subset_equal:
      subset s s'=true -> equal (diff s s') empty=true.
    Proof.
      auto with set.
    Qed.

    Lemma remove_inter_singleton:
      equal (remove x s) (diff s (singleton x))=true.
    Proof.
      auto with set.
    Qed.

    Lemma diff_inter_empty_equal :
      equal (inter (diff s s') (inter s s')) empty=true.
    Proof.
      auto with set.
    Qed.

    Lemma diff_inter_all_equal:
      equal (union (diff s s') (inter s s')) s=true.
    Proof.
      auto with set.
    Qed.

  End BasicProperties.

  #[global]
   Hint Immediate empty_mem is_empty_equal_empty add_mem_1
   remove_mem_1 singleton_equal_add union_mem inter_mem
   diff_mem equal_sym add_remove_equal remove_add_equal : set.
  #[global]
   Hint Resolve equal_mem_1 subset_mem_1 choose_mem_1
   choose_mem_2 add_mem_2 remove_mem_2 equal_refl equal_equal
   subset_refl subset_equal subset_antisym
   add_mem_3 add_equal remove_mem_3 remove_equal : set.

  Section GeneralRecursionPrinciple.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Lemma set_rec:  forall (P:t->Type),
        (forall s s', equal s s'=true -> P s -> P s') ->
        (forall s x, mem x s=false -> P s -> P (add x s)) ->
        P empty -> forall s, P s.
    Proof.
      intros.
      apply set_induction; auto; intros.
      apply X with empty; auto with set.
      apply X with (add x s0); auto with set.
      apply equal_1; intro a; rewrite add_iff; rewrite (H0 a); tauto.
      apply X0; auto with set; apply mem_3; auto.
    Qed.

  End GeneralRecursionPrinciple.

  Section ExclusiveSet.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Lemma exclusive_set : forall s s' x,
        ~(In x s/\In x s') <-> mem (t:=t) x s && mem (t:=t) x s'=false.
    Proof.
      intros; do 2 rewrite mem_iff.
      destruct (mem x s); destruct (mem x s'); intuition.
    Qed.

  End ExclusiveSet.

  Section Fold.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Variables (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA).
    Variables (f:elt->A->A)(Comp:compat_op oeq eqA f)(Ass:transpose eqA f).
    Variables (i:A).
    Variables (s s':t)(x:elt).

    Lemma fold_empty: (fold (t:=t) f empty i) = i.
    Proof.
      apply fold_empty; auto.
    Qed.

    Lemma fold_equal:
      equal s s'=true -> eqA (fold f s i) (fold f s' i).
    Proof.
      intros; apply fold_Equal with (eqA:=eqA); auto with set.
    Qed.

    Lemma fold_add:
      mem x s=false -> eqA (fold f (add x s) i) (f x (fold f s i)).
    Proof.
      intros; apply fold_add with (eqA:=eqA); auto.
      rewrite not_mem_iff; auto.
    Qed.

    Lemma add_fold:
      mem x s=true -> eqA (fold f (add x s) i) (fold f s i).
    Proof.
      intros; apply add_fold with (eqA:=eqA); auto with set.
    Qed.

    Lemma remove_fold_1:
      mem x s=true -> eqA (f x (fold f (remove x s) i)) (fold f s i).
    Proof.
      intros; apply remove_fold_1 with (eqA:=eqA); auto with set.
    Qed.

    Lemma remove_fold_2:
      mem x s=false -> eqA (fold f (remove x s) i) (fold f s i).
    Proof.
      intros; apply remove_fold_2 with (eqA:=eqA); auto.
      rewrite not_mem_iff; auto.
    Qed.

    Lemma fold_union:
      (forall x, mem x s && mem x s'=false) ->
      eqA (fold f (union s s') i) (fold f s (fold f s' i)).
    Proof.
      intros; apply fold_union with (eqA:=eqA); auto.
      intros; rewrite exclusive_set; auto.
    Qed.

  End Fold.

  Section Cardinal.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Lemma add_cardinal_1:
      forall (s : t) x, mem x s=true -> cardinal (add x s)=cardinal s.
    Proof.
      auto with set fset.
    Qed.

    Lemma add_cardinal_2:
      forall (s : t) x, mem x s=false -> cardinal (add x s)=S (cardinal s).
    Proof.
      intros; apply add_cardinal_2; auto.
      rewrite not_mem_iff; auto.
    Qed.

    Lemma remove_cardinal_1:
      forall (s : t) x, mem x s=true -> S (cardinal (remove x s))=cardinal s.
    Proof.
      intros; apply remove_cardinal_1; auto with set.
    Qed.

    Lemma remove_cardinal_2:
      forall (s : t) x, mem x s=false -> cardinal (remove x s)=cardinal s.
    Proof.
      intros; apply Equal_cardinal; apply equal_2; auto with set.
    Qed.

    Lemma union_cardinal:
      forall (s s' : t), (forall x, mem x s && mem x s'=false) ->
                         cardinal (union s s')=cardinal s+cardinal s'.
    Proof.
      intros; apply union_cardinal; auto; intros.
      rewrite exclusive_set; auto.
    Qed.

    Lemma subset_cardinalb:
      forall (s s' : t), subset s s'=true -> cardinal s<=cardinal s'.
    Proof.
      intros; apply subset_cardinal; auto with set.
    Qed.

  End Cardinal.

  Section Bool.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Local Open Scope fset_scope.

    Variable f:elt->bool.
    Variable Comp: Proper (oeq==>Logic.eq) f.

    Let Comp' : Proper (oeq==>Logic.eq) (fun x =>negb (f x)).
    Proof.
      repeat red; intros; f_equal; auto.
    Qed.

    Lemma filter_mem: forall (s : t) x, mem x (filter f s)=mem x s && f x.
    Proof.
      intros; apply filter_b; auto.
    Qed.

    Lemma for_all_filter:
      forall (s : t), for_all f s = is_empty (filter (fun x => negb (f x)) s).
    Proof.
      intros; apply bool_1; split; intros.
      apply is_empty_1.
      unfold Empty; intros.
      rewrite filter_iff; auto.
      red; destruct 1.
      rewrite <- (@for_all_iff elt t s f) in H; auto.
      rewrite (H a H0) in H1; discriminate.
      apply for_all_1; auto; red; intros.
      revert H; rewrite <- is_empty_iff.
      unfold Empty; intro H; generalize (H x); clear H.
      rewrite filter_iff; auto.
      destruct (f x); auto.
    Qed.

    Lemma exists_filter :
      forall (s : t), exists_ f s = negb (is_empty (filter f s)).
    Proof.
      intros; apply bool_1; split; intros.
      destruct (exists_2 Comp H) as (a,(Ha1,Ha2)).
      apply bool_6.
      red; intros; apply (@is_empty_2 _ t _ H0 a); auto with set.
      generalize (@choose_1 elt t (filter f s)) (@choose_2 elt t (filter f s)).
      destruct (choose (filter f s)).
      intros H0 _; apply exists_1; auto.
      exists s0; generalize (H0 s0); rewrite filter_iff; auto.
      intros _ H0.
      rewrite (is_empty_1 (H0 Logic.eq_refl)) in H; auto; discriminate.
    Qed.

    Lemma partition_filter_1:
      forall (s : t), equal (fst (partition f s)) (filter f s)=true.
    Proof.
      auto with set.
    Qed.

    Lemma partition_filter_2:
      forall (s : t), equal (snd (partition f s)) (filter (fun x => negb (f x)) s)=true.
    Proof.
      auto with set.
    Qed.

    Lemma filter_add_1 : forall (s : t) x, f x = true ->
                                           filter f (add x s) [=] add x (filter f s).
    Proof.
      red; intros; set_iff; do 2 (rewrite filter_iff; auto); set_iff.
      intuition.
      rewrite <- H; apply Comp; auto with ordered_type.
    Qed.

    Lemma filter_add_2 : forall (s : t) x, f x = false ->
                                           filter f (add x s) [=] filter f s.
    Proof.
      red; intros; do 2 (rewrite filter_iff; auto); set_iff.
      intuition.
      assert (f x = f a) by (apply Comp; auto).
      rewrite H in H1; rewrite H2 in H1; discriminate.
    Qed.

    Lemma add_filter_1 : forall (s s' : t) x,
        f x=true -> (Add x s s') -> (Add x (filter f s) (filter f s')).
    Proof.
      unfold Add; intros.
      repeat rewrite filter_iff; auto.
      rewrite H0; clear H0.
      assert (oeq x y -> f y = true) by
        (intro H0; rewrite <- (Comp H0); auto).
      tauto.
    Qed.

    Lemma add_filter_2 : forall (s s' : t) x,
        f x=false -> (Add x s s') -> filter f s [=] filter f s'.
    Proof.
      unfold Add, Equal; intros.
      repeat rewrite filter_iff; auto.
      rewrite H0; clear H0.
      assert (f a = true -> ~oeq x a).
      intros H0 H1.
      rewrite (Comp H1) in H.
      rewrite H in H0; discriminate.
      tauto.
    Qed.

    Lemma union_filter: forall f g, (compat_bool oeq f) -> (compat_bool oeq g) ->
                                    forall (s : t), union (filter f s) (filter g s) [=] filter (fun x=>orb (f x) (g x)) s.
    Proof.
      clear Comp' Comp f.
      intros.
      assert (compat_bool oeq (fun x => orb (f x) (g x))).
      unfold compat_bool, Proper, respectful; intros.
      rewrite (H x y H1);  rewrite (H0 x y H1); auto.
      unfold Equal; intros; set_iff; repeat rewrite filter_iff; auto.
      assert (f a || g a = true <-> f a = true \/ g a = true).
      split; auto with bool.
      intro H3; destruct (orb_prop _ _ H3); auto.
      tauto.
    Qed.

    Lemma filter_union: forall (s s' : t), filter f (union s s') [=] union (filter f s) (filter f s').
    Proof.
      unfold Equal; intros; set_iff; repeat rewrite filter_iff; auto; set_iff; tauto.
    Qed.

    Lemma for_all_mem_1: forall (s : t),
        (forall x, (mem x s)=true->(f x)=true) -> (for_all f s)=true.
    Proof.
      intros.
      rewrite for_all_filter; auto.
      rewrite is_empty_equal_empty.
      apply equal_mem_1;intros.
      rewrite filter_b; auto.
      rewrite empty_mem.
      generalize (H a); case (mem a s);intros;auto.
      rewrite H0;auto.
    Qed.

    Lemma for_all_mem_2: forall (s : t),
        (for_all f s)=true -> forall x,(mem x s)=true -> (f x)=true.
    Proof.
      intros.
      rewrite for_all_filter in H; auto.
      rewrite is_empty_equal_empty in H.
      generalize (equal_mem_2 H x).
      rewrite filter_b; auto.
      rewrite empty_mem.
      rewrite H0; simpl;intros.
      rewrite <- negb_false_iff; auto.
    Qed.

    Lemma for_all_mem_3:
      forall (s : t) x,(mem x s)=true -> (f x)=false -> (for_all f s)=false.
    Proof.
      intros.
      apply (Sumbool.bool_eq_ind (for_all f s));intros;auto.
      rewrite for_all_filter in H1; auto.
      rewrite is_empty_equal_empty in H1.
      generalize (equal_mem_2 H1 x).
      rewrite filter_b; auto.
      rewrite empty_mem.
      rewrite H.
      rewrite H0.
      simpl;auto.
    Qed.

    Lemma for_all_mem_4:
      forall (s : t), for_all f s=false -> {x:elt | mem x s=true /\ f x=false}.
    Proof.
      intros.
      rewrite for_all_filter in H; auto.
      destruct (choose_mem_3 H) as (x,(H0,H1));intros.
      exists x.
      rewrite filter_b in H1; auto.
      elim (andb_prop _ _ H1).
      split;auto.
      rewrite <- negb_true_iff; auto.
    Qed.

    Lemma for_all_exists:
      forall (s : t), exists_ f s = negb (for_all (fun x =>negb (f x)) s).
    Proof.
      intros.
      rewrite for_all_b; auto.
      rewrite exists_b; auto.
      induction (elements s); simpl; auto.
      destruct (f a); simpl; auto.
    Qed.

  End Bool.

  Section Bool'.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Local Open Scope fset_scope.

    Variable f:elt->bool.
    Variable Comp: compat_bool oeq f.

    Let Comp' : compat_bool oeq (fun x =>negb (f x)).
    Proof.
      unfold compat_bool, Proper, respectful in *; intros; f_equal; auto.
    Qed.

    Lemma exists_mem_1:
      forall (s : t), (forall x, mem x s=true->f x=false) -> exists_ f s=false.
    Proof.
      intros.
      rewrite -> for_all_exists; auto.
      rewrite -> for_all_mem_1;auto with bool.
      intros;generalize (H x H0);intros.
      rewrite negb_true_iff; auto.
    Qed.

    Lemma exists_mem_2:
      forall (s : t), exists_ f s=false -> forall x, mem x s=true -> f x=false.
    Proof.
      intros.
      rewrite -> for_all_exists in H; auto.
      rewrite negb_false_iff in H.
      rewrite <- negb_true_iff.
      apply for_all_mem_2 with (2:=H); auto.
    Qed.

    Lemma exists_mem_3:
      forall (s : t) x, mem x s=true -> f x=true -> exists_ f s=true.
    Proof.
      intros.
      rewrite -> for_all_exists; auto.
      rewrite negb_true_iff.
      apply for_all_mem_3 with x;auto.
      rewrite negb_false_iff; auto.
    Qed.

    Lemma exists_mem_4:
      forall (s : t), exists_ f s=true -> {x:elt | (mem x s)=true /\ (f x)=true}.
    Proof.
      intros.
      rewrite -> for_all_exists in H; auto.
      rewrite -> negb_true_iff in H.
      destruct (@for_all_mem_4 elt t (fun x => negb (f x)) Comp' s) as (x,p); auto.
      elim p;intros.
      exists x;split;auto.
      rewrite <-negb_false_iff; auto.
    Qed.

  End Bool'.

  Section Sum.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.

    Local Open Scope fset_scope.

    Definition sum (f:elt -> nat)(s:t) := fold (fun x => plus (f x)) s 0.
    Notation compat_opL := (compat_op oeq Logic.eq).
    Notation transposeL := (transpose Logic.eq).

    Lemma sum_plus :
      forall f g, Proper (oeq==>Logic.eq) f -> Proper (oeq==>Logic.eq) g ->
                  forall s, sum (fun x =>f x+g x) s = sum f s + sum g s.
    Proof.
      unfold sum.
      intros f g Hf Hg.
      assert (fc : compat_opL (fun x:elt =>plus (f x))).  red; auto with fset.
      assert (ft : transposeL (fun x:elt =>plus (f x))). red; intros x y z.
      rewrite -> !PeanoNat.Nat.add_assoc, (PeanoNat.Nat.add_comm (f x) (f y)); reflexivity.
      assert (gc : compat_opL (fun x:elt => plus (g x))). red; auto with fset.
      assert (gt : transposeL (fun x:elt =>plus (g x))). red; intros x y z.
      rewrite -> !PeanoNat.Nat.add_assoc, (PeanoNat.Nat.add_comm (g x) (g y)); reflexivity.
      assert (fgc : compat_opL (fun x:elt =>plus ((f x)+(g x)))). repeat red; auto.
      assert (fgt : transposeL (fun x:elt=>plus ((f x)+(g x)))). red; intros x y z.
      set (u := (f x + g x)); set (v := (f y + g y)).
      rewrite -> !PeanoNat.Nat.add_assoc, (PeanoNat.Nat.add_comm u).
      reflexivity.
      assert (st : Equivalence (@Logic.eq nat)) by (split; congruence).
      intros s;pattern s; apply set_rec.
      intros.
      rewrite <- (fold_equal st fc 0 H).
      rewrite <- (fold_equal st gc 0 H).
      rewrite <- (fold_equal st fgc 0 H); auto.
      intros; do 3 (rewrite (fold_add st);auto).
      rewrite H0;simpl.
      rewrite <- !(PeanoNat.Nat.add_assoc (f x)); f_equal.
      rewrite !PeanoNat.Nat.add_assoc. f_equal.
      apply PeanoNat.Nat.add_comm.
      do 3 rewrite fold_empty;auto.
    Qed.

    Lemma sum_filter : forall f, (compat_bool oeq f) ->
                                 forall s, (sum (fun x => if f x then 1 else 0) s) = (cardinal (filter f s)).
    Proof.
      unfold sum; intros f Hf.
      assert (st : Equivalence (@Logic.eq nat)) by (split; congruence).
      assert (cc : compat_opL (fun x => plus (if f x then 1 else 0))).
      repeat red; intros.
      rewrite (Hf _ _ H); auto.
      assert (ct : transposeL (fun x => plus (if f x then 1 else 0))).
      red; intros.
      set (a := if f x then _ else _).
      rewrite PeanoNat.Nat.add_comm.
      rewrite <- !PeanoNat.Nat.add_assoc. f_equal.
      apply PeanoNat.Nat.add_comm.
      intros s;pattern s; apply set_rec.
      intros.
      rewrite <- (fold_equal st cc 0 H).
      rewrite <- (Equal_cardinal (filter_equal Hf (equal_2 H))); auto.
      intros; rewrite (fold_add st cc ct); auto.
      generalize (@add_filter_1 elt t f Hf s0 (add x s0) x) (@add_filter_2 elt t f Hf s0 (add x s0) x) .
      assert (~ In x (filter f s0)).
      intro H1; rewrite (mem_1 (filter_1 Hf H1)) in H; discriminate H.
      case (f x); simpl; intros.
      rewrite (cardinal_2 H1 (H2 Logic.eq_refl (Add_add s0 x))); auto.
      rewrite <- (Equal_cardinal (H3 Logic.eq_refl (Add_add s0 x))); auto.
      intros; rewrite fold_empty;auto.
      rewrite cardinal_1; auto.
      unfold Empty; intros.
      rewrite filter_iff; auto; set_iff; tauto.
    Qed.

    Lemma fold_compat :
      forall (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA)
             (f g:elt->A->A),
        (compat_op oeq eqA f) -> (transpose eqA f) ->
        (compat_op oeq eqA g) -> (transpose eqA g) ->
        forall (i:A)(s:t),(forall x:elt, (In x s) -> forall y, (eqA (f x y) (g x y))) ->
                          (eqA (fold f s i) (fold g s i)).
    Proof.
      intros A eqA st f g fc ft gc gt i.
      intro s; pattern s; apply set_rec; intros.
      transitivity (fold f s0 i).
      apply fold_equal with (eqA:=eqA); auto.
      rewrite equal_sym; auto.
      transitivity (fold g s0 i).
      apply H0; intros; apply H1; auto with set.
      elim  (equal_2 H x); auto with set; intros.
      apply fold_equal with (eqA:=eqA); auto with set.
      transitivity (f x (fold f s0 i)).
      apply fold_add with (eqA:=eqA); auto with set.
      transitivity (g x (fold f s0 i)); auto with set ordered_type.
      transitivity (g x (fold g s0 i)); auto with set ordered_type.
      apply gc; auto with set ordered_type.
      symmetry; apply fold_add with (eqA:=eqA); auto.
      do 2 rewrite fold_empty; reflexivity.
    Qed.

    Lemma sum_compat :
      forall f g, Proper (oeq==>Logic.eq) f -> Proper (oeq==>Logic.eq) g ->
                  forall s, (forall x, In x s -> f x=g x) -> sum f s=sum g s.
      intros.
      unfold sum; apply (@fold_compat _ (@Logic.eq nat)); auto with fset.
      intros x x' Hx y y' Hy. rewrite -> Hx, Hy; auto.
      intros x y z; rewrite !PeanoNat.Nat.add_assoc; f_equal; apply PeanoNat.Nat.add_comm.
      intros x x' Hx y y' Hy. rewrite -> Hx, Hy; auto.
      intros x y z; rewrite !PeanoNat.Nat.add_assoc; f_equal; apply PeanoNat.Nat.add_comm.
    Qed.

  End Sum.

End FSetTypeEqProperties.

Export FSetTypeEqProperties.


(** * Additional Lemmas *)

Module FSetTypeLemmas.

  Local Open Scope fset_scope.

  Section FSetTypeLemmas.

    Context {elt : orderedType}.
    Context {t : fsetType elt}.


    (* reflection *)

    Lemma memP x (s : t) : reflect (In x s) (mem x s).
    Proof.
      case H: (mem x s).
      - apply: ReflectT. exact: (mem_2 H).
      - apply: ReflectF. move=> Hin; move: (mem_1 Hin). rewrite H; discriminate.
    Qed.

    Lemma equalP (s1 s2 : t) : reflect (Equal s1 s2) (equal s1 s2).
    Proof.
      case Heq: (equal s1 s2).
      - apply: ReflectT. exact: (equal_2 Heq).
      - apply: ReflectF. move=> HEq. apply/negPf: Heq. exact: (equal_1 HEq).
    Qed.

    Lemma subsetP (s1 s2 : t) : reflect (Subset s1 s2) (subset s1 s2).
    Proof.
      case Hs: (subset s1 s2).
      - apply: ReflectT. exact: (subset_2 Hs).
      - apply: ReflectF. move=> HS. apply/negPf: Hs. exact: (subset_1 HS).
    Qed.

    Lemma emptyP (s : t) : reflect (Empty s) (is_empty s).
    Proof.
      case Hs: (is_empty s).
      - apply: ReflectT. exact: (is_empty_2 Hs).
      - apply: ReflectF. move=> He. apply/negPf: Hs. exact: (is_empty_1 He).
    Qed.


    (* fsetType and predType *)

    Global Canonical fsetPredType := Eval hnf in @PredType elt t (flip mem).

    Lemma oin_set x s : x \in s = mem x s.
    Proof. done. Qed.

    Lemma memPs x s : x \in s <-> mem x s.
    Proof. done. Qed.


    (* mem and empty *)

    Lemma mem_empty x : mem (t:=t) x empty = false.
    Proof. apply/memP => Hin. exact: (empty_1 (t:=t) Hin). Qed.

    Lemma is_empty_mem x (s : t) : is_empty s -> mem x s = false.
    Proof.
      move=> H. apply/negP => /memP Hmem. exact: (is_empty_2 H Hmem).
    Qed.

    Lemma all_not_mem_is_empty (s : t) : (forall x, ~~ mem x s) -> is_empty s.
    Proof.
      move=> H. apply: is_empty_1. move=> x /memP Hmem.
      move: (H x) => /negP; apply. exact: Hmem.
    Qed.

    Lemma Empty_mem x (s : t) : Empty s -> mem x s = false.
    Proof. move=> Hemp. apply/memP => Hin. exact: (Hemp x Hin). Qed.


    (* mem and singleton *)

    Lemma mem_singleton_eq (x y : elt) : mem (t:=t) x (singleton y) -> oeq x y.
    Proof.
      move=> /memP Hin. move: (singleton_1 Hin) => Heq. exact: (OrderedType.eq_sym Heq).
    Qed.

    Lemma eq_mem_singleton (x y : elt) : oeq x y -> mem (t:=t) x (singleton y).
    Proof.
      move=> Heq. apply/memP. move: (OrderedType.eq_sym Heq) => {} Heq.
      exact: (singleton_2 Heq).
    Qed.

    Hint Resolve mem_singleton_eq eq_mem_singleton : set.

    Lemma mem_singleton_iff (x y : elt) : mem (t:=t) x (singleton y) <-> oeq x y.
    Proof. split; by auto with set. Qed.

    Lemma mem_singleton (x y : elt) : mem (t:=t) x (singleton y) = oeqb x y.
    Proof.
      symmetry. case H: (mem x (singleton y)).
      - apply/oeqP. exact: (mem_singleton_eq H).
      - apply/oeqP => Heq. apply/negPf: H. exact: (eq_mem_singleton Heq).
    Qed.

    Lemma not_mem_singleton_neq x y : ~~ mem (t:=t) x (singleton y) -> ~ oeq x y.
    Proof. move=> /negP Hmem Heq. by auto with set. Qed.

    Lemma neq_not_mem_singleton x y : ~ oeq x y -> ~~ mem (t:=t) x (singleton y).
    Proof. move=> Heq. apply/negP => Hmem. by auto with set. Qed.

    Hint Resolve not_mem_singleton_neq neq_not_mem_singleton : set.

    Lemma not_mem_singleton_iff x y : ~~ mem (t:=t) x (singleton y) <-> ~ oeq x y.
    Proof. by split; auto with set. Qed.

    Lemma not_mem_singleton x y : ~~ mem (t:=t) x (singleton y) = ~~ oeqb x y.
    Proof.
      symmetry. case Hmem: (mem x (singleton y)) => /=.
      - apply/negPn/oeqP. by auto with set.
      - apply/oeqP => H. apply/negPf: Hmem. by auto with set.
    Qed.


    (* mem and add *)

    Lemma mem_add_or x y (s : t) : mem x (add y s) -> oeq x y \/ mem x s.
    Proof.
      move=> /memP Hin. move: (add_iff s y x) => [H _].
      move: (H Hin); case => {Hin H}.
      - move=> Heq; left. exact: OrderedType.eq_sym.
      - move=> Hin; right. apply/memP; assumption.
    Qed.

    Lemma mem_add_l x y (s : t) : oeq x y -> mem x (add y s).
    Proof. by auto with set ordered_type. Qed.

    Lemma mem_add_r x y (s : t) : mem x s -> mem x (add y s).
    Proof. by auto with set ordered_type. Qed.

    Lemma mem_add_neq {x y s} : ~ (oeq x y) -> mem x (add y s) = mem (t:=t) x s.
    Proof. by auto with set ordered_type. Qed.

    Hint Resolve mem_add_or mem_add_l mem_add_r : set.

    Lemma mem_add_iff x y (s : t) : mem x (add y s) <-> oeq x y \/ mem x s.
    Proof. by case_all; auto with set. Qed.

    Lemma mem_add x y (s : t) : mem x (add y s) = oeqb x y || mem x s.
    Proof.
      symmetry. case Hmem: (mem x (add y s)).
      - apply/orP. case/mem_add_or: Hmem => H.
        + by left; apply/oeqP.
        + by right.
      - apply: orb_false_intro.
        + apply/negP => H. apply/negPf: Hmem. exact: (mem_add_l _ (oeqP H)).
        + apply/negP => H. apply/negPf: Hmem. exact: (mem_add_r _ H).
    Qed.

    Lemma not_mem_add_l x y (s : t) : ~~ mem x (add y s) -> ~ oeq x y.
    Proof. move=> /negP Hmem; by auto with set. Qed.

    Lemma not_mem_add_r x y (s : t) : ~~ mem x (add y s) -> ~~ mem x s.
    Proof.
      move=> /negP Hmem. apply/negP => H; apply: Hmem. by auto with set.
    Qed.

    Lemma neq_not_mem_add x y (s : t) :
      ~ oeq x y -> ~~ mem x s -> ~~ mem x (add y s).
    Proof.
      move=> Heq /negP Hmem. apply/negP => H. apply: Hmem.
      rewrite -(mem_add_neq Heq). assumption.
    Qed.

    Hint Resolve neq_not_mem_add : set.

    Lemma not_mem_add_iff x y (s : t) :
      ~~ mem x (add y s) <-> ~ oeq x y /\ ~~ mem x s.
    Proof.
      split.
      - split; by eauto using not_mem_add_l, not_mem_add_r.
      - move=> [H1 H2]. by auto with set.
    Qed.

    Lemma not_mem_add x y (s : t) :
      ~~ mem x (add y s) = (x ~=? y)%OT && ~~ mem x s.
    Proof.
      symmetry. case Hmem: (mem x (add y s)) => /=.
      - apply/negP => /andP [H1 H2]. apply/idP: H2. move/oeqP: H1 => H1.
        rewrite (mem_add_neq H1) in Hmem. assumption.
      - move/idP/negP: Hmem => /not_mem_add_iff [/oeqP H1 H2]. by rewrite H1 H2.
    Qed.


    (* mem and union *)

    Lemma mem_union_or x (s1 s2 : t) : mem x (union s1 s2) -> mem x s1 \/ mem x s2.
    Proof.
      move=> /memP H. case: (union_1 H).
      - by left; apply/memP.
      - by right; apply/memP.
    Qed.

    Lemma mem_union_l x (s1 s2 : t) : mem x s1 -> mem x (union s1 s2).
    Proof. move/memP => H. apply/memP. exact: union_2. Qed.

    Lemma mem_union_r x (s1 s2 : t) : mem x s2 -> mem x (union s1 s2).
    Proof. move/memP => H. apply/memP. exact: union_3. Qed.

    Hint Resolve mem_union_l mem_union_r : set.

    Lemma mem_union_iff x (s1 s2 : t) : mem x (union s1 s2) <-> mem x s1 \/ mem x s2.
    Proof. split; first exact: mem_union_or. by case; auto with set. Qed.

    Lemma mem_union x (s1 s2 : t) : mem x (union s1 s2) = mem x s1 || mem x s2.
    Proof.
      symmetry. case H1: (mem x (union s1 s2)).
      - case: (mem_union_or H1) => -> //=; by rewrite ?orbT.
      - apply/negP => /orP [] H; apply/negPf: H1; by auto with set.
    Qed.

    Lemma not_mem_union_l x (s1 s2 : t) : ~~ mem x (union s1 s2) -> ~~ mem x s1.
    Proof.
      move=> /negP H; apply/negP => Hmem; apply: H. exact: (mem_union_l _ Hmem).
    Qed.

    Lemma not_mem_union_r x (s1 s2 : t) : ~~ mem x (union s1 s2) -> ~~ mem x s2.
    Proof. rewrite union_sym. exact: not_mem_union_l. Qed.

    Lemma not_mem_union x (s1 s2 : t) :
      ~~ mem x s1 -> ~~ mem x s2 -> ~~ mem x (union s1 s2).
    Proof.
      move=> /negP H1 /negP H2; apply/negP => Hmem.
      case: (mem_union_or Hmem) => H3.
      - apply: H1; assumption.
      - apply: H2; assumption.
    Qed.

    Hint Resolve not_mem_union : set.

    Lemma not_mem_union_iff x (s1 s2 : t) :
      ~~ mem x (union s1 s2) <-> ~~ mem x s1 /\ ~~ mem x s2.
    Proof.
      case_all.
      - exact: (not_mem_union_l H).
      - exact: (not_mem_union_r H).
      - exact: (not_mem_union H0 H1).
    Qed.


    (* mem and subset *)

    Lemma mem_subset x (s1 s2 : t) :
      mem x s1 -> subset s1 s2 -> mem x s2.
    Proof.
      move=> /memP Hin Hsub; apply/memP. move: (subset_2 Hsub) => {} Hsub.
      exact: (Hsub _ Hin).
    Qed.

    Lemma not_mem_subset x (s1 s2 : t) :
      ~~ mem x s2 -> subset s1 s2 -> ~~ mem x s1.
    Proof.
      move=> Hmem2 Hsub. apply/negP=> Hmem1. move/negP: Hmem2; apply.
      exact: (mem_subset Hmem1 Hsub).
    Qed.


    (* mem and \in *)

    Lemma oin_elements x (s : t) : (x \in elements s) = (mem x s).
    Proof.
      case Hmem: (mem x s).
      - apply/oinP. move/memP: Hmem. exact: elements_1.
      - apply/negP => /oinP Hin. apply/negPf: Hmem. apply/memP.
        exact: elements_2.
    Qed.

    Lemma mem_oin_elements x (s : t) : mem x s -> x \in elements s.
    Proof. by rewrite oin_elements. Qed.

    Lemma oin_elements_mem x (s : t) : x \in elements s -> mem x s.
    Proof. by rewrite oin_elements. Qed.

    Lemma memPo x (s : t) : (x \in elements s) <-> (mem x s).
    Proof. by rewrite oin_elements. Qed.

    Lemma mem_of_list x (s : olist elt) : mem (t:=t) x (of_list s) = (x \in s).
    Proof.
      case Hin: (x \in s).
      - apply/memP. apply/of_list_1. move/oinP: Hin. by apply.
      - apply/negP => /memP /of_list_1 Hmem. apply/negPf: Hin.
        apply/oinP. assumption.
    Qed.

    Lemma mem_of_list_oin x (s : olist elt) : mem (t:=t) x (of_list s) -> x \in s.
    Proof. by rewrite mem_of_list. Qed.

    Lemma oin_mem_of_list x (s : olist elt) : x \in s -> mem (t:=t) x (of_list s).
    Proof. by rewrite mem_of_list. Qed.

    Lemma mem_of_list_iff x (s : olist elt) : mem (t:=t) x (of_list s) <-> x \in s.
    Proof. by rewrite mem_of_list. Qed.

    Lemma inPo x (s : t) : reflect (In x s) (x \in elements s).
    Proof.
      case Hmem: (x \in elements s).
      - apply: ReflectT. apply/memP. move/memPo: Hmem. by apply.
      - apply/ReflectF => Hin. apply/negPf: Hmem. apply/memPo.
        move/memP: Hin. by apply.
    Qed.

    Definition inPa := elements_iff (t:=t).


    (* equal *)

    Lemma equal_refl (s : t) : equal s s.
    Proof. apply: equal_1. exact: Equal_refl. Qed.

    Lemma equal_sym (s1 s2 : t) : equal s1 s2 = equal s2 s1.
    Proof.
      case H: (equal s2 s1).
      - apply/equalP. move/equalP: H. exact: Equal_sym.
      - apply/negP=> /equalP H1. apply/negPf/equalP: H. exact: Equal_sym.
    Qed.

    Lemma equal_trans (s1 s2 s3 : t) : equal s1 s2 -> equal s2 s3 -> equal s1 s3.
    Proof.
      move=> /equal_2 H12 /equal_2 H23. apply: equal_1.
      exact: (Equal_trans H12 H23).
    Qed.

    Global Instance equal_ST : Equivalence (equal (t:=t)).
    Proof.
      split.
      - exact: equal_refl.
      - move=> x y. by rewrite equal_sym.
      - exact: equal_trans.
    Qed.

    Lemma cardinal_neq (s1 s2 : t) :
      cardinal s1 <> cardinal s2 -> ~~ equal s1 s2.
    Proof.
      move=> Hcar. apply/negP => /equalP Heq. apply: Hcar.
      rewrite Heq. reflexivity.
    Qed.


    (* add *)

    Lemma add_singleton_sym x y :
      Equal (t:=t) (add x (singleton y)) (add y (singleton x)).
    Proof. rewrite !add_union_singleton union_sym. reflexivity. Qed.

    Lemma add_twice x (s : t) : Equal (add x (add x s)) (add x s).
    Proof.
      move=> y. split => H.
      - case/add_iff: H => H.
        + exact: (add_1 _ H).
        + assumption.
      - apply/add_iff. by right.
    Qed.


    (* union *)

    Lemma union_Empty_l (s1 s2 : t) : Empty (union s1 s2) -> Empty s1.
    Proof.
      move=> H x Hin. apply: (H x). apply/union_iff. left; assumption.
    Qed.

    Lemma union_Empty_r (s1 s2 : t) : Empty (union s1 s2) -> Empty s2.
    Proof.
      move=> H x Hin. apply: (H x). apply/union_iff. right; assumption.
    Qed.

    Lemma union_empty_l (s : t) : Equal (union empty s) s.
    Proof.
      move=> v; split => Hin.
      - case: (union_1 Hin) => {} Hin.
        + apply: False_ind. apply: empty_1. exact: Hin.
        + assumption.
      - apply: union_3. assumption.
    Qed.

    Lemma union_empty_r (s : t) : Equal (union s empty) s.
    Proof. rewrite union_sym. exact: union_empty_l. Qed.

    Lemma union_singleton_l x (s : t) : Equal (union (singleton x) s) (add x s).
    Proof. by rewrite add_union_singleton. Qed.

    Lemma union_singleton_r x (s : t) : Equal (union s (singleton x)) (add x s).
    Proof. rewrite union_sym. exact: union_singleton_l. Qed.

    Lemma union_add_l x (s1 s2 : t) :
      Equal (union (add x s1) s2) (add x (union s1 s2)).
    Proof. exact: union_add. Qed.

    Lemma union_add_r x (s1 s2 : t) :
      Equal (union s1 (add x s2)) (add x (union s1 s2)).
    Proof.
      rewrite (union_sym s1 (add _ _)) (union_sym s1 s2). exact: union_add_l.
    Qed.

    Lemma union_subset_Equal (s1 s2 : t) :
      subset s1 s2 -> Equal (union s1 s2) s2.
    Proof. move=> /subset_2 Hsub. exact: (union_Subset_Equal Hsub). Qed.

    Lemma union_same (s : t) : Equal (union s s) s.
    Proof. apply: union_Subset_Equal. exact: Subset_refl. Qed.

    Lemma union_distr_l (s1 s2 s3 : t) :
      Equal (union (union s1 s2) (union s1 s3))
            (union s1 (union s2 s3)).
    Proof.
      rewrite -union_assoc (union_sym _ s1)
              -union_assoc union_same union_assoc. reflexivity.
    Qed.

    Lemma union_distr_r (s1 s2 s3 : t) :
      Equal (union (union s1 s3) (union s2 s3))
            (union (union s1 s2) s3).
    Proof.
      rewrite (union_sym s1) (union_sym s2) (union_sym (union s1 s2)).
      exact: union_distr_l.
    Qed.

    Lemma add_union_distr x (s1 s2 : t) :
      Equal (add x (union s1 s2))
            (union (add x s1) (add x s2)).
    Proof.
      rewrite union_add. rewrite (union_sym _ (add x s2)).
      rewrite union_add. rewrite add_twice. rewrite union_sym. reflexivity.
    Qed.


    (* subset *)

    Lemma subset_unions (sa1 sa2 sb1 sb2 : t) :
      subset sa1 sb1 -> subset sa2 sb2 ->
      subset (union sa1 sa2) (union sb1 sb2).
    Proof.
      move=> Hsub1 Hsub2. apply/subset_1 => x /memP Hmemx.
      apply/memP. move: (mem_union_or Hmemx) => {Hmemx} [] Hmemx.
      - apply: mem_union_l. exact: (mem_subset Hmemx Hsub1).
      - apply: mem_union_r. exact: (mem_subset Hmemx Hsub2).
    Qed.

    Lemma subset_l_union (s1 s2 : t) : subset s1 (union s2 s1).
    Proof. apply/subset_1. exact: union_Subset_2. Qed.

    Lemma subset_r_union (s1 s2 : t) : subset s1 (union s1 s2).
    Proof. apply/subset_1. exact: union_Subset_1. Qed.

    Hint Immediate subset_l_union subset_r_union : set.

    Lemma subset_is_empty_r (s1 s2 : t) : subset s1 s2 -> is_empty s2 -> is_empty s1.
    Proof.
      move=> /subsetP Hsub /emptyP Hemp. apply/emptyP. move=> x Hin1. apply: (Hemp x).
      exact: (Hsub _ Hin1).
    Qed.

    Lemma subset_is_empty_l (s1 s2 : t) : is_empty s1 -> subset s1 s2.
    Proof.
      move/emptyP=> Hemp. apply/subsetP. move=> x Hin1. apply: False_ind.
      exact: (Hemp _ Hin1).
    Qed.

    Lemma subset_empty_l (s : t) : subset empty s.
    Proof. apply/subset_1. exact: subset_empty. Qed.

    Lemma subset_empty_r (s : t) : subset s empty = is_empty s.
    Proof.
      case H: (is_empty s).
      - exact: (subset_is_empty_l _ H).
      - apply/negP => H1. apply/negPf: H. apply: (subset_is_empty_r H1).
        apply: is_empty_1. exact: empty_1.
    Qed.

    Lemma subset_cardinal (s1 s2 : t) : subset s1 s2 -> cardinal s1 <= cardinal s2.
    Proof. move=> /subsetP Hs. exact: (subset_cardinal Hs). Qed.

    Lemma subset_cardinal_equal (s1 s2 : t) :
      subset s1 s2 -> cardinal s1 = cardinal s2 -> equal s1 s2.
    Proof.
      move/subsetP. move=> Hsub Hcar. apply/equalP. move=> x. split.
      - move=> Hin1. exact: (Hsub _ Hin1).
      - move=> Hin2. case Hmem1: (mem x s1).
        + apply/memP. exact: Hmem1.
        + move/memP: Hmem1 => Hin1. move: (subset_cardinal_lt Hsub Hin2 Hin1).
          rewrite Hcar => H. rewrite ltnn in H. discriminate.
    Qed.

    Lemma subset_singleton_mem x (s : t) : subset (singleton x) s -> mem x s.
    Proof.
      move=> H. apply/memP. move: (subset_2 H) => {} H.
      apply: (H x). apply: singleton_2. reflexivity.
    Qed.

    Lemma mem_subset_singleton x (s : t) : mem x s -> subset (singleton x) s.
    Proof.
      move/memP=> H. apply: subset_1 => y Hy. move: (singleton_1 Hy) => {Hy} Hxy.
      exact: (In_1 Hxy H).
    Qed.

    Hint Resolve mem_subset_singleton : set.

    Lemma subset_singleton x (s : t) : subset (singleton x) s = mem x s.
    Proof.
      case Hmem: (mem x s).
      - exact: mem_subset_singleton.
      - apply/negP => Hsub. move/negP: Hmem; apply. exact: subset_singleton_mem.
    Qed.

    Lemma subset_union_l (s1 s2 s3 : t) : subset s1 s2 -> subset s1 (union s2 s3).
    Proof.
      move=> Hsub. apply: subset_1 => x /memP Hx. apply/memP.
      apply/mem_union_l. exact: (mem_subset Hx Hsub).
    Qed.

    Lemma subset_union_r (s1 s2 s3 : t) : subset s1 s3 -> subset s1 (union s2 s3).
    Proof. rewrite union_sym. exact: subset_union_l. Qed.

    Lemma subset_union_2l (s1 s2 s3 : t) :
      subset s1 s3 -> subset s2 s3 -> subset (union s1 s2) s3.
    Proof. by auto with set. Qed.

    Hint Resolve subset_unions subset_union_l subset_union_r subset_union_2l : set.

    Lemma subset_union_ll (s1 s2 s3 : t) : subset (union s1 s2) s3 -> subset s1 s3.
    Proof.
      move=> Hsub. move: (subset_2 Hsub) => {} Hsub.
      apply: subset_1 => x Hinx. apply: (Hsub x). exact: (union_2 _ Hinx).
    Qed.

    Lemma subset_union_lr (s1 s2 s3 : t) : subset (union s1 s2) s3 -> subset s2 s3.
    Proof. rewrite union_sym. exact: subset_union_ll. Qed.

    Lemma subset_union_b (s1 s2 s3 : t) :
      subset (union s1 s2) s3 = subset s1 s3 && subset s2 s3.
    Proof.
      case H: (subset s1 s3 && subset s2 s3).
      - move/andP: H => [H13 H23]. apply: subset_union_2l; assumption.
      - apply/negP => H123. move/negP: H; apply.
        by rewrite (subset_union_ll H123) (subset_union_lr H123).
    Qed.

    Lemma subset_refl (s : t) : subset s s.
    Proof. apply: subset_1. exact: Subset_refl. Qed.

    Lemma subset_trans (s1 s2 s3 : t) :
      subset s1 s2 -> subset s2 s3 -> subset s1 s3.
    Proof.
      move=> H12 H23. move: (subset_2 H12) => {} H12.
      move: (subset_2 H23) => {} H23. apply: subset_1.
      exact: (Subset_trans H12 H23).
    Qed.

    Lemma subset_add_r x (s1 s2 : t) : subset s1 s2 -> subset s1 (add x s2).
    Proof.
      move=> Hsub. move: (subset_2 Hsub) => {} Hsub.
      apply/subset_1. exact: subset_add_2.
    Qed.

    Lemma subset_add_l x (s1 s2 : t) :
      mem x s2 -> subset s1 s2 -> subset (add x s1) s2.
    Proof.
      move=> /memP Hin Hsub. move: (subset_2 Hsub) => {} Hsub.
      apply/subset_1. exact: subset_add_3.
    Qed.

    Lemma subset_add_ll x (s1 s2 : t) : subset (add x s1) s2 -> mem x s2.
    Proof.
      rewrite add_union_singleton. move=> H.
      move: (subset_union_ll H) => {} H. exact: (subset_singleton_mem H).
    Qed.

    Lemma subset_add_lr x (s1 s2 : t) : subset (add x s1) s2 -> subset s1 s2.
    Proof. rewrite add_union_singleton. exact: subset_union_lr. Qed.

    Lemma subset_add_b x (s1 s2 : t) : subset (add x s1) s2 = mem x s2 && subset s1 s2.
    Proof.
      case H: (mem x s2 && subset s1 s2).
      - move/andP: H => [H1 H2]. exact: (subset_add_l H1 H2).
      - apply/negP => Hsub. move/negP: H; apply.
        by rewrite (subset_add_ll Hsub) (subset_add_lr Hsub).
    Qed.

    Lemma subset_antisym (s1 s2 : t) : subset s1 s2 -> subset s2 s1 -> equal s1 s2.
    Proof.
      move=> /subset_2 Hsub12 /subset_2 Hsub21. apply/equal_1.
      exact: Subset_antisym.
    Qed.

    Hint Resolve subset_add_l subset_add_r : set.


    (* elements *)

    Lemma elements_singleton x : eqlistA oeq (elements (t:=t) (singleton x)) (x::nil).
    Proof.
      rewrite (@elements_Add_Above _ _ (empty) (singleton x) x).
      - rewrite elements_empty /=. apply: eqlistA_cons.
        + exact: OrderedType.eq_refl.
        + exact: eqlistA_nil.
      - move=> y Hin. apply: False_ind. move/empty_iff: Hin. by apply.
      - move=> y. split.
        + move=> Hin. left. exact: (singleton_1 Hin).
        + case=> Hin.
          * apply: singleton_2. assumption.
          * apply: False_ind. move/empty_iff: Hin. by apply.
    Qed.


    (* inA *)

    Lemma mem_inA_elements x (s : t) :
      mem x s -> InA oeq x (elements s).
    Proof. move=> Hmem. apply: elements_1. apply/memP. assumption. Qed.

    Lemma inA_elements_mem x (s : t) :
      InA oeq x (elements s) -> mem x s.
    Proof. move=> Hin. apply/memP. apply: elements_2. assumption. Qed.

    Lemma memPa x (s : t) : reflect (InA oeq x (elements s)) (mem x s).
    Proof.
      case Hmem: (mem x s).
      - apply: ReflectT. exact: mem_inA_elements.
      - apply:ReflectF => Hin. apply/negPf: Hmem. exact: inA_elements_mem.
    Qed.


    (* of_list *)

    Lemma in_of_list_inA x s : In (t:=t) x (of_list s) -> InA oeq x s.
    Proof.
      move=> Hin. move: (of_list_1 (t:=t) s x) => [H1 H2].
      exact: (H1 Hin).
    Qed.

    Lemma inA_in_of_list x s : InA oeq x s -> In (t:=t) x (of_list s).
    Proof.
      move=> Hin. move: (of_list_1 (t:=t) s x) => [H1 H2].
      exact: (H2 Hin).
    Qed.

    Lemma mem_of_list_inA x s : mem (t:=t) x (of_list s) -> InA oeq x s.
    Proof. move=> /memP Hin. exact: in_of_list_inA. Qed.

    Lemma inA_mem_of_list x s : InA oeq x s -> mem (t:=t) x (of_list s).
    Proof. move=> Hin; apply/memP. exact: inA_in_of_list. Qed.


    (* remove *)

    Lemma mem_remove_neq x y (s : t) :
      mem x (remove y s) -> ~ oeq x y.
    Proof.
      move=> Hmem Heq. move: (OrderedType.eq_sym Heq) => {} Heq.
      apply: (@remove_1 _ _ s y x Heq). apply/memP. assumption.
    Qed.

    Lemma mem_remove_mem x y (s : t) :
      mem x (remove y s) -> mem x s.
    Proof.
      move=> Hmem. apply/memP; apply: (@remove_3 _ _ s y x); apply/memP; assumption.
    Qed.

    Lemma eq_not_mem_remove x y (s : t) :
      oeq x y -> ~~ mem x (remove y s).
    Proof.
      move=> Heq. apply/negP => Hmem. exact: (mem_remove_neq Hmem Heq).
    Qed.

    Lemma neq_mem_remove x y (s : t) :
      ~ oeq x y -> mem x s -> mem x (remove y s).
    Proof.
      move=> Hne Hmem. apply/memP; apply: remove_2.
      - move=> Heq; apply: Hne; apply: OrderedType.eq_sym; assumption.
      - apply/memP; assumption.
    Qed.

    Lemma in_remove_neq x y (s : t) :
      In x (remove y s) -> ~ oeq x y.
    Proof. move=> /memP Hmem. exact: (mem_remove_neq Hmem). Qed.

    Hint Resolve eq_not_mem_remove neq_mem_remove : set.


    (* diff *)

    Lemma diff_add x (s1 s2 : t) :
      Equal (diff s1 (add x s2)) (remove x (diff s1 s2)).
    Proof.
      split => Hin.
      - apply: remove_2.
        + move=> Heq; apply: (diff_2 Hin).
          exact: (add_1 _ Heq).
        + apply: (diff_3 (diff_1 Hin)).
          move=> H; apply: (diff_2 Hin).
          exact: (add_2 _ H).
      - apply: diff_3.
        + exact: (diff_1 (remove_3 Hin)).
        + move: (Add_add s2 x a).
          move=> [H _].
          move=> H1; case: (H H1) => {H H1}.
          * move=> Heq.
            move: (OrderedType.eq_sym Heq) => {} Heq.
            exact: (in_remove_neq Hin Heq).
          * move=> Hins2.
            exact: (diff_2 (remove_3 Hin) Hins2).
    Qed.

    Lemma subset_union_diff_l (s1 s2 s3 : t) :
      subset s1 (union s2 s3) -> subset (diff s1 s2) s3.
    Proof.
      move=> H. apply: subset_1 => x Hin_diff. move: (subset_2 H) => {} H.
      move: (H x (diff_1 Hin_diff)) => Hin_union. case: (union_1 Hin_union).
      - move=> Hin2. apply: False_ind; exact: (diff_2 Hin_diff Hin2).
      - by apply.
    Qed.

    Lemma subset_union_diff_r (s1 s2 s3 : t) :
      subset s1 (union s2 s3) -> subset (diff s1 s3) s2.
    Proof. rewrite union_sym. exact: subset_union_diff_l. Qed.

    Hint Resolve subset_union_diff_l subset_union_diff_r : set.

    Lemma subset_union_diff (s1 s2 : t) : subset s1 (union (diff s1 s2) s2).
    Proof.
      apply: subset_1 => x Hinx. case Hmem: (mem x s2).
      - apply: union_3. apply/memP; assumption.
      - apply: union_2. apply: (diff_3 Hinx). apply/memP. by rewrite Hmem.
    Qed.

    Lemma union_diff (s1 s2 : t) : Equal (union (diff s1 s2) s2) (union s1 s2).
    Proof.
      split => H.
      - case: (union_1 H) => {} H.
        + apply: union_2. exact: (diff_1 H).
        + by apply: union_3.
      - case Hmem2: (mem a s2).
        + move/memP: Hmem2 => Hin2. by apply: union_3.
        + move/memP: Hmem2 => Hin2. apply: union_2. apply: (diff_3 _ Hin2).
          by case: (union_1 H).
    Qed.

    Lemma subset_diff_union (s1 s2 s3 : t) :
      subset (diff s1 s2) s3 -> subset s1 (union s2 s3).
    Proof.
      move=> H. move: (subset_2 H) => {} H. apply/subset_1 => x Hinx.
      case H2: (mem x s2).
      - apply: union_2. apply/memP; assumption.
      - apply: union_3. apply: (H x). apply: (diff_3 Hinx).
        apply/memP. by rewrite H2.
    Qed.

    Lemma subset_diff_same (s1 s2 : t) u :
      subset s1 s2 ->
      subset (diff s1 u) (diff s2 u).
    Proof.
      move/subsetP=> Hsub. apply/subsetP.
      apply: (diff_s_m Hsub). exact: Subset_refl.
    Qed.

    Lemma subset_diff (s1 s2 t1 t2 : t) :
      subset s1 s2 ->
      subset t2 t1 ->
      subset (diff s1 t1) (diff s2 t2).
    Proof.
      move => /subsetP Hsubs /subsetP Hsubt. apply/subsetP.
      exact: (diff_s_m Hsubs Hsubt).
    Qed.

    Lemma diff_empty_l (s : t) : Equal (diff empty s) empty.
    Proof.
      move=> x; split => H.
      - by elim: (empty_diff_1 empty_1 H).
      - by elim: (empty_1 H).
    Qed.

    Lemma diff_empty_r (s : t) : Equal (diff s empty) s.
    Proof. by rewrite (empty_diff_2 s empty_1). Qed.


    (* inter *)

    Lemma mem_inter_l x (s1 s2 : t) : mem x (inter s1 s2) -> mem x s1.
    Proof. by eauto with set. Qed.

    Lemma mem_inter_r x (s1 s2 : t) : mem x (inter s1 s2) -> mem x s2.
    Proof. by eauto with set. Qed.

    Lemma mem2_mem_inter x (s1 s2 : t) :
      mem x s1 -> mem x s2 -> mem x (inter s1 s2).
    Proof. by auto with set. Qed.

    Lemma mem_inter_iff x (s1 s2 : t) :
      mem x (inter s1 s2) <-> mem x s1 /\ mem x s2.
    Proof. by case_all; eauto with set. Qed.

    Lemma mem_inter_b x (s1 s2 : t) :
      mem x (inter s1 s2) = mem x s1 && mem x s2.
    Proof.
      symmetry. case Hmem: (mem x (inter s1 s2)).
      - by apply/andP; split; eauto using mem_inter_l, mem_inter_r.
      - apply/negP=> /andP [H1 H2]. apply/negPf: Hmem. exact: (mem2_mem_inter H1 H2).
    Qed.


    (* disjoint *)

    Definition disjoint (s1 s2 : t) : bool := is_empty (inter s1 s2).

    Notation "s [o] t" := (disjoint s t) (at level 70, no associativity) : fset_scope.

    Lemma disjoint_sym (s1 s2 : t) : disjoint s1 s2 = disjoint s2 s1.
    Proof. rewrite /disjoint inter_sym. reflexivity. Qed.

    Lemma disjoint_nonempty_irrefl (s : t) :
      ~~ is_empty s -> disjoint s s = false.
    Proof.
      move=> Hemp. apply/negP => H. move/negP: Hemp; apply.
      move: H. by rewrite /disjoint inter_Subset_Equal.
    Qed.

    Global Instance disjoint_compat : Proper (Equal ==> Equal ==> Logic.eq) disjoint.
    Proof.
      move=> s1 s2 Heq1 s3 s4 Heq2. rewrite /disjoint. rewrite Heq1 Heq2. reflexivity.
    Qed.

    Lemma mem_disjoint_inl x (s1 s2 : t) :
      disjoint s1 s2 -> mem x s1 -> ~~ mem x s2.
    Proof.
      move=> Hd Hm1. apply/negP => Hm2. move: (is_empty_2 Hd) => {} Hd.
      apply: (Hd x). apply/memP. exact: (mem2_mem_inter Hm1 Hm2).
    Qed.

    Lemma mem_disjoint_inr x (s1 s2 : t) :
      disjoint s1 s2 -> mem x s2 -> ~~ mem x s1.
    Proof. rewrite disjoint_sym. exact: mem_disjoint_inl. Qed.

    Lemma all_mem_disjoint s1 s2 :
      (forall x, mem x s1 -> ~~ mem x s2) -> disjoint s1 s2.
    Proof.
      move=> H. apply: all_not_mem_is_empty. move=> x. apply/negP => Hmem.
      move: (H x (mem_inter_l Hmem)). move/negP; apply. exact: (mem_inter_r Hmem).
    Qed.

    Lemma disjoint_singleton_r x (s : t) :
      disjoint s (singleton x) = ~~ mem x s.
    Proof.
      case H: (mem x s) => /=.
      - apply/negP => Hd. move: (is_empty_2 Hd) => Hemp. apply: (Hemp x).
        apply/memP. apply: (mem2_mem_inter H). apply: eq_mem_singleton.
        exact: OrderedType.eq_refl.
      - move/negP: H => H. apply: is_empty_1 => v /memP Hv. apply: H.
        rewrite -(mem_singleton_eq (mem_inter_r Hv)). exact: (mem_inter_l Hv).
    Qed.

    Lemma disjoint_singleton_l x s : disjoint (singleton x) s = ~~ mem x s.
    Proof. rewrite disjoint_sym. exact: disjoint_singleton_r. Qed.

    Lemma disjoint_add_r x (s1 s2 : t) :
      disjoint s1 (add x s2) = ~~ mem x s1 && disjoint s1 s2.
    Proof.
      case Hx: (mem x s1) => /=.
      - apply/negP => Hd. move: (is_empty_2 Hd) => Hemp. apply: (Hemp x).
        apply/memP. apply: (mem2_mem_inter Hx). apply: mem_add_l.
        exact: OrderedType.eq_refl.
      - case Hd12: (disjoint s1 s2) => /=.
        + apply: is_empty_1 => v /memP Hv.
          move: (mem_inter_l Hv) (mem_inter_r Hv) => {Hv} Hv1 Hv2.
          move: (is_empty_2 Hd12) => {Hd12} Hemp. apply: (Hemp v) => {Hemp}.
          apply/memP. apply: (mem2_mem_inter Hv1).
          case: (mem_add_or Hv2); last by apply. move=> H.
          apply: False_ind. move/negP: Hx; apply. rewrite -H; assumption.
        + apply/negP => Hd. move/negP: Hd12; apply.
          apply: is_empty_1 => v /memP Hv. move: (is_empty_2 Hd) => {Hd} Hemp.
          apply: (Hemp v). apply/memP. apply: (mem2_mem_inter (mem_inter_l Hv)).
          apply: mem_add_r. exact: (mem_inter_r Hv).
    Qed.

    Lemma disjoint_add_l x s1 s2 :
      disjoint (add x s1) s2 = ~~ mem x s2 && disjoint s1 s2.
    Proof.
      rewrite disjoint_sym disjoint_add_r disjoint_sym. reflexivity.
    Qed.

    Lemma disjoint_union_r (s1 s2 s3 : t) :
      disjoint s1 (union s2 s3) = disjoint s1 s2 && disjoint s1 s3.
    Proof.
      case H12: (disjoint s1 s2); case H13: (disjoint s1 s3) => /=.
      - apply: all_mem_disjoint => x Hmem1. apply/negP => Hmem23.
        case: (mem_union_or Hmem23) => Hmem.
        + move: (mem_disjoint_inl H12 Hmem1). move/negP; apply. exact: Hmem.
        + move: (mem_disjoint_inl H13 Hmem1). move/negP; apply. exact: Hmem.
      - apply/negP => H123. move/negP: H13; apply. apply: all_mem_disjoint => x Hmem1.
        apply/negP => Hmem3. move: (mem_disjoint_inl H123 Hmem1). move/negP; apply.
        apply: mem_union_r. exact: Hmem3.
      - apply/negP => H123. move/negP: H12; apply. apply: all_mem_disjoint => x Hmem1.
        apply/negP => Hmem2. move: (mem_disjoint_inl H123 Hmem1). move/negP; apply.
        apply: mem_union_l. exact: Hmem2.
      - apply/negP => H123. move/negP: H13; apply. apply: all_mem_disjoint => x Hmem1.
        apply/negP => Hmem3. move: (mem_disjoint_inl H123 Hmem1). move/negP; apply.
        apply: mem_union_r. exact: Hmem3.
    Qed.

    Lemma disjoint_union_l s1 s2 s3 :
      disjoint (union s1 s2) s3 = disjoint s1 s3 && disjoint s2 s3.
    Proof.
      rewrite disjoint_sym disjoint_union_r. rewrite !(@disjoint_sym s3).
      reflexivity.
    Qed.

    Lemma disjoint_diff_l (s1 s2 : t) : disjoint (diff s1 s2) s2.
    Proof.
      rewrite /disjoint. apply: is_empty_1. move=> x Hin.
      move: (inter_1 Hin) (inter_2 Hin) => Hin1 Hin2.
      apply: (diff_2 Hin1). exact: Hin2.
    Qed.

    Lemma disjoint_diff_r s1 s2 : disjoint s1 (diff s2 s1).
    Proof. rewrite disjoint_sym. exact: disjoint_diff_l. Qed.

    Lemma subset_union_disjoint_r (s1 s2 s3 : t) :
      subset s1 (union s2 s3) -> disjoint s1 s3 -> subset s1 s2.
    Proof.
      move=> Hsub Hd. apply: subset_1 => x /memP Hmem1. apply/memP.
      case: (mem_union_or (@mem_subset x _ _ Hmem1 Hsub)) => //=.
      move=> Hmem3. apply: False_ind. apply/negP/negPn: (mem_disjoint_inl Hd Hmem1).
      assumption.
    Qed.

    Lemma subset_union_disjoint_l (s1 s2 s3 : t) :
      subset s1 (union s2 s3) -> disjoint s1 s2 -> subset s1 s3.
    Proof. rewrite union_sym. exact: subset_union_disjoint_r. Qed.

    Lemma disjoint_empty_l (s : t) : disjoint empty s.
    Proof.
      rewrite /disjoint. apply: is_empty_1. apply: empty_inter_1.
      exact: empty_1.
    Qed.

    Lemma disjoint_empty_r s : disjoint s empty.
    Proof. rewrite disjoint_sym. exact: disjoint_empty_l. Qed.

    Lemma disjoint_subset_l s1 s2 s3 :
      disjoint s1 s2 -> subset s3 s1 -> disjoint s3 s2.
    Proof.
      move=> Hdisj Hsub. apply: all_mem_disjoint. move=> x Hmem3. apply/negP => Hmem2.
      move: (mem_disjoint_inr Hdisj Hmem2). move/negP; apply.
      exact: (mem_subset Hmem3 Hsub).
    Qed.

    Lemma disjoint_subset_r s1 s2 s3 :
      disjoint s1 s2 -> subset s3 s2 -> disjoint s1 s3.
    Proof.
      move=> Hdisj Hsub. apply: all_mem_disjoint. move=> x Hmem1. apply/negP => Hmem3.
      move: (mem_disjoint_inl Hdisj Hmem1). move/negP; apply.
      exact: (mem_subset Hmem3 Hsub).
    Qed.

    Hint Immediate disjoint_diff_l disjoint_diff_r disjoint_empty_l disjoint_empty_r : set.


    (* proper_subset *)

    Definition proper_subset (s1 s2 : t) := subset s1 s2 && ~~ equal s1 s2.

    Notation "s [<?] t" := (proper_subset s t) (at level 70, no associativity) : fset_scope.

    Lemma proper_subset_subset s1 s2 : proper_subset s1 s2 -> subset s1 s2.
    Proof. move/andP=> [? ?]; assumption. Qed.

    Lemma proper_subset_neq s1 s2 : proper_subset s1 s2 -> ~~ equal s1 s2.
    Proof. move/andP=> [? ?]; assumption. Qed.

    Lemma proper_subset_trans s1 s2 s3 :
      proper_subset s1 s2 -> proper_subset s2 s3 -> proper_subset s1 s3.
    Proof.
      move=> /andP [Hsub12 Hneq12] /andP [Hsub23 Hneq23]. rewrite /proper_subset.
      rewrite (subset_trans Hsub12 Hsub23) /=. apply/negP => /equal_2 Heq13.
      rewrite -> Heq13 in Hsub12. move: (subset_antisym Hsub23 Hsub12) => Heq23.
      move/negP: Hneq23; rewrite Heq23. by apply.
    Qed.

    Lemma proper_subset_subset_trans s1 s2 s3 :
      proper_subset s1 s2 -> subset s2 s3 -> proper_subset s1 s3.
    Proof.
      move=> /andP [Hsub12 Hneq12] Hsub23. rewrite /proper_subset.
      rewrite (subset_trans Hsub12 Hsub23) /=. apply/negP => /equal_2 Heq13.
      rewrite -> Heq13 in Hsub12. move: (subset_antisym Hsub23 Hsub12) => /equal_2 Heq23.
      move/negP: Hneq12; apply. rewrite Heq13 Heq23. exact: equal_refl.
    Qed.

    Lemma subset_proper_subset_trans s1 s2 s3 :
      subset s1 s2 -> proper_subset s2 s3 -> proper_subset s1 s3.
    Proof.
      move=> Hsub12 /andP [Hsub23 Hneq23]. rewrite /proper_subset.
      rewrite (subset_trans Hsub12 Hsub23) /=. apply/negP => /equal_2 Heq13.
      rewrite -> Heq13 in Hsub12. move: (subset_antisym Hsub23 Hsub12) => Heq23.
      move/negP: Hneq23; apply. exact: Heq23.
    Qed.

    Lemma proper_subset_irrefl s : proper_subset s s = false.
    Proof.
      apply/negP => /andP [Hsub Hneq]. rewrite equal_refl in Hneq. discriminate.
    Qed.

    Lemma proper_subset_antisym s1 s2 : proper_subset s1 s2 -> proper_subset s2 s1 = false.
    Proof.
      move=> Hsub12. apply/negP=> Hsub21. move: (proper_subset_trans Hsub12 Hsub21).
      rewrite proper_subset_irrefl. discriminate.
    Qed.

    Lemma proper_subset_cardinal s1 s2 :
      proper_subset s1 s2 -> cardinal s1 < cardinal s2.
    Proof.
      move/andP=> [Hsub Hne]. move: (subset_cardinal Hsub).
      rewrite leq_eqVlt. case/orP.
      - move=> /eqP H. move: (subset_cardinal_equal Hsub H) => {} H.
        rewrite H in Hne. discriminate.
      - by apply.
    Qed.

    Global Instance proper_subset_compat : Proper (Equal ==> Equal ==> Logic.eq) proper_subset.
    Proof.
      move=> s1 s2 Heq12 s3 s4 Heq34. rewrite /proper_subset.
      rewrite Heq12 Heq34. reflexivity.
    Qed.

    Lemma proper_subset_is_empty_l s1 s2 :
      is_empty s1 -> ~~ is_empty s2 -> proper_subset s1 s2.
    Proof.
      move=> /emptyP H1 H2. apply/andP; split.
      - apply/subsetP => x Hin1. apply: False_ind; exact: (H1 _ Hin1).
      - apply/negP => /equalP Heq. move/negP: H2; apply. rewrite -Heq.
        apply/emptyP. exact: H1.
    Qed.

    Lemma proper_subset_not_empty_r s1 s2 : proper_subset s1 s2 -> ~~ is_empty s2.
    Proof.
      move=> /andP [/subsetP Hsub Hneq]. apply/negP=> /emptyP Hemp.
      move/negP: Hneq; apply. apply/equalP => x. split.
      - move=> Hin1. exact: (Hsub _ Hin1).
      - move=> Hin2. apply: False_ind. exact: (Hemp _ Hin2).
    Qed.

    Lemma subset_not_mem_proper s1 s2 x :
      subset s1 s2 -> ~~ mem x s1 -> mem x s2 -> proper_subset s1 s2.
    Proof.
      move=> /subsetP Hsub Hmem1 Hmem2. apply/andP; split.
      - apply/subsetP. exact: Hsub.
      - apply/negP=> Heq. move/negP: Hmem1; apply.
        move/equalP: Heq => ->. exact: Hmem2.
    Qed.

    Lemma proper_subset_inter s1 s2 : proper_subset s1 s2 -> equal (inter s1 s2) s1.
    Proof.
      move=> /andP [/subsetP Hsub _]. apply/equalP. exact: (inter_Subset_Equal Hsub).
    Qed.

    Lemma proper_subset_union s1 s2 : proper_subset s1 s2 -> equal (union s1 s2) s2.
    Proof.
      move=> /andP [/subsetP Hsub _]. apply/equalP. exact: (union_Subset_Equal Hsub).
    Qed.

    Lemma proper_subset_subset_union s1 s2 s3 s4 :
      proper_subset s1 s2 -> subset s3 s4 -> subset (union s1 s3) (union s2 s4).
    Proof. move=> /andP [H1 _] H2. exact: (subset_unions H1 H2). Qed.

    Lemma subset_proper_subset_union s1 s2 s3 s4 :
      subset s1 s2 -> proper_subset s3 s4 -> subset (union s1 s3) (union s2 s4).
    Proof. move=> H1 /andP [H2 _]. exact: (subset_unions H1 H2). Qed.


    (* max_elt *)

    Lemma max_elt_mem (s : t) x :
      max_elt s = Some x -> mem x s.
    Proof. move=> H; apply/memP; exact: max_elt_1. Qed.

    Lemma max_elt_nlt (s : t) x y :
      max_elt s = Some x -> mem y s -> ~ olt x y.
    Proof. move=> H1 /memP H2; exact: (max_elt_2 H1 H2). Qed.

    Lemma max_elt_empty (s : t) : max_elt s = None -> is_empty s.
    Proof. move=> H; apply: is_empty_1; exact: max_elt_3 H. Qed.


    (* for_all *)

    Section ForAll.

      Variable f : elt -> bool.
      Variable compat : compat_bool oeq f.

      Lemma for_all_compat (s1 s2 : t) : Equal s1 s2 -> for_all f s1 = for_all f s2.
      Proof.
        move=> Heq. case H2: (for_all f s2).
        - apply: (for_all_1 compat). move=> x Hin. rewrite Heq in Hin.
          exact: (for_all_2 compat H2 Hin).
        - apply/negP=> H1. apply/negPf: H2. apply: (for_all_1 compat). move=> x Hin.
          rewrite <- Heq in Hin. exact: (for_all_2 compat H1 Hin).
      Qed.

      Lemma for_all_union (s1 s2 : t) :
        for_all f (union s1 s2) = (for_all f s1 && for_all f s2).
      Proof.
        case Hall1: (for_all f s1) => /=.
        - move: (for_all_2 compat Hall1) => {} Hall1. case Hall2: (for_all f s2).
          + apply: (for_all_1 compat).
            move=> x Hin. case: (union_1 Hin) => {} Hin.
            * exact: (Hall1 x Hin).
            * move: (for_all_2 compat Hall2) => {} Hall2. exact: (Hall2 x Hin).
          + apply/negP => Hunion. apply/negPf: Hall2.
            move: (for_all_2 compat Hunion) => {} Hunion.
            apply: (for_all_1 compat). move=> x Hin2.
            exact: (Hunion x (union_3 s1 Hin2)).
        - apply/negP=> Hunion. apply/negPf: Hall1.
          move: (for_all_2 compat Hunion) => {} Hunion.
          apply: (for_all_1 compat). move=> x Hin1.
          exact: (Hunion x (union_2 s2 Hin1)).
      Qed.

      Lemma for_all_subset (s1 s2 : t) :
        subset s1 s2 -> for_all f s2 -> for_all f s1.
      Proof.
        move=> Hsub Hall2. move: (for_all_2 compat Hall2) => {} Hall2.
        apply: (for_all_1 compat). move=> x Hin1.
        move: (subset_2 Hsub) => {} Hsub. move: (Hsub x Hin1) => Hin2.
        exact: (Hall2 x Hin2).
      Qed.

      Lemma for_all_singleton x : for_all (t:=t) f (singleton x) = f x.
      Proof.
        case H: (f x).
        - apply: (for_all_1 compat). move=> y /memP Hiny.
          move: (mem_singleton_eq Hiny) => Heqy. rewrite (compat Heqy). assumption.
        - apply/negP=> Hall. apply/negPf: H. move: (for_all_2 compat Hall) => {} Hall.
          move: (eq_mem_singleton (OrderedType.eq_refl _ x)) => /memP Hin.
          exact: (Hall x Hin).
      Qed.

      Lemma for_all_Add x (s1 s2 : t) :
        Add x s1 s2 -> for_all f s2 = f x && for_all f s1.
      Proof.
        move=> Hadd. case H: (f x && for_all f s1).
        - move/andP: H => [Hfv Hall]. move: (for_all_2 compat Hall) => {} Hall.
          apply: (for_all_1 compat) => y /(Hadd y) Hiny. case: Hiny => Hiny.
          + rewrite -(compat Hiny). assumption.
          + exact: (Hall y Hiny).
        - apply/negP=> Hall. apply/negPf: H.
          move: (for_all_2 compat Hall) => {} Hall. apply/andP; split.
          + move: (Hadd x) => [H1 H2]. exact: (Hall x (H2 (or_introl (OrderedType.eq_refl _ x)))).
          + apply: (for_all_1 compat) => y Hiny. move: (Hadd y) => [H1 H2].
            exact: (Hall y (H2 (or_intror Hiny))).
      Qed.

      Lemma for_all_add x (s : t) : for_all f (add x s) = f x && for_all f s.
      Proof. exact: (for_all_Add (Add_add _ _)). Qed.

      Lemma for_all_inter_l (s1 s2 : t) :
        for_all f s1 -> for_all f (inter s1 s2).
      Proof.
        move=> H. move: (for_all_2 compat H) => {}H.
        apply: (for_all_1 compat) => x Hin. exact: (H x (inter_1 Hin)).
      Qed.

      Lemma for_all_inter_r (s1 s2 : t) :
        for_all f s2 -> for_all f (inter s1 s2).
      Proof. rewrite (for_all_compat (inter_sym s1 s2)). exact: for_all_inter_l. Qed.

      Lemma for_all_mem x (s : t) : for_all f s -> mem x s -> f x.
      Proof. move/(for_all_2 compat)=> Hall /memP Hin. exact: (Hall x Hin). Qed.

    End ForAll.


    (* foldl *)

    Section FoldUnion.

      Variable T : Type.

      Variable f : T -> t.

      Lemma mem_foldl_union x (r : t) (s : seq T) :
        mem x (foldl (fun res a => union (f a) res) r s) =
          mem x r || mem x (foldl (fun res a => union (f a) res) empty s).
      Proof.
        elim: s r => /=.
        - move=> r. rewrite mem_empty orbF. reflexivity.
        - move=> s_hd s_tl IH r. rewrite (IH (union (f s_hd) r)).
          rewrite mem_union. rewrite (orb_comm (mem x (f s_hd))). rewrite -orb_assoc.
          rewrite -{1}(union_empty_r (f s_hd)). rewrite -IH. reflexivity.
      Qed.

      Lemma foldl_union_swap (r1 r2 : t) (s : seq T) :
        Equal r1 r2 ->
        Equal (foldl (fun res a => union (f a) res) r1 s)
              (foldl (fun res a => union (f a) res) r2 s).
      Proof.
        move=> Hr x. move: (Hr x) => [H1 H2]. split => /memP Hf.
        - apply/memP. rewrite mem_foldl_union. rewrite mem_foldl_union in Hf.
          case/orP: Hf => H.
          + by move/memP: H => H; move: (H1 H) => {H} /memP ->.
          + by rewrite H orbT.
        - apply/memP. rewrite mem_foldl_union. rewrite mem_foldl_union in Hf.
          case/orP: Hf => H.
          + by move/memP: H => H; move: (H2 H) => {H} /memP ->.
          + by rewrite H orbT.
      Qed.

      Lemma foldl_union_cons (x : T) (s : seq T) (r : t) :
        Equal
          (foldl (fun res a => union (f a) res) r (x::s))
          (union (f x) (foldl (fun res a => union (f a) res) r s)).
      Proof.
        apply: (foldl_cons (R := Equal)).
        - move=> a1 a2 b. rewrite -union_assoc. rewrite (union_sym (f a2)).
          rewrite union_assoc. reflexivity.
        - exact: foldl_union_swap.
      Qed.

    End FoldUnion.


    (* inclA *)

    Lemma Subset_inclA (s1 s2 : t) :
      Subset s1 s2 -> inclA oeq (elements s1) (elements s2).
    Proof.
      move=> Hsub x /elements_iff H1. apply/elements_iff. exact: (Hsub _ H1).
    Qed.

    Lemma Equal_inclA (s1 s2 : t) :
      Equal s1 s2 -> inclA oeq (elements s1) (elements s2).
    Proof.
      move=> Heq x /elements_iff H1. apply/elements_iff. by rewrite <- Heq.
    Qed.


  End FSetTypeLemmas.

  Notation "s [o] t" := (disjoint s t) (at level 70, no associativity) : fset_scope.
  Notation "s [<?] t" := (proper_subset s t) (at level 70, no associativity) : fset_scope.
  Global Hint Resolve mem_singleton_eq eq_mem_singleton : set.
  Global Hint Resolve not_mem_singleton_neq neq_not_mem_singleton : set.
  Global Hint Resolve mem_add_or mem_add_l mem_add_r : set.
  Global Hint Resolve neq_not_mem_add : set.
  Global Hint Resolve mem_union_l mem_union_r : set.
  Global Hint Resolve not_mem_union : set.
  Global Hint Immediate subset_l_union subset_r_union : set.
  Global Hint Resolve mem_subset_singleton : set.
  Global Hint Resolve subset_unions subset_union_l subset_union_r subset_union_2l : set.
  Global Hint Resolve subset_add_l subset_add_r : set.
  Global Hint Resolve eq_not_mem_remove neq_mem_remove : set.
  Global Hint Resolve subset_union_diff_l subset_union_diff_r : set.
  Global Hint Resolve mem2_mem_inter : set.
  Global Hint Immediate disjoint_diff_l disjoint_diff_r disjoint_empty_l disjoint_empty_r : set.
  Global Hint Immediate for_all_inter_l for_all_inter_r : set.

  (* Tactics *)

  Ltac all2mem :=
    repeat
      match goal with
      | H : context [_ \in _] |- _ => rewrite oin_set in H
      | |- context [_ \in _] => rewrite oin_set
      | H : context [In _ _] |- _ => move/memP: H => H
      | |- context [In _ _] => apply/memP
      | H : context [_ \in elements _] |- _ => rewrite oin_elements in H
      | |- context [_ \in elements _] => rewrite oin_elements
      | H : context [InA _ _ (elements _)] |- _ => move/memPa: H => H
      | |- context [InA _ _ (elements _)] => apply/memPa
      end.

  Ltac all2in :=
    repeat
      match goal with
      | H : context [_ \in _] |- _ => rewrite oin_set in H; move/memP: H => H
      | |- context [_ \in _] => rewrite oin_set; apply/memP
      | H : context [mem _ _] |- _ => move/memP: H => H
      | |- context [mem _ _] => apply/memP
      | H : context [_ \in elements _] |- _ => move/inPo: H => H
      | |- context [_ \in elements _] => apply/inPo
      | H : context [InA _ _ (elements _)] |- _ => move/inPa: H => H
      | |- context [InA _ _ (elements _)] => apply/inPa
      end.

  Ltac dp_mem :=
    match goal with
    | |- mem _ _ = true => apply/idP; dp_mem
    (* *)
    | H : is_true (mem ?x ?s) |- is_true (mem ?x ?s) => exact: H
    | H : ?x = ?y |- ?x = ?y => exact: H
    | H : ?x = ?y |- is_true (?x == ?y) => apply/eqtype.eqP; exact: H
    | H : is_true (?x == ?y) |- ?x = ?y => exact: (eqtype.eqP H)
    | H : is_true (?x == ?y) |- is_true (?x == ?y) => exact: H
    | H : oeq ?x ?y |- oeq ?x ?y => exact: H
    | |- ?x = ?x => reflexivity
    | |- is_true (?x == ?x) => exact: eqxx
    | |- oeq ?x ?x => exact: OrderedType.eq_refl
    | H1 : is_true (mem ?x ?s1), H2 : is_true (subset ?s1 ?s2) |-
        is_true (mem ?x ?s2) =>
        exact: (mem_subset H1 H2)
    (* *)
    | H : is_true (mem ?x (singleton ?y)) |- is_true (mem ?x _) =>
        move: (mem_singleton_eq H) => {} H; dp_mem
    | H : is_true (mem ?x (add ?y ?s)) |- is_true (mem ?x _) =>
        move: (mem_add_or H) => {H} [] H; dp_mem
    | H : is_true (mem ?x (union ?s1 ?s2)) |- is_true (mem ?x _) =>
        move: (mem_union_or H) => {H} [] H; dp_mem
    (* *)
    | |- is_true (mem ?x (singleton ?y)) =>
        apply: eq_mem_singleton; dp_mem
    | |- is_true (mem ?x (add ?y ?s)) =>
        first [ apply: mem_add_l; by dp_mem | apply: mem_add_r; by dp_mem ]
    | |- is_true (mem ?x (union ?s1 ?s2)) =>
        first [ apply: mem_union_l; by dp_mem | apply: mem_union_r; by dp_mem ]
    (* *)
    | H : is_true (subset (singleton _) _) |- _ =>
        move: (subset_singleton_mem H) => {} H; dp_mem
    | H : is_true (subset (add _ _) _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        move: (subset_add_ll H) (subset_add_lr H) => {H} H1 H2; dp_mem
    | H : is_true (subset (union _ _) _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        move: (subset_union_ll H) (subset_union_lr H) => {H} H1 H2; dp_mem
    (* *)
    | H : is_true (_ && _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        move/andP: H => [H1 H2]; dp_mem
    | H : _ /\ _ |- _ =>
        let H1 := fresh in
        let H2 := fresh in
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
    | |- subset _ _ = true => apply/idP; dp_subset
    | |- is_true (subset empty _) => exact: subset_empty_l
    | H : is_true (subset ?x ?y) |- is_true (subset ?x ?y) => exact: H
    | |- is_true (subset ?x ?x) => exact: subset_refl
    | H1 : is_true (subset ?s1 ?s2), H2 : is_true (subset ?s2 ?s3) |-
        is_true (subset ?s1 ?s3) =>
        exact: (subset_trans H1 H2)
    (* *)
    | H : is_true (subset (singleton _) _) |- _ =>
        move: (subset_singleton_mem H) => {} H; dp_subset
    | H : is_true (subset (add _ _) _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        move: (subset_add_ll H) (subset_add_lr H) => {H} H1 H2; dp_subset
    | H : is_true (subset (union _ _) _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        move: (subset_union_ll H) (subset_union_lr H) => {H} H1 H2; dp_subset
    (* *)
    | |- is_true (subset (singleton _) _) =>
        apply: mem_subset_singleton; dp_mem
    | |- is_true (subset (add _ _) _) =>
        apply: subset_add_l; [ dp_mem | dp_subset ]
    | |- is_true (subset (union _ _) _) =>
        apply: subset_union_2l; dp_subset
    (* *)
    | |- is_true (subset _ (add _ _)) =>
        apply: subset_add_r; dp_subset
    | |- is_true (subset _ (union _ _)) =>
        first [ apply: subset_union_l; by dp_subset |
                apply: subset_union_r; by dp_subset ]
    (* *)
    | H : is_true (_ && _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        move/andP: H => [H1 H2]; dp_subset
    | H : _ /\ _ |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        move: H => [H1 H2]; dp_subset
    (* *)
    | H : is_true (_ || _) |- _ =>
        move/orP: H => [] H; dp_subset
    | H : _ \/ _ |- _ =>
        move: H => [] H; dp_subset
    end.

  Ltac dp_Equal :=
    apply: Subset_antisym; apply: subset_2; dp_subset.

  Ltac simpl_union :=
    repeat
      match goal with
      | H : context [union empty _] |- _ => rewrite union_empty_l in H
      | |- context [union empty _] => rewrite union_empty_l
      | H : context [union _ empty] |- _ => rewrite union_empty_r in H
      | |- context [union _ empty] => rewrite union_empty_r
      | H1 : Empty ?s1, H2 : context [union ?s1 ?s2] |- _ =>
          rewrite (empty_union_1 s2 H1) in H2
      | H1 : Empty ?s2, H2 : context [union ?s1 ?s2] |- _ =>
          rewrite (empty_union_2 s1 H1) in H2
      | H : Empty ?s1 |- context [union ?s1 ?s2] =>
          rewrite (empty_union_1 s2 H)
      | H : Empty ?s2 |- context [union ?s1 ?s2] =>
          rewrite (empty_union_2 s1 H)
      end.

  Ltac simpl_cardinal :=
    repeat
      match goal with
      | H : context [cardinal empty] |- _ => rewrite empty_cardinal in H
      | |- context [cardinal empty] => rewrite empty_cardinal
      | H1 : Empty ?s, H2 : context [cardinal ?s] |- _ =>
          rewrite (cardinal_1 H1) in H2
      | H : Empty ?s |- context [cardinal ?s] => rewrite (cardinal_1 H)
      | H1 : ~ In ?x ?s, H2 : Add ?x ?s ?s', H3 : context [cardinal ?s'] |- _ =>
          rewrite (cardinal_2 H1 H2) in H3
      | H1 : ~ In ?x ?s, H2 : Add ?x ?s ?s' |- context [cardinal ?s'] =>
          rewrite (cardinal_2 H1 H2)
      | H1 : In ?x ?s, H2 : context [cardinal (add ?x ?s)] |- _ =>
          rewrite (add_cardinal_1 H1) in H2
      | H : In ?x ?s |- context [cardinal (add ?x ?s)] =>
          rewrite (add_cardinal_1 H)
      | H1 : ~ In ?x ?s, H2 : context [cardinal (add ?x ?s)] |- _ =>
          rewrite (add_cardinal_2 H1) in H2
      | H : ~ In ?x ?s |- context c [cardinal (add ?x ?s)] =>
          rewrite (add_cardinal_2 H)
      end.


  (** Map a set of type A to another set of type B *)

  Section FSetMap.

    Context {A B : orderedType}.
    Context {sA : fsetType A} {sB : fsetType B}.
    Context (f : A -> B).

    Definition compatA : Prop := Proper (oeq ==> oeq) f.

    Definition injectiveA : Prop := oinjective f.

    Record wf_fsetmap : Prop :=
      mkWfFSetMap { f_compat : compatA
                  ; f_injective : injectiveA }.

    Context (f_wf : wf_fsetmap).

    Definition fsetmap (s : sA) : sB := of_list (map f (elements s)).

    Lemma inA_map_compat x s :
      InA oeq x s -> InA oeq (f x) (map f s).
    Proof.
      elim: s x => [| a s IH] x Hin /=.
      - by inversion Hin.
      - case/InA_cons: Hin => Hin.
        + apply: InA_cons_hd. exact: (f_compat f_wf).
        + apply: InA_cons_tl. exact: (IH _ Hin).
    Qed.

    Lemma inA_map_injective x s :
      InA oeq (f x) (map f s) -> InA oeq x s.
    Proof.
      elim: s x => [| a s IH] x Hin /=.
      - by inversion Hin.
      - case/InA_cons: Hin => Hin.
        + apply: InA_cons_hd. exact: (f_injective f_wf Hin).
        + apply: InA_cons_tl. exact: (IH _ Hin).
    Qed.

    Lemma inA_map_exists x s :
      InA oeq x (map f s) -> exists y, oeq x (f y) /\ InA oeq y s.
    Proof.
      elim: s x => [| a s IH] x Hin /=.
      - by inversion Hin.
      - case/InA_cons: Hin => Hin.
        + exists a; split; first assumption. apply: InA_cons_hd.
          exact: OrderedType.eq_refl.
        + move: (IH _ Hin) => [y [Heq HinA]].
          exists y; split; first assumption. exact: InA_cons_tl.
    Qed.

    Lemma Empty_Empty_fsetmap s : Empty s -> Empty (fsetmap s).
    Proof.
      rewrite /fsetmap => Hemp1 x Hin. move: (elements_Empty s) => [H _].
      rewrite (H Hemp1) /= in Hin => {H}. apply/(empty_iff x). exact: Hin.
    Qed.

    Lemma Empty_fsetmap_Empty s : Empty (fsetmap s) -> Empty s.
    Proof.
      rewrite /fsetmap => Hemp1 x Hin. apply: (Hemp1 (f x)).
      apply: inA_in_of_list. apply: inA_map_compat. exact: (elements_1 Hin).
    Qed.

    Hint Resolve Empty_Empty_fsetmap : fset.

    Lemma Empty_fsetmap_iff s : Empty (fsetmap s) <-> Empty s.
    Proof. split; auto with fset. exact: Empty_fsetmap_Empty. Qed.

    Lemma mem_fsetmap a s : mem (f a) (fsetmap s) = mem a s.
    Proof.
      rewrite /fsetmap. case Hmem1: (mem a s).
      - apply: inA_mem_of_list. apply: inA_map_compat.
        move/memP: Hmem1 => Hin1. exact: (elements_1 Hin1).
      - apply/negP => Hmem2. apply/negPf: Hmem1. move: (mem_of_list_inA Hmem2) => HinA.
        move: (inA_map_injective HinA) => {} HinA. apply/memP. exact: (elements_2 HinA).
    Qed.

    Lemma mem_fsetmap_exists b s :
      mem b (fsetmap s) -> exists a, oeq b (f a) /\ mem a s.
    Proof.
      rewrite /fsetmap => Hmem. move: (mem_of_list_inA Hmem) => {Hmem} HinA.
      move: (inA_map_exists HinA) => {HinA} [a [Heq HinA]].
      exists a; split; first assumption. apply/memP. exact: elements_2.
    Qed.

    Lemma fsetmap_singleton a :
      Equal (fsetmap (singleton a)) (singleton (f a)).
    Proof.
      move=> x; split => /memP Hmem; apply: memP.
      - move: (mem_fsetmap_exists Hmem) => [y [Hy Hmemy]].
        apply: eq_mem_singleton. rewrite Hy.
        exact: (f_compat _ (mem_singleton_eq Hmemy)).
      - rewrite (mem_singleton_eq Hmem) mem_fsetmap.
        apply: eq_mem_singleton. reflexivity.
    Qed.

    Lemma fsetmap_add a s :
      Equal (fsetmap (add a s)) (add (f a) (fsetmap s)).
    Proof.
      move=> x; split; move=> /memP Hmem; apply/memP.
      - move: (mem_fsetmap_exists Hmem) => [y [Hfy Hmemy]].
        case: (mem_add_or Hmemy) => {Hmemy} Hy.
        + rewrite Hfy. apply: mem_add_l. exact: (f_compat _ Hy).
        + apply: mem_add_r. rewrite Hfy mem_fsetmap. assumption.
      - case: (mem_add_or Hmem) => {Hmem} Hx.
        + rewrite Hx mem_fsetmap. apply: mem_add_l. reflexivity.
        + move: (mem_fsetmap_exists Hx) => [y [Hfy Hmemy]]. rewrite Hfy mem_fsetmap.
          apply: mem_add_r. assumption.
    Qed.

    Lemma fsetmap_union s1 s2 :
      Equal (fsetmap (union s1 s2)) (union (fsetmap s1) (fsetmap s2)).
    Proof.
      move=> x; split; move=> /memP Hmem; apply/memP.
      - move: (mem_fsetmap_exists Hmem) => [y [Hy Hmemy]].
        case: (mem_union_or Hmemy) => {} Hmemy.
        + apply: mem_union_l. rewrite Hy mem_fsetmap. assumption.
        + apply: mem_union_r. rewrite Hy mem_fsetmap. assumption.
      - case: (mem_union_or Hmem) => {Hmem} Hmemx.
        + move: (mem_fsetmap_exists Hmemx) => [y [Hy Hmemy]].
          rewrite Hy mem_fsetmap. apply/mem_union_l; assumption.
        + move: (mem_fsetmap_exists Hmemx) => [y [Hy Hmemy]].
          rewrite Hy mem_fsetmap. apply/mem_union_r; assumption.
    Qed.

    Lemma mem_fsetmap_union b s1 s2 :
      mem b (fsetmap (union s1 s2)) =
        (mem b (fsetmap s1)) || (mem b (fsetmap s2)).
    Proof. rewrite fsetmap_union. rewrite union_b. reflexivity. Qed.

    Lemma mem_fsetmap_union_or b s1 s2 :
      mem b (fsetmap (union s1 s2)) ->
      mem b (fsetmap s1) \/ mem b (fsetmap s2).
    Proof.
      rewrite fsetmap_union => Hmem. case: (mem_union_or Hmem); [by left | by right].
    Qed.

    Lemma mem_fsetmap_union_l b s1 s2 :
      mem b (fsetmap s1) -> mem b (fsetmap (union s1 s2)).
    Proof. rewrite mem_fsetmap_union. by move=> ->. Qed.

    Lemma mem_fsetmap_union_r b s1 s2 :
      mem b (fsetmap s2) -> mem b (fsetmap (union s1 s2)).
    Proof. rewrite mem_fsetmap_union. by move=> ->; rewrite orbT. Qed.

    Lemma subset_fsetmap s1 s2 :
      subset (fsetmap s1) (fsetmap s2) = subset s1 s2.
    Proof.
      case H: (subset s1 s2).
      - apply: subset_1 => x /memP Hmem. apply/memP.
        move: (mem_fsetmap_exists Hmem) => {Hmem} [fx [Heq Hmem]].
        rewrite Heq mem_fsetmap. exact: (mem_subset Hmem H).
      - apply/negP => Hsubset. apply/negPf: H.
        apply: subset_1 => x /memP Hmem. apply/memP.
        rewrite -mem_fsetmap. apply: (mem_subset _ Hsubset).
        rewrite mem_fsetmap. assumption.
    Qed.

  End FSetMap.

  Notation "{ 'set' E | i <- s }" := (fsetmap (fun i => E) s)
                                       (at level 0, E at level 99, i name,
                                         format "{ '[hv'  'set'  E '/'  |  i  <-  s  } ']'") : fset_scope.

  Global Hint Resolve Empty_Empty_fsetmap : set.
  Global Hint Immediate mem_fsetmap_union_l mem_fsetmap_union_r : set.

End FSetTypeLemmas.


(** * Collection of definitions and lemmas *)

Module FSets.
  Module D := FSetType.Exports.
  Module F := FSetTypeFacts.
  Module P := FSetTypeWProperties.
  Module OP := FSetTypeOrdProperties.
  Module L := FSetTypeLemmas.
  Include D.
  Include F.
  Include L.
End FSets.


(** * FSetInterface.S is a fsetType *)

Module FSet_as_FSetType
       (E : Ordered)
       (S : FSetInterface.S with Module E := E).

  Definition fset_mixin :=
    @FSetMixin E.T S.t S.In S.empty S.is_empty S.mem S.add S.singleton
               S.remove S.union S.inter S.diff S.eq_dec S.equal S.subset
               S.fold S.for_all S.exists_ S.filter S.partition S.cardinal
               S.elements S.choose S.In_1 S.eq_refl S.eq_sym S.eq_trans
               S.mem_1 S.mem_2 S.equal_1 S.equal_2 S.subset_1 S.subset_2
               S.empty_1 S.is_empty_1 S.is_empty_2 S.add_1 S.add_2 S.add_3
               S.remove_1 S.remove_2 S.remove_3 S.singleton_1 S.singleton_2
               S.union_1 S.union_2 S.union_3 S.inter_1 S.inter_2 S.inter_3
               S.diff_1 S.diff_2 S.diff_3 S.fold_1 S.cardinal_1
               S.filter_1 S.filter_2 S.filter_3 S.for_all_1 S.for_all_2
               S.exists_1 S.exists_2 S.partition_1 S.partition_2
               S.elements_1 S.elements_2 S.elements_3w S.choose_1 S.choose_2
               S.lt S.compare S.min_elt S.max_elt S.lt_trans S.lt_not_eq
               S.elements_3 S.min_elt_1 S.min_elt_2 S.min_elt_3
               S.max_elt_1 S.max_elt_2 S.max_elt_3 S.choose_3.

  Global Canonical fset_type := Eval hnf in @FSetType E.T S.t fset_mixin.

End FSet_as_FSetType.


(* Sets that can generate new elements. *)

Module FSet_as_FSetTypeWithDefaultSucc
       (E : OrderedWithDefaultSucc)
       (S : FSetInterface.S with Module E := E).

  Module SS := FSet_as_FSetType E S.
  Include SS.

  Definition new_elt (s : S.t) : E.t :=
    match max_elt s with
    | Some x => E.succ x
    | None => E.default
    end.

  Lemma new_elt_is_new : forall (s : S.t), ~~ mem (new_elt s) s.
  Proof.
    move=> s. apply/negP => Hmem. move/mem_2: Hmem.
    rewrite /new_elt. case H: (max_elt s) => Hin.
    - apply: (max_elt_2 H Hin). exact: E.lt_succ.
    - move: (max_elt_3 H) => {} H. apply: (H E.default). assumption.
  Qed.

End FSet_as_FSetTypeWithDefaultSucc.
