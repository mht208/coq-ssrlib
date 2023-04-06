
(**
   A structure [fmapType] is defined in the module [FM]. The structure
   [fmapType] contains the interface from Coq's [FMapInterface.S].
   Keys in [fmapType] are of type [orderedType].
   Functors for converting [FMapInterface.S] to [fmapType] are provided.
   - [FMapInterface_as_FM]
   - [FMapInterface_as_FM_WDS]
   In [FMapInterface_as_FM_WDS], a default element and a successor function
   must be provided to generate new keys with respect to a map by [new_key].

   Lemmas from Coq about [FMapInterface.S] are defined for [fmapType] in
   the following modules.
   - [F]: lemmas from [FMapFacts.Facts]
   - [P]: lemmas from [FMapFacts.Properties]
   - [OP]: lemmas from [FMapFacts.OrdProperties]

   Additional lemmas about [fmapType] are provided in the module [L], which
   includes [F] and [OP].

   Below is a list of conversions between various membership tests:
<<
                        memP
            mem k m *********** In k m
               *
               *
        memPks *
               *
               *
      FS.mem k (key_set m)
>>

*)

From Coq Require Import Arith FMaps Bool DecidableType DecidableTypeEx OrderedType List Morphisms.
From ssrlib Require Import Tactics Sets Orders.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Declare Scope fmap_scope.
Delimit Scope fmap_scope with FM.


(** ** fmapType: a finite map as a structure *)

Module FM.

  Local Open Scope ordered_scope.

  Import O.

  Module ClassDef.

    Structure mixin_of (key : orderedType) (t : Type -> Type) :=
      Mixin { (* WSfun *)
          empty : forall elt : Type, t elt
        ; is_empty : forall elt : Type, t elt -> bool
        ; add : forall elt : Type, key -> elt -> t elt -> t elt
        ; find : forall elt : Type, key -> t elt -> option elt
        ; remove : forall elt : Type, key -> t elt -> t elt
        ; mem : forall elt : Type, key -> t elt -> bool
        ; map : forall elt elt' : Type, (elt -> elt') -> t elt -> t elt'
        ; mapi : forall elt elt' : Type, (key -> elt -> elt') -> t elt -> t elt'
        ; map2 :
          forall elt elt' elt'' : Type,
            (option elt -> option elt' -> option elt'') -> t elt -> t elt' ->  t elt''
        ; elements : forall elt : Type, t elt -> list (key * elt)
        ; cardinal : forall elt : Type, t elt -> nat
        ; fold : forall elt A: Type, (key -> elt -> A -> A) -> t elt -> A -> A
        ; equal : forall elt : Type, (elt -> elt -> bool) -> t elt -> t elt -> bool
        ; MapsTo : forall elt : Type, key -> elt -> t elt -> Prop
        ; In : forall elt : Type, key -> t elt -> Prop :=
          fun (elt : Type) (k : key) (m : t elt) => exists e : elt, MapsTo k e m
        ; Empty : forall elt : Type, t elt -> Prop :=
          fun (elt : Type) (m : t elt) => forall (a : key) (e : elt), ~ MapsTo a e m
        ; eq_key : forall elt : Type, key * elt -> key * elt -> Prop :=
          fun (elt : Type) (p p' : key * elt) => (fst p) == (fst p')
        ; eq_key_elt : forall elt : Type, key * elt -> key * elt -> Prop :=
          fun (elt : Type) (p p' : key * elt) => (fst p) == (fst p') /\ (snd p) = (snd p')
        ; MapsTo_1 :
          forall (elt : Type) (m : t elt) (x y : key) (e : elt),
            x == y -> MapsTo x e m -> MapsTo y e m
        ; mem_1 : forall (elt : Type) (m : t elt) (x : key), In x m -> mem x m = true
        ; mem_2 : forall (elt : Type) (m : t elt) (x : key), mem x m = true -> In x m
        ; empty_1 : forall elt : Type, Empty (empty elt)
        ; is_empty_1 : forall (elt : Type) (m : t elt), Empty m -> is_empty m = true
        ; is_empty_2 : forall (elt : Type) (m : t elt), is_empty m = true -> Empty m
        ; add_1 :
          forall (elt : Type) (m : t elt) (x y : key) (e : elt),
            x == y -> MapsTo y e (add x e m)
        ; add_2 :
          forall (elt : Type) (m : t elt) (x y : key) (e e' : elt),
            ~ x == y -> MapsTo y e m -> MapsTo y e (add x e' m)
        ; add_3 :
          forall (elt : Type) (m : t elt) (x y : key) (e e' : elt),
            ~ x == y -> MapsTo y e (add x e' m) -> MapsTo y e m
        ; remove_1 : forall (elt : Type) (m : t elt) (x y : key), x == y -> ~ In y (remove x m)
        ; remove_2 :
          forall (elt : Type) (m : t elt) (x y : key) (e : elt),
            ~ x == y -> MapsTo y e m -> MapsTo y e (remove x m)
        ; remove_3 :
          forall (elt : Type) (m : t elt) (x y : key) (e : elt),
            MapsTo y e (remove x m) -> MapsTo y e m
        ; find_1 :
          forall (elt : Type) (m : t elt) (x : key) (e : elt),
            MapsTo x e m -> find x m = Some e
        ; find_2 :
          forall (elt : Type) (m : t elt) (x : key) (e : elt),
            find x m = Some e -> MapsTo x e m
        ; elements_1 :
          forall (elt : Type) (m : t elt) (x : key) (e : elt),
            MapsTo x e m -> InA (@eq_key_elt elt) (x, e) (elements m)
        ; elements_2 :
          forall (elt : Type) (m : t elt) (x : key) (e : elt),
            InA (@eq_key_elt elt) (x, e) (elements m) -> MapsTo x e m
        ; elements_3w : forall (elt : Type) (m : t elt), NoDupA (@eq_key elt) (elements m)
        ; cardinal_1 : forall (elt : Type) (m : t elt), cardinal m = length (elements m)
        ; fold_1 :
          forall (elt : Type) (m : t elt) (A : Type) (i : A) (f : key -> elt -> A -> A),
            fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i
        ; Equal : forall (elt : Type), t elt -> t elt -> Prop :=
          fun (elt : Type) (m m' : t elt) => forall y, find y m = find y m'
        ; Equiv :
          forall (elt : Type), (elt -> elt -> Prop) -> t elt -> t elt -> Prop :=
          fun (elt : Type) (eq_elt : elt -> elt -> Prop) m m' =>
            (forall k, In k m <-> In k m') /\
              (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e')
        ; Equivb :
          forall (elt : Type), (elt -> elt -> bool) -> t elt -> t elt -> Prop :=
          fun (elt : Type) (cmp: elt -> elt -> bool) => Equiv (Cmp cmp)
        ; equal_1 :
          forall (elt : Type) (m m' : t elt) (cmp : elt -> elt -> bool),
            Equivb cmp m m' -> equal cmp m m' = true
        ; equal_2 :
          forall (elt : Type) (m m' : t elt) (cmp : elt -> elt -> bool),
            equal cmp m m' = true -> Equivb cmp m m'
        ; map_1 :
          forall (elt elt' : Type) (m : t elt) (x : key) (e : elt) (f : elt -> elt'),
            MapsTo x e m -> MapsTo x (f e) (map f m)
        ; map_2 :
          forall (elt elt' : Type) (m : t elt) (x : key) (f : elt -> elt'),
            In x (map f m) -> In x m
        ; mapi_1 :
          forall (elt elt' : Type) (m : t elt) (x : key) (e : elt)
                 (f : key -> elt -> elt'), MapsTo x e m ->
                                           exists y, y == x /\ MapsTo x (f y e) (mapi f m)
        ; mapi_2 :
          forall (elt elt' : Type) (m : t elt) (x : key)
                 (f : key -> elt -> elt'), In x (mapi f m) -> In x m
        ; map2_1 :
          forall (elt elt' elt'' : Type) (m : t elt) (m' : t elt')
                 (x : key) (f : option elt -> option elt' -> option elt''),
            In x m \/ In x m' ->
            find x (map2 f m m') = f (find x m) (find x m')
        ; map2_2 :
          forall (elt elt' elt'' : Type) (m : t elt) (m' : t elt')
                 (x : key) (f : option elt -> option elt' -> option elt''),
            In x (map2 f m m') -> In x m \/ In x m'
        (* Sfun *)
        ; lt_key :
          forall (elt : Type), key * elt -> key * elt -> Prop :=
          fun (elt : Type) (p p' : key * elt) => (fst p) < (fst p')
        ; elements_3 : forall (elt : Type) (m : t elt), Sorted.sort (@lt_key elt) (elements m)
        }.
    Notation class_of := mixin_of (only parsing).

    Section Def.

      Structure type (key : orderedType) : Type :=
        Pack { sort; _ : class_of key sort }.

      Local Coercion sort : type >-> Funclass.

      Definition sort_type (key : orderedType) (elt : Type) (m : type key) : Type :=
        (sort m) elt.

      Local Coercion sort_type : type >-> Sortclass.

      Variables (key : orderedType) (cT : type key).

      Definition class := let: Pack _ c := cT return class_of key cT in c.

    End Def.

  End ClassDef.

  Import ClassDef.

  Module Exports.

    Coercion sort : type >-> Funclass.
    Coercion sort_type : type >-> Sortclass.
    Notation fmapType := type.
    Notation FMapMixin := Mixin.
    Notation FMapType key map m := (@Pack key map m).

  End Exports.

  Import Exports.

  Section Definitions.
    Context {key : orderedType}.
    Context {t : fmapType key}.

    Definition empty : forall elt : Type, t elt := empty (class t).
    Definition is_empty : forall elt : Type, t elt -> bool := is_empty (class t).
    Definition add : forall elt : Type, key -> elt -> t elt -> t elt := add (class t).
    Definition find : forall elt : Type, key -> t elt -> option elt := find (class t).
    Definition remove : forall elt : Type, key -> t elt -> t elt := remove (class t).
    Definition mem : forall elt : Type, key -> t elt -> bool := mem (class t).
    Definition map : forall elt elt' : Type, (elt -> elt') -> t elt -> t elt' := map (class t).
    Definition mapi : forall elt elt' : Type, (key -> elt -> elt') -> t elt -> t elt' := mapi (class t).
    Definition map2 :
      forall elt elt' elt'' : Type,
        (option elt -> option elt' -> option elt'') -> t elt -> t elt' ->  t elt'' :=
      map2 (class t).
    Definition elements : forall elt : Type, t elt -> list (key * elt) := elements (class t).
    Definition cardinal : forall elt : Type, t elt -> nat := cardinal (class t).
    Definition fold : forall elt A: Type, (key -> elt -> A -> A) -> t elt -> A -> A := fold (class t).
    Definition equal : forall elt : Type, (elt -> elt -> bool) -> t elt -> t elt -> bool := equal (class t).
    Definition MapsTo : forall elt : Type, key -> elt -> t elt -> Prop := MapsTo (class t).
    Definition In : forall elt : Type, key -> t elt -> Prop :=
      fun (elt : Type) (k : key) (m : t elt) => exists e : elt, MapsTo k e m.
    Definition Empty : forall elt : Type, t elt -> Prop :=
      fun (elt : Type) (m : t elt) => forall (a : key) (e : elt), ~ MapsTo a e m.
    Definition eq_key : forall elt : Type, key * elt -> key * elt -> Prop :=
      fun (elt : Type) (p p' : key * elt) => (fst p) == (fst p').
    Definition eq_key_elt : forall elt : Type, key * elt -> key * elt -> Prop :=
      fun (elt : Type) (p p' : key * elt) => (fst p) == (fst p') /\ (snd p) = (snd p').
    Definition MapsTo_1 :
      forall (elt : Type) (m : t elt) (x y : key) (e : elt),
        x == y -> MapsTo x e m -> MapsTo y e m := MapsTo_1 (m0:=class t).
    Definition mem_1 : forall (elt : Type) (m : t elt) (x : key), In x m -> mem x m = true :=
      mem_1 (m0:=class t).
    Definition mem_2 : forall (elt : Type) (m : t elt) (x : key), mem x m = true -> In x m :=
      mem_2 (m0:=class t).
    Definition empty_1 : forall elt : Type, Empty (empty elt) := empty_1 (m0:=class t).
    Definition is_empty_1 : forall (elt : Type) (m : t elt), Empty m -> is_empty m = true :=
      is_empty_1 (m0:=class t).
    Definition is_empty_2 : forall (elt : Type) (m : t elt), is_empty m = true -> Empty m :=
      is_empty_2 (m0:=class t).
    Definition add_1 :
      forall (elt : Type) (m : t elt) (x y : key) (e : elt),
        x == y -> MapsTo y e (add x e m) :=
      add_1 (class t).
    Definition add_2 :
      forall (elt : Type) (m : t elt) (x y : key) (e e' : elt),
        ~ x == y -> MapsTo y e m -> MapsTo y e (add x e' m) :=
      add_2 (m0:=class t).
    Definition add_3 :
      forall (elt : Type) (m : t elt) (x y : key) (e e' : elt),
        ~ x == y -> MapsTo y e (add x e' m) -> MapsTo y e m :=
      add_3 (m0:=class t).
    Definition remove_1 :
      forall (elt : Type) (m : t elt) (x y : key), x == y -> ~ In y (remove x m) :=
      remove_1 (m0:=class t).
    Definition remove_2 :
      forall (elt : Type) (m : t elt) (x y : key) (e : elt),
        ~ x == y -> MapsTo y e m -> MapsTo y e (remove x m) :=
      remove_2 (m0:=class t).
    Definition remove_3 :
      forall (elt : Type) (m : t elt) (x y : key) (e : elt),
        MapsTo y e (remove x m) -> MapsTo y e m :=
      remove_3 (m0:=class t).
    Definition find_1 :
      forall (elt : Type) (m : t elt) (x : key) (e : elt),
        MapsTo x e m -> find x m = Some e :=
      find_1 (m0:=class t).
    Definition find_2 :
      forall (elt : Type) (m : t elt) (x : key) (e : elt),
        find x m = Some e -> MapsTo x e m :=
      find_2 (m0:=class t).
    Definition elements_1 :
      forall (elt : Type) (m : t elt) (x : key) (e : elt),
        MapsTo x e m -> InA (@eq_key_elt elt) (x, e) (elements m) :=
      elements_1 (m0:=class t).
    Definition elements_2 :
      forall (elt : Type) (m : t elt) (x : key) (e : elt),
        InA (@eq_key_elt elt) (x, e) (elements m) -> MapsTo x e m :=
      elements_2 (m0:=class t).
    Definition elements_3w : forall (elt : Type) (m : t elt), NoDupA (@eq_key elt) (elements m) :=
      elements_3w (class t).
    Definition cardinal_1 : forall (elt : Type) (m : t elt), cardinal m = length (elements m) :=
      cardinal_1 (class t).
    Definition fold_1 :
      forall (elt : Type) (m : t elt) (A : Type) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i :=
      fold_1 (class t).
    Definition Equal : forall (elt : Type), t elt -> t elt -> Prop :=
      fun (elt : Type) (m m' : t elt) => forall y, find y m = find y m'.
    Definition Equiv :
      forall (elt : Type), (elt -> elt -> Prop) -> t elt -> t elt -> Prop :=
      fun (elt : Type) (eq_elt : elt -> elt -> Prop) m m' =>
        (forall k, In k m <-> In k m') /\
          (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
    Definition Equivb :
      forall (elt : Type), (elt -> elt -> bool) -> t elt -> t elt -> Prop :=
      fun (elt : Type) (cmp: elt -> elt -> bool) => Equiv (Cmp cmp).
    Definition equal_1 :
      forall (elt : Type) (m m' : t elt) (cmp : elt -> elt -> bool),
        Equivb cmp m m' -> equal cmp m m' = true :=
      equal_1 (m0:=class t).
    Definition equal_2 :
      forall (elt : Type) (m m' : t elt) (cmp : elt -> elt -> bool),
        equal cmp m m' = true -> Equivb cmp m m' :=
      equal_2 (m0:=class t).
    Definition map_1 :
      forall (elt elt' : Type) (m : t elt) (x : key) (e : elt) (f : elt -> elt'),
        MapsTo x e m -> MapsTo x (f e) (map f m) :=
      map_1 (m0:=class t).
    Definition map_2 :
      forall (elt elt' : Type) (m : t elt) (x : key) (f : elt -> elt'),
        In x (map f m) -> In x m :=
      map_2 (m0:=class t).
    Definition mapi_1 :
      forall (elt elt' : Type) (m : t elt) (x : key) (e : elt)
             (f : key -> elt -> elt'), MapsTo x e m ->
                                       exists y, y == x /\ MapsTo x (f y e) (mapi f m) :=
      mapi_1 (m0:=class t).
    Definition mapi_2 :
      forall (elt elt' : Type) (m : t elt) (x : key)
             (f : key -> elt -> elt'), In x (mapi f m) -> In x m :=
      mapi_2 (m0:=class t).
    Definition map2_1 :
      forall (elt elt' elt'' : Type) (m : t elt) (m' : t elt')
             (x : key) (f : option elt -> option elt' -> option elt''),
        In x m \/ In x m' ->
        find x (map2 f m m') = f (find x m) (find x m') :=
      map2_1 (m0:=class t).
    Definition map2_2 :
      forall (elt elt' elt'' : Type) (m : t elt) (m' : t elt')
             (x : key) (f : option elt -> option elt' -> option elt''),
        In x (map2 f m m') -> In x m \/ In x m' :=
      map2_2 (m0:=class t).
    Definition lt_key :
      forall (elt : Type), key * elt -> key * elt -> Prop :=
      fun (elt : Type) (p p' : key * elt) => (fst p) < (fst p').
    Definition elements_3 :
      forall (elt : Type) (m : t elt), Sorted.sort (@lt_key elt) (elements m) :=
      elements_3 (class t).

  End Definitions.

  #[global]
   Hint Immediate MapsTo_1 mem_2 is_empty_2
   map_2 mapi_2 add_3 remove_3 find_2
    : map.

  #[global]
   Hint Resolve mem_1 is_empty_1 is_empty_2 add_1 add_2 remove_1
   remove_2 find_1 fold_1 map_1 mapi_1 mapi_2
    : map.

End FM.

Export FM.Exports.
Import FM.


(** ** Lemmas from FMapFacts.Facts. *)

Module F.

  Local Close Scope boolean_if_scope.
  Local Open Scope general_if_scope.

  Local Open Scope ordered_scope.
  Local Open Scope fmap_scope.

  Global Hint Extern 1 (Equivalence _) => constructor; congruence : core.

  (* WFacts_fun *)

  Local Notation eq_dec := Orders.F.eq_dec.
  Local Notation eqb := Orders.F.eqb.

  Section WeakMapFacts.

    Context {key : orderedType}.
    Context {t : fmapType key}.

    Lemma eq_bool_alt : forall b b', b = b' <-> (b = true <-> b' = true).
    Proof.
      destruct b; destruct b'; intuition.
    Qed.

    Lemma eq_option_alt : forall (elt : Type) (o o' : option elt),
        o = o' <-> (forall e, o = Some e <-> o' = Some e).
    Proof.
      split; intros.
      subst; split; auto.
      destruct o; destruct o'; try rewrite H; auto.
      symmetry; rewrite <- H; auto.
    Qed.

    Lemma MapsTo_fun : forall (elt : Type) (m : t elt) x (e e' : elt),
        MapsTo x e m -> MapsTo x e' m -> e = e'.
    Proof.
      intros.
      generalize (find_1 H) (find_1 H0); clear H H0.
      intros; rewrite H in H0; injection H0; auto.
    Qed.

  End WeakMapFacts.


  Section IffSpec.

    Context {key : orderedType}.
    Context {t : fmapType key}.

    Variable elt elt' elt'' : Type.
    Implicit Type m : t elt.
    Implicit Type x y z : key.
    Implicit Type e : elt.
    Notation empty := (empty (t:=t)).

    Lemma In_iff : forall m x y, x == y -> (In x m <-> In y m).
    Proof.
      unfold In.
      split; intros (e0,H0); exists e0.
      apply (MapsTo_1 H H0); auto.
      apply (MapsTo_1 (O.eq_sym H) H0); auto.
    Qed.

    Lemma MapsTo_iff : forall m x y e, x == y -> (MapsTo x e m <-> MapsTo y e m).
    Proof.
      split; apply MapsTo_1; auto with ordered_type.
    Qed.

    Lemma mem_in_iff : forall m x, In x m <-> mem x m = true.
    Proof.
      split; [apply mem_1|apply mem_2].
    Qed.

    Lemma not_mem_in_iff : forall m x, ~ In x m <-> mem x m = false.
    Proof.
      intros; rewrite mem_in_iff; destruct (mem x m); intuition.
    Qed.

    Lemma In_dec : forall m x, { In x m } + { ~ In x m }.
    Proof.
      intros.
      generalize (mem_in_iff m x).
      destruct (mem x m); [left|right]; intuition.
    Qed.

    Lemma find_mapsto_iff : forall m x e, MapsTo x e m <-> find x m = Some e.
    Proof.
      split; [apply find_1|apply find_2].
    Qed.

    Lemma not_find_in_iff : forall m x, ~ In x m <-> find x m = None.
    Proof.
      split; intros.
      rewrite eq_option_alt. intro e. rewrite <- find_mapsto_iff.
      split; try discriminate. intro H'; elim H; exists e; auto.
      intros (e, He); rewrite -> find_mapsto_iff, H in He. discriminate.
    Qed.

    Lemma in_find_iff : forall m x, In x m <-> find x m <> None.
    Proof.
      intros; rewrite <- not_find_in_iff, mem_in_iff.
      destruct mem; intuition.
    Qed.

    Lemma equal_iff : forall m m' cmp, Equivb cmp m m' <-> equal cmp m m' = true.
    Proof.
      split; [apply equal_1|apply equal_2].
    Qed.

    Lemma empty_mapsto_iff : forall x e, MapsTo x e (empty elt) <-> False.
    Proof.
      intuition; apply (empty_1 H).
    Qed.

    Lemma empty_in_iff : forall x, In x (empty elt) <-> False.
    Proof.
      unfold In.
      split; [intros (e,H); rewrite empty_mapsto_iff in H|]; intuition.
    Qed.

    Lemma is_empty_iff : forall m, Empty m <-> is_empty m = true.
    Proof.
      split; [apply is_empty_1|apply is_empty_2].
    Qed.

    Lemma add_mapsto_iff : forall m x y e e',
        MapsTo y e' (add x e m) <->
          (x == y /\ e=e') \/
            (~ x == y /\ MapsTo y e' m).
    Proof.
      intros.
      intuition.
      destruct (eq_dec x y); [left|right].
      split; auto.
      symmetry; apply (MapsTo_fun (e':=e) H); auto with map.
      split; auto; apply add_3 with x e; auto.
      subst; auto with map.
    Qed.

    Lemma add_in_iff : forall m x y e, In y (add x e m) <-> x == y \/ In y m.
    Proof.
      unfold In; split.
      intros (e',H).
      destruct (eq_dec x y) as [E|E]; auto.
      right; exists e'; auto.
      apply (add_3 E H).
      destruct (eq_dec x y) as [E|E]; auto.
      intros.
      exists e; apply add_1; auto.
      intros [H|(e',H)].
      destruct E; auto.
      exists e'; apply add_2; auto.
    Qed.

    Lemma add_neq_mapsto_iff : forall m x y e e',
        ~ x == y -> (MapsTo y e' (add x e m)  <-> MapsTo y e' m).
    Proof.
      split; [apply add_3|apply add_2]; auto.
    Qed.

    Lemma add_neq_in_iff : forall m x y e,
        ~ x == y -> (In y (add x e m)  <-> In y m).
    Proof.
      split; intros (e',H0); exists e'.
      apply (add_3 H H0).
      apply add_2; auto.
    Qed.

    Lemma remove_mapsto_iff : forall m x y e,
        MapsTo y e (remove x m) <-> ~ x == y /\ MapsTo y e m.
    Proof.
      intros.
      split; intros.
      split.
      assert (In y (remove x m)) by (exists e; auto).
      intro H1; apply (remove_1 H1 H0).
      apply remove_3 with x; auto.
      apply remove_2; intuition.
    Qed.

    Lemma remove_in_iff : forall m x y, In y (remove x m) <-> ~ x == y /\ In y m.
    Proof.
      unfold In; split.
      intros (e,H).
      split.
      assert (In y (remove x m)) by (exists e; auto).
      intro H1; apply (remove_1 H1 H0).
      exists e; apply remove_3 with x; auto.
      intros (H,(e,H0)); exists e; apply remove_2; auto.
    Qed.

    Lemma remove_neq_mapsto_iff : forall m x y e,
        ~ x == y -> (MapsTo y e (remove x m)  <-> MapsTo y e m).
    Proof.
      split; [apply remove_3|apply remove_2]; auto.
    Qed.

    Lemma remove_neq_in_iff : forall m x y,
        ~ x == y -> (In y (remove x m)  <-> In y m).
    Proof.
      split; intros (e',H0); exists e'.
      apply (remove_3 H0).
      apply remove_2; auto.
    Qed.

    Lemma elements_mapsto_iff : forall m x e,
        MapsTo x e m <-> InA (@eq_key_elt _ elt) (x, e) (elements m).
    Proof.
      split; [apply elements_1 | apply elements_2].
    Qed.

    Lemma elements_in_iff : forall m x,
        In x m <-> exists e, InA (@eq_key_elt _ elt) (x,e) (elements m).
    Proof.
      unfold In; split; intros (e,H); exists e; [apply elements_1 | apply elements_2]; auto.
    Qed.

    Lemma map_mapsto_iff : forall m x b (f : elt -> elt'),
        MapsTo x b (map f m) <-> exists a, b = f a /\ MapsTo x a m.
    Proof.
      split.
      case_eq (find x m); intros.
      exists e.
      split.
      apply (MapsTo_fun (m:=map f m) (x:=x)); auto with map.
      apply find_2; auto with map.
      assert (In x (map f m)) by (exists b; auto).
      destruct (map_2 H1) as (a,H2).
      rewrite (find_1 H2) in H; discriminate.
      intros (a,(H,H0)).
      subst b; auto with map.
    Qed.

    Lemma map_in_iff : forall m x (f : elt -> elt'),
        In x (map f m) <-> In x m.
    Proof.
      split; intros; eauto with map.
      destruct H as (a,H).
      exists (f a); auto with map.
    Qed.

    Lemma mapi_in_iff : forall m x (f:key->elt->elt'),
        In x (mapi f m) <-> In x m.
    Proof.
      split; intros; eauto with map.
      destruct H as (a,H).
      destruct (mapi_1 f H) as (y,(H0,H1)).
      exists (f y a); auto.
    Qed.

    Lemma mapi_inv : forall m x b (f : key -> elt -> elt'),
        MapsTo x b (mapi f m) ->
        exists a y, y == x /\ b = f y a /\ MapsTo x a m.
    Proof.
      intros; case_eq (find x m); intros.
      exists e.
      destruct (@mapi_1 _ _ _ _ m x e f) as (y,(H1,H2)).
      apply find_2; auto with map.
      exists y; repeat split; auto with map.
      apply (MapsTo_fun (m:=mapi f m) (x:=x)); auto with map.
      assert (In x (mapi f m)) by (exists b; auto).
      destruct (mapi_2 H1) as (a,H2).
      rewrite (find_1 H2) in H0; discriminate.
    Qed.

    Lemma mapi_1bis : forall m x e (f : key -> elt -> elt'),
        (forall x y e, x == y -> f x e = f y e) ->
        MapsTo x e m -> MapsTo x (f x e) (mapi f m).
    Proof.
      intros.
      destruct (mapi_1 f H0) as (y,(H1,H2)).
      replace (f x e) with (f y e) by auto.
      auto.
    Qed.

    Lemma mapi_mapsto_iff : forall m x b (f : key -> elt -> elt'),
        (forall x y e, x == y -> f x e = f y e) ->
        (MapsTo x b (mapi f m) <-> exists a, b = f x a /\ MapsTo x a m).
    Proof.
      split.
      intros.
      destruct (mapi_inv H0) as (a,(y,(H1,(H2,H3)))).
      exists a; split; auto.
      subst b; auto.
      intros (a,(H0,H1)).
      subst b.
      apply mapi_1bis; auto.
    Qed.

  End IffSpec.


  Ltac map_iff :=
    repeat (progress (
                rewrite add_mapsto_iff || rewrite add_in_iff ||
                  rewrite remove_mapsto_iff || rewrite remove_in_iff ||
                    rewrite empty_mapsto_iff || rewrite empty_in_iff ||
                      rewrite map_mapsto_iff || rewrite map_in_iff ||
                        rewrite mapi_in_iff)).


  Section BoolSpec.

    Context {key : orderedType}.
    Context {t : fmapType key}.

    Lemma mem_find_b : forall (elt : Type) (m : t elt) (x : key),
        mem x m = if find x m then true else false.
    Proof.
      intros.
      generalize (find_mapsto_iff m x)(mem_in_iff m x); unfold In.
      destruct (find x m); destruct (mem x m); auto.
      intros.
      rewrite <- H0; exists e; rewrite H; auto.
      intuition.
      destruct H0 as (e,H0).
      destruct (H e); intuition discriminate.
    Qed.

    Variable elt elt' elt'' : Type.
    Implicit Types m : t elt.
    Implicit Types x y z : key.
    Implicit Types e : elt.

    Lemma mem_b : forall m x y, x == y -> mem x m = mem y m.
    Proof.
      intros.
      generalize (mem_in_iff m x) (mem_in_iff m y)(In_iff m H).
      destruct (mem x m); destruct (mem y m); intuition.
    Qed.

    Lemma find_o : forall m x y, x == y -> find x m = find y m.
    Proof.
      intros. rewrite eq_option_alt. intro e. rewrite <- 2 find_mapsto_iff.
      apply MapsTo_iff; auto.
    Qed.

    Lemma empty_o : forall x, find (t:=t) x (empty elt) = None.
    Proof.
      intros. rewrite eq_option_alt. intro e.
      rewrite <- find_mapsto_iff, empty_mapsto_iff; now intuition.
    Qed.

    Lemma empty_a : forall x, mem (t:=t) x (empty elt) = false.
    Proof.
      intros.
      case_eq (mem x (empty (t:=t) elt)); intros; auto.
      generalize (mem_2 H).
      rewrite empty_in_iff; intuition.
    Qed.

    Lemma add_eq_o : forall m x y e,
        x == y -> find y (add x e m) = Some e.
    Proof.
      auto with map.
    Qed.

    Lemma add_neq_o : forall m x y e,
        ~ x == y -> find y (add x e m) = find y m.
    Proof.
      intros. rewrite eq_option_alt. intro e'. rewrite <- 2 find_mapsto_iff.
      apply add_neq_mapsto_iff; auto.
    Qed.

    Local Hint Resolve add_neq_o : map.

    Lemma add_o : forall m x y e,
        find y (add x e m) = if eq_dec x y then Some e else find y m.
    Proof.
      intros; destruct (eq_dec x y); simpl; auto with map.
    Qed.

    Lemma add_eq_b : forall m x y e,
        x == y -> mem y (add x e m) = true.
    Proof.
      intros; rewrite mem_find_b; rewrite add_eq_o; auto.
    Qed.

    Lemma add_neq_b : forall m x y e,
        ~ x == y -> mem y (add x e m) = mem y m.
    Proof.
      intros; do 2 rewrite mem_find_b; rewrite add_neq_o; auto.
    Qed.

    Lemma add_b : forall m x y e,
        mem y (add x e m) = eqb x y || mem y m.
    Proof.
      intros; do 2 rewrite mem_find_b; rewrite add_o; unfold eqb.
      destruct (eq_dec x y); simpl; auto.
    Qed.

    Lemma remove_eq_o : forall m x y,
        x == y -> find y (remove x m) = None.
    Proof.
      intros. rewrite eq_option_alt. intro e.
      rewrite <- find_mapsto_iff, remove_mapsto_iff; now intuition.
    Qed.

    Local Hint Resolve remove_eq_o : map.

    Lemma remove_neq_o : forall m x y,
        ~ x == y -> find y (remove x m) = find y m.
    Proof.
      intros. rewrite eq_option_alt. intro e.
      rewrite <- find_mapsto_iff, remove_neq_mapsto_iff; now intuition.
    Qed.

    Local Hint Resolve remove_neq_o : map.

    Lemma remove_o : forall m x y,
        find y (remove x m) = if eq_dec x y then None else find y m.
    Proof.
      intros; destruct (eq_dec x y); simpl; auto with map.
    Qed.

    Lemma remove_eq_b : forall m x y,
        x == y -> mem y (remove x m) = false.
    Proof.
      intros; rewrite mem_find_b; rewrite remove_eq_o; auto.
    Qed.

    Lemma remove_neq_b : forall m x y,
        ~ x == y -> mem y (remove x m) = mem y m.
    Proof.
      intros; do 2 rewrite mem_find_b; rewrite remove_neq_o; auto.
    Qed.

    Lemma remove_b : forall m x y,
        mem y (remove x m) = negb (eqb x y) && mem y m.
    Proof.
      intros; do 2 rewrite mem_find_b; rewrite remove_o; unfold eqb.
      destruct (eq_dec x y); auto.
    Qed.

    Lemma map_o : forall m x (f : elt -> elt'),
        find x (map f m) = Datatypes.option_map f (find x m).
    Proof.
      intros.
      generalize (find_mapsto_iff (map f m) x) (find_mapsto_iff m x)
                 (fun b => map_mapsto_iff m x b f).
      destruct (find x (map f m)); destruct (find x m); simpl; auto; intros.
      rewrite <- H; rewrite H1; exists e0; rewrite H0; auto.
      destruct (H e) as [_ H2].
      rewrite H1 in H2.
      destruct H2 as (a,(_,H2)); auto.
      rewrite H0 in H2; discriminate.
      rewrite <- H; rewrite H1; exists e; rewrite H0; auto.
    Qed.

    Lemma map_b : forall m x (f : elt -> elt'),
        mem x (map f m) = mem x m.
    Proof.
      intros; do 2 rewrite mem_find_b; rewrite map_o.
      destruct (find x m); simpl; auto.
    Qed.

    Lemma mapi_b : forall m x (f : key -> elt -> elt'),
        mem x (mapi f m) = mem x m.
    Proof.
      intros.
      generalize (mem_in_iff (mapi f m) x) (mem_in_iff m x) (mapi_in_iff m x f).
      destruct (mem x (mapi f m)); destruct (mem x m); simpl; auto; intros.
      symmetry; rewrite <- H0; rewrite <- H1; rewrite H; auto.
      rewrite <- H; rewrite H1; rewrite H0; auto.
    Qed.

    Lemma mapi_o : forall m x (f : key -> elt -> elt'),
        (forall x y e, x == y -> f x e = f y e) ->
        find x (mapi f m) = Datatypes.option_map (f x) (find x m).
    Proof.
      intros.
      generalize (find_mapsto_iff (mapi f m) x) (find_mapsto_iff m x)
                 (fun b => mapi_mapsto_iff m x b H).
      destruct (find x (mapi f m)); destruct (find x m); simpl; auto; intros.
      rewrite <- H0; rewrite H2; exists e0; rewrite H1; auto.
      destruct (H0 e) as [_ H3].
      rewrite H2 in H3.
      destruct H3 as (a,(_,H3)); auto.
      rewrite H1 in H3; discriminate.
      rewrite <- H0; rewrite H2; exists e; rewrite H1; auto.
    Qed.

    Lemma map2_1bis : forall (m : t elt) (m' : t elt') x
                             (f : option elt -> option elt' -> option elt''),
        f None None = None ->
        find x (map2 f m m') = f (find x m) (find x m').
    Proof.
      intros.
      case_eq (find x m); intros.
      rewrite <- H0.
      apply map2_1; auto with map.
      left; exists e; auto with map.
      case_eq (find x m'); intros.
      rewrite <- H0; rewrite <- H1.
      apply map2_1; auto.
      right; exists e; auto with map.
      rewrite H.
      case_eq (find x (map2 f m m')); intros; auto with map.
      assert (In x (map2 f m m')) by (exists e; auto with map).
      destruct (map2_2 H3) as [(e0,H4)|(e0,H4)].
      rewrite (find_1 H4) in H0; discriminate.
      rewrite (find_1 H4) in H1; discriminate.
    Qed.

    Lemma elements_o : forall m x,
        find x m = findA (eqb x) (elements m).
    Proof.
      intros. rewrite eq_option_alt. intro e.
      rewrite <- find_mapsto_iff, elements_mapsto_iff.
      unfold eqb.
      rewrite <- findA_NoDupA; dintuition; try apply elements_3w; eauto.
    Qed.

    Lemma elements_b : forall m x,
        mem x m = existsb (fun p => eqb x (fst p)) (elements m).
    Proof.
      intros.
      generalize (mem_in_iff m x)(elements_in_iff m x)
                 (existsb_exists (fun p => eqb x (fst p)) (elements m)).
      destruct (mem x m); destruct (existsb (fun p => eqb x (fst p)) (elements m)); auto; intros.
      symmetry; rewrite H1.
      destruct H0 as (H0,_).
      destruct H0 as (e,He); [ intuition |].
      rewrite InA_alt in He.
      destruct He as ((y,e'),(Ha1,Ha2)).
      compute in Ha1; destruct Ha1; subst e'.
      exists (y,e); split; simpl; auto.
      unfold eqb; destruct (eq_dec x y); intuition.
      rewrite <- H; rewrite H0.
      destruct H1 as (H1,_).
      destruct H1 as ((y,e),(Ha1,Ha2)); [intuition|].
      simpl in Ha2.
      unfold eqb in *; destruct (eq_dec x y); auto; try discriminate.
      exists e; rewrite InA_alt.
      exists (y,e); intuition.
      compute; auto.
    Qed.

  End BoolSpec.


  Section Equalities.

    Context {key : orderedType}.
    Context {t : fmapType key}.

    Variable elt : Type.

    Lemma Equal_mapsto_iff : forall m1 m2 : t elt,
        Equal m1 m2 <-> (forall k e, MapsTo k e m1 <-> MapsTo k e m2).
    Proof.
      intros m1 m2. split; [intros Heq k e|intros Hiff].
      rewrite -> 2 find_mapsto_iff, Heq. split; auto.
      intro k. rewrite eq_option_alt. intro e.
      rewrite <- 2 find_mapsto_iff; auto.
    Qed.

    Lemma Equal_Equiv : forall (m m' : t elt),
        Equal m m' <-> Equiv Logic.eq m m'.
    Proof.
      intros. rewrite Equal_mapsto_iff. split; intros.
      split.
      split; intros (e,Hin); exists e; [rewrite <- H|rewrite H]; auto.
      intros; apply MapsTo_fun with m k; auto; rewrite H; auto.
      split; intros H'.
      destruct H.
      assert (Hin : In k m') by (rewrite <- H; exists e; auto).
      destruct Hin as (e',He').
      rewrite (H0 k e e'); auto.
      destruct H.
      assert (Hin : In k m) by (rewrite H; exists e; auto).
      destruct Hin as (e',He').
      rewrite <- (H0 k e' e); auto.
    Qed.

    Section Cmp.

      Variable eq_elt : elt -> elt -> Prop.
      Variable cmp : elt -> elt -> bool.

      Definition compat_cmp :=
        forall e e', cmp e e' = true <-> eq_elt e e'.

      Lemma Equiv_Equivb : compat_cmp ->
                           forall (m m' : t elt), Equiv eq_elt m m' <-> Equivb cmp m m'.
      Proof.
        unfold Equivb, Equiv, Cmp; intuition.
        red in H; rewrite H; eauto.
        red in H; rewrite <-H; eauto.
      Qed.

    End Cmp.

    Lemma Equal_Equivb : forall cmp,
        (forall e e', cmp e e' = true <-> e = e') ->
        forall (m m' : t elt), Equal m m' <-> Equivb cmp m m'.
    Proof.
      intros; rewrite Equal_Equiv.
      apply Equiv_Equivb; auto.
    Qed.

    Lemma Equal_Equivb_eqdec :
      forall eq_elt_dec : (forall e e', { e = e' } + { e <> e' }),
        let cmp := fun e e' => if eq_elt_dec e e' then true else false in
        forall (m m' : t elt), Equal m m' <-> Equivb cmp m m'.
    Proof.
      intros; apply Equal_Equivb.
      unfold cmp; clear cmp; intros.
      destruct eq_elt_dec; now intuition.
    Qed.

  End Equalities.


  Section Setoid.

    Context {key : orderedType}.
    Context {t : fmapType key}.

    Lemma Equal_refl : forall (elt : Type) (m : t elt), Equal m m.
    Proof. red; reflexivity. Qed.

    Lemma Equal_sym : forall (elt : Type) (m m' : t elt),
        Equal m m' -> Equal m' m.
    Proof. unfold Equal; auto. Qed.

    Lemma Equal_trans : forall (elt : Type) (m m' m'' : t elt),
        Equal m m' -> Equal m' m'' -> Equal m m''.
    Proof. unfold Equal; congruence. Qed.

    Definition Equal_ST : forall elt : Type, Equivalence (@Equal key t elt).
    Proof.
      constructor; red; [apply Equal_refl | apply Equal_sym | apply Equal_trans].
    Qed.

    Add Relation key oeq
        reflexivity proved by O.eq_refl
        symmetry proved by O.eq_sym
        transitivity proved by O.eq_trans
        as KeySetoid.

    Arguments Equal {key} {t} {elt} m m'.

  End Setoid.

  Add Parametric Relation (key : orderedType) (t : fmapType key) (elt : Type) : (t elt) (@Equal key t elt)
      reflexivity proved by (@Equal_refl key t elt)
      symmetry proved by (@Equal_sym key t elt)
      transitivity proved by (@Equal_trans key t elt)
      as EqualSetoid.

  Add Parametric Morphism (key : orderedType) (t : fmapType key) (elt : Type) : (@In key t elt)
      with signature oeq ==> (@Equal key t elt) ==> iff as In_m.
  Proof.
    unfold Equal; intros k k' Hk m m' Hm.
    rewrite -> (In_iff m Hk), in_find_iff, in_find_iff, Hm; intuition.
  Qed.

  Add Parametric Morphism (key : orderedType) (t : fmapType key) (elt : Type) : (@MapsTo key t elt)
      with signature oeq ==> Logic.eq ==> (@Equal key t elt) ==> iff as MapsTo_m.
  Proof.
    unfold Equal; intros k k' Hk e m m' Hm.
    rewrite -> (MapsTo_iff m e Hk), find_mapsto_iff, find_mapsto_iff, Hm;
      intuition.
  Qed.

  Add Parametric Morphism (key : orderedType) (t : fmapType key) (elt : Type) : (@Empty key t elt)
      with signature (@Equal key t elt) ==> iff as Empty_m.
  Proof.
    unfold Empty; intros m m' Hm. split; intros; intro.
    rewrite <-Hm in H0; eapply H, H0.
    rewrite Hm in H0; eapply H, H0.
  Qed.

  Add Parametric Morphism (key : orderedType) (t : fmapType key) (elt : Type) : (@is_empty key t elt)
      with signature (@Equal key t elt) ==> Logic.eq as is_empty_m.
  Proof.
    intros m m' Hm.
    rewrite -> eq_bool_alt, <-is_empty_iff, <-is_empty_iff, Hm; intuition.
  Qed.

  Add Parametric Morphism (key : orderedType) (t : fmapType key) (elt : Type) : (@mem key t elt)
      with signature oeq ==> (@Equal key t elt) ==> Logic.eq as mem_m.
  Proof.
    intros k k' Hk m m' Hm.
    rewrite -> eq_bool_alt, <- mem_in_iff, <-mem_in_iff, Hk, Hm; intuition.
  Qed.

  Add Parametric Morphism (key : orderedType) (t : fmapType key) (elt : Type) : (@find key t elt)
      with signature oeq ==> (@Equal key t elt) ==> Logic.eq as find_m.
  Proof.
    intros k k' Hk m m' Hm. rewrite eq_option_alt. intro e.
    rewrite <- 2 find_mapsto_iff, Hk, Hm. split; auto.
  Qed.

  Add Parametric Morphism (key : orderedType) (t : fmapType key) (elt : Type) : (@add key t elt)
      with signature oeq ==> Logic.eq ==> (@Equal key t elt) ==> (@Equal key t elt) as add_m.
  Proof.
    intros k k' Hk e m m' Hm y.
    rewrite -> add_o, add_o; do 2 destruct eq_dec as [|?Hnot]; auto.
    elim Hnot; rewrite <-Hk; auto.
    elim Hnot; rewrite Hk; auto.
  Qed.

  Add Parametric Morphism (key : orderedType) (t : fmapType key) (elt : Type) : (@remove key t elt)
      with signature oeq ==> (@Equal key t elt) ==> (@Equal key t elt) as remove_m.
  Proof.
    intros k k' Hk m m' Hm y.
    rewrite -> remove_o, remove_o; do 2 destruct eq_dec as [|?Hnot]; auto.
    elim Hnot; rewrite <-Hk; auto.
    elim Hnot; rewrite Hk; auto.
  Qed.

  Add Parametric Morphism (key : orderedType) (t : fmapType key) (elt elt' : Type) : (@map key t elt elt')
      with signature Logic.eq ==> (@Equal key t elt) ==> (@Equal key t elt') as map_m.
  Proof.
    intros f m m' Hm y.
    rewrite -> map_o, map_o, Hm; auto.
  Qed.

  Notation not_find_mapsto_iff := not_find_in_iff.

End F.


(** ** Lemmas from FMapFacts.Properties *)

Module P.

  Import F.

  Local Open Scope ordered_scope.

  Local Notation eqb := Orders.F.eqb.

  Section Elt.

    Context {key : orderedType}.
    Context {t : fmapType key}.

    Variable elt : Type.

    Definition Add x (e : elt) (m m' : t elt) := forall y, find y m' = find y (add x e m).

    Notation eqke := (@eq_key_elt key elt).
    Notation eqk := (@eq_key key elt).

    Instance eqk_equiv : Equivalence eqk.
    Proof. unfold eq_key; split; eauto with ordered_type. Qed.

    Instance eqke_equiv : Equivalence eqke.
    Proof.
      unfold eq_key_elt; split; repeat red; firstorder; eauto with ordered_type.
      congruence.
    Qed.

    Lemma InA_eqke_eqk : forall k1 k2 e1 e2 l,
        (k1 == k2)%OT -> InA eqke (k1, e1) l -> InA eqk (k2, e2) l.
    Proof.
      intros k1 k2 e1 e2 l Hk. rewrite -> 2 InA_alt.
      intros ((k',e') & (Hk',He') & H); simpl in *.
      exists (k',e'); split; auto.
      red; simpl; eauto with ordered_type.
    Qed.

    Lemma NoDupA_eqk_eqke : forall l, NoDupA eqk l -> NoDupA eqke l.
    Proof.
      induction 1; auto.
      constructor; auto.
      destruct x as (k,e).
      eauto using InA_eqke_eqk with ordered_type.
    Qed.

    Lemma findA_rev : forall l k, NoDupA eqk l ->
                                  findA (eqb k) l = findA (eqb k) (rev l).
    Proof.
      intros.
      case_eq (findA (eqb k) l).
      intros. symmetry.
      unfold eqb.
      (rewrite <- findA_NoDupA, InA_rev, findA_NoDupA
        by (eauto using NoDupA_rev with *); eauto).
       case_eq (findA (eqb k) (rev l)); auto.
       intros e.
       unfold eqb.
       (rewrite <- findA_NoDupA, InA_rev, findA_NoDupA
         by (eauto using NoDupA_rev with *)).
        intro Eq; rewrite Eq; auto.
    Qed.

    Lemma elements_Empty : forall m : t elt, Empty m <-> elements m = nil.
    Proof.
      intros.
      unfold Empty.
      split; intros.
      assert (forall a, ~ List.In a (elements m)).
      red; intros.
      apply (H (fst a) (snd a)).
      rewrite elements_mapsto_iff.
      rewrite InA_alt; exists a; auto with ordered_type.
      split; auto; split; auto with ordered_type.
      destruct (elements m); auto with ordered_type.
      elim (H0 p); simpl; auto.
      red; intros.
      rewrite elements_mapsto_iff in H0.
      rewrite InA_alt in H0; destruct H0.
      rewrite H in H0; destruct H0 as (_,H0); inversion H0.
    Qed.

    Lemma elements_empty : elements (@empty key t elt) = nil.
    Proof.
      rewrite <- elements_Empty; apply empty_1.
    Qed.

    Definition uncurry {U V W : Type} (f : U -> V -> W) : U * V -> W :=
      fun p => f (fst p) (snd p).

    Definition of_list :=
      List.fold_right (uncurry (@add key t elt)) (empty elt).

    Definition to_list := elements (t:=t).

    Lemma of_list_1 : forall l k e,
        NoDupA eqk l ->
        (MapsTo k e (of_list l) <-> InA eqke (k, e) l).
    Proof.
      induction l as [|(k',e') l IH]; simpl; intros k e Hnodup.
      rewrite empty_mapsto_iff, InA_nil; intuition.
      unfold uncurry; simpl.
      inversion_clear Hnodup as [| ? ? Hnotin Hnodup'].
      specialize (IH k e Hnodup'); clear Hnodup'.
      rewrite add_mapsto_iff, InA_cons, <- IH.
      unfold eq_key_elt at 1; simpl.
      split; destruct 1 as [H|H]; try (intuition;fail).
      destruct (O.eq_dec k k'); [left|right]; split; auto with ordered_type.
      contradict Hnotin.
      apply InA_eqke_eqk with k e; intuition.
    Qed.

    Lemma of_list_1b : forall l k,
        NoDupA eqk l ->
        find k (of_list l) = findA (eqb k) l.
    Proof.
      induction l as [|(k',e') l IH]; simpl; intros k Hnodup.
      apply empty_o.
      unfold uncurry; simpl.
      inversion_clear Hnodup as [| ? ? Hnotin Hnodup'].
      specialize (IH k Hnodup'); clear Hnodup'.
      rewrite add_o, IH.
      unfold eqb; do 2 destruct O.eq_dec as [|?Hnot]; auto; elim Hnot; eauto with ordered_type.
    Qed.

    Lemma of_list_2 : forall l, NoDupA eqk l ->
                                equivlistA eqke l (to_list (of_list l)).
    Proof.
      intros l Hnodup (k,e). unfold to_list.
      rewrite <- elements_mapsto_iff, of_list_1; intuition.
    Qed.

    Lemma of_list_3 : forall s, Equal (of_list (to_list s)) s.
    Proof.
      intros s k.
      rewrite of_list_1b, elements_o; auto.
      apply elements_3w.
    Qed.

    Lemma fold_spec_right (m : t elt) (A : Type) (i : A) (f : key -> elt -> A -> A) :
      fold f m i = List.fold_right (uncurry f) i (rev (elements m)).
    Proof.
      rewrite fold_1. symmetry. apply fold_left_rev_right.
    Qed.

    Lemma fold_rec :
      forall (A : Type) (P : t elt -> A -> Type) (f : key -> elt -> A -> A),
      forall (i : A) (m : t elt),
        (forall m, Empty m -> P m i) ->
        (forall k e a m' m'', MapsTo k e m -> ~In k m' ->
                              Add k e m' m'' -> P m' a -> P m'' (f k e a)) ->
        P m (fold f m i).
    Proof.
      intros A P f i m Hempty Hstep.
      rewrite fold_spec_right.
      set (F:=uncurry f).
      set (l:=rev (elements m)).
      assert (Hstep' : forall k e a m' m'', InA eqke (k,e) l -> ~In k m' ->
                                            Add k e m' m'' -> P m' a -> P m'' (F (k,e) a)).
      intros k e a m' m'' H ? ? ?; eapply Hstep; eauto.
      revert H; unfold l; rewrite InA_rev, elements_mapsto_iff. auto.
      assert (Hdup : NoDupA eqk l).
      unfold l. apply NoDupA_rev; try red; unfold eq_key. auto with typeclass_instances.
      apply elements_3w.
      assert (Hsame : forall k, find k m = findA (eqb k) l).
      intros k. unfold l. rewrite elements_o, findA_rev; auto.
      apply elements_3w.
      clearbody l. clearbody F. clear Hstep f. revert m Hsame. induction l.
      (* empty *)
      intros m Hsame; simpl.
      apply Hempty. intros k e.
      rewrite find_mapsto_iff, Hsame; simpl; discriminate.
      (* step *)
      intros m Hsame; destruct a as (k,e); simpl.
      apply Hstep' with (of_list l); auto.
      rewrite InA_cons; left; red; auto with ordered_type.
      inversion_clear Hdup. contradict H. destruct H as (e',He').
      apply InA_eqke_eqk with k e'; auto with ordered_type.
      rewrite <- of_list_1; auto.
      intro k'. rewrite Hsame, add_o, of_list_1b. simpl.
      unfold eqb. do 2 destruct O.eq_dec as [|?Hnot]; auto; elim Hnot; eauto with ordered_type.
      inversion_clear Hdup; auto.
      apply IHl.
      intros; eapply Hstep'; eauto.
      inversion_clear Hdup; auto.
      intros; apply of_list_1b. inversion_clear Hdup; auto.
    Qed.

    Theorem fold_rec_bis :
      forall (A : Type) (P : t elt -> A -> Type) (f : key -> elt -> A -> A),
      forall (i : A) (m : t elt),
        (forall m m' a, Equal m m' -> P m a -> P m' a) ->
        (P (empty _) i) ->
        (forall k e a m', MapsTo k e m -> ~In k m' ->
                          P m' a -> P (add k e m') (f k e a)) ->
        P m (fold f m i).
    Proof.
      intros A P f i m Pmorphism Pempty Pstep.
      apply fold_rec; intros.
      apply Pmorphism with (empty _); auto. intro k. rewrite empty_o.
      case_eq (find k m0); auto; intros e'; rewrite <- find_mapsto_iff.
      intro H'; elim (H k e'); auto.
      apply Pmorphism with (add k e m'); try intro; auto.
    Qed.

    Lemma fold_rec_nodep :
      forall (A : Type) (P : A -> Type) (f : key -> elt -> A -> A) (i : A) (m : t elt),
        P i -> (forall k e a, MapsTo k e m -> P a -> P (f k e a)) ->
        P (fold f m i).
    Proof.
      intros; apply fold_rec_bis with (P:=fun _ => P); auto.
    Qed.

    Lemma fold_rec_weak :
      forall (A : Type) (P : t elt -> A -> Type) (f : key -> elt -> A -> A) (i : A),
        (forall m m' a, Equal m m' -> P m a -> P m' a) ->
        P (empty _) i ->
        (forall k e a m, ~In k m -> P m a -> P (add k e m) (f k e a)) ->
        forall m, P m (fold f m i).
    Proof.
      intros; apply fold_rec_bis; auto.
    Qed.

    Lemma fold_rel :
      forall (A B : Type) (R : A -> B -> Type)
             (f : key -> elt -> A -> A) (g : key -> elt -> B -> B) (i : A) (j : B)
             (m : t elt),
        R i j ->
        (forall k e a b, MapsTo k e m -> R a b -> R (f k e a) (g k e b)) ->
        R (fold f m i) (fold g m j).
    Proof.
      intros A B R f g i j m Rempty Rstep.
      rewrite 2 fold_spec_right. set (l:=rev (elements m)).
      assert (Rstep' : forall k e a b, InA eqke (k,e) l ->
                                       R a b -> R (f k e a) (g k e b)) by
        (intros; apply Rstep; auto; rewrite elements_mapsto_iff, <- InA_rev; assumption).
      clearbody l; clear Rstep m.
      induction l; simpl; auto.
      apply Rstep'; auto.
      destruct a; simpl; rewrite InA_cons; left; red; auto with ordered_type.
    Qed.

    Lemma map_induction :
      forall P : t elt -> Type,
        (forall m, Empty m -> P m) ->
        (forall m m', P m -> forall x e, ~In x m -> Add x e m m' -> P m') ->
        forall m, P m.
    Proof.
      intros. apply (@fold_rec _ (fun s _ => P s) (fun _ _ _ => tt) tt m); eauto.
    Qed.

    Lemma map_induction_bis :
      forall P : t elt -> Type,
        (forall m m', Equal m m' -> P m -> P m') ->
        P (empty _) ->
        (forall x e m, ~In x m -> P m -> P (add x e m)) ->
        forall m, P m.
    Proof.
      intros.
      apply (@fold_rec_bis _ (fun s _ => P s) (fun _ _ _ => tt) tt m); eauto.
    Qed.

    Lemma fold_identity : forall m : t elt, Equal (fold (@add _ _ _) m (empty _)) m.
    Proof.
      intros.
      apply fold_rec with (P:=fun m acc => Equal acc m); auto with map.
      intros m' Heq k'.
      rewrite empty_o.
      case_eq (find k' m'); auto; intros e'; rewrite <- find_mapsto_iff.
      intro; elim (Heq k' e'); auto.
      intros k e a m' m'' _ _ Hadd Heq k'.
      red in Heq. rewrite Hadd, 2 add_o, Heq; auto.
    Qed.

    Section Fold_More.

      Variables (A : Type) (eqA : A -> A -> Prop) (st : Equivalence eqA) (f : key -> elt -> A -> A).

      Hypothesis Comp : Proper (oeq==>Logic.eq==>eqA==>eqA) f.

      Lemma fold_init :
        forall (m : t elt) i i', eqA i i' -> eqA (fold f m i) (fold f m i').
      Proof.
        intros. apply fold_rel with (R:=eqA); auto.
        intros. apply Comp; auto with ordered_type.
      Qed.

      Lemma fold_Empty :
        forall (m : t elt) i, Empty m -> eqA (fold f m i) i.
      Proof.
        intros. apply fold_rec_nodep with (P:=fun a => eqA a i).
        reflexivity.
        intros. elim (H k e); auto.
      Qed.

      Definition transpose_neqkey :=
        forall k k' e e' a, ~ k == k' ->
                            eqA (f k e (f k' e' a)) (f k' e' (f k e a)).

      Hypothesis Tra : transpose_neqkey.

      Lemma fold_commutes :
        forall i (m : t elt) k e,
          ~ In k m ->
          eqA (fold f m (f k e i)) (f k e (fold f m i)).
      Proof.
        intros i m k e Hnotin.
        apply fold_rel with (R:= fun a b => eqA a (f k e b)); auto.
        reflexivity.
        intros.
        transitivity (f k0 e0 (f k e b)).
        apply Comp; auto with ordered_type.
        apply Tra; auto with ordered_type.
        contradict Hnotin. rewrite <- (In_iff _ Hnotin); exists e0; auto.
      Qed.

      Local Hint Resolve NoDupA_eqk_eqke NoDupA_rev elements_3w : map.

      (* Renamed from fold_Equal because there is another stronger lemma with the same name *)
      Lemma fold_Equal1 :
        forall (m1 m2 : t elt) i, Equal m1 m2 ->
                                  eqA (fold f m1 i) (fold f m2 i).
      Proof.
        intros.
        rewrite 2 fold_spec_right.
        assert (NoDupA eqk (rev (elements m1))) by auto with map typeclass_instances.
        assert (NoDupA eqk (rev (elements m2))) by auto with map typeclass_instances.
        apply fold_right_equivlistA_restr with (R:=complement eqk)(eqA:=eqke).
        auto with typeclass_instances.
        auto.
        2: auto with crelations.
        4, 5: auto with map.
        intros (k1,e1) (k2,e2) (Hk,He) a1 a2 Ha; simpl in *; apply Comp; auto.
        unfold complement, eq_key, eq_key_elt; repeat red. intuition eauto with ordered_type.
        intros (k,e) (k',e'); unfold eq_key, uncurry; simpl; auto.
        rewrite <- NoDupA_altdef; auto.
        intros (k,e).
        rewrite 2 InA_rev, <- 2 elements_mapsto_iff, 2 find_mapsto_iff, H.
        auto with crelations.
      Qed.

      Lemma fold_Equal2 :
        forall (m1 m2 : t elt) i j, Equal m1 m2 -> eqA i j ->
                                    eqA (fold f m1 i) (fold f m2 j).
      Proof.
        intros.
        rewrite 2 fold_spec_right.
        assert (NoDupA eqk (rev (elements m1))) by auto with map typeclass_instances.
        assert (NoDupA eqk (rev (elements m2))) by auto with map typeclass_instances.
        apply fold_right_equivlistA_restr2 with (R:=complement eqk)(eqA:=eqke).
        auto with typeclass_instances.
        1, 10: auto.
        2: auto with crelations.
        4, 5: auto with map.
        - intros (k1,e1) (k2,e2) (Hk,He) a1 a2 Ha; simpl in *; apply Comp; auto.
        - unfold complement, eq_key, eq_key_elt; repeat red. intuition eauto with ordered_type.
        - intros (k,e) (k',e') z z' h h'; unfold eq_key, uncurry;simpl; auto.
          rewrite h'.
          auto.
        - rewrite <- NoDupA_altdef; auto.
        - intros (k,e).
          rewrite 2 InA_rev, <- 2 elements_mapsto_iff, 2 find_mapsto_iff, H.
          auto with crelations.
      Qed.

      Lemma fold_Add :
        forall (m1 m2 : t elt) k e i, ~ In k m1 -> Add k e m1 m2 ->
                                      eqA (fold f m2 i) (f k e (fold f m1 i)).
      Proof.
        intros.
        rewrite 2 fold_spec_right.
        set (f':=uncurry f).
        change (f k e (fold_right f' i (rev (elements m1))))
          with (f' (k,e) (fold_right f' i (rev (elements m1)))).
        assert (NoDupA eqk (rev (elements m1))) by auto with map typeclass_instances.
        assert (NoDupA eqk (rev (elements m2))) by auto with map typeclass_instances.
        apply fold_right_add_restr with
          (R:=complement eqk)(eqA:=eqke)(eqB:=eqA).
        auto with typeclass_instances.
        auto.
        2: auto with crelations.
        4, 5: auto with map.
        intros (k1,e1) (k2,e2) (Hk,He) a a' Ha; unfold f'; simpl in *. apply Comp; auto.
        unfold complement, eq_key_elt, eq_key; repeat red; intuition eauto with ordered_type.
        unfold f'; intros (k1,e1) (k2,e2); unfold eq_key, uncurry; simpl; auto.
        rewrite <- NoDupA_altdef; auto.
        rewrite InA_rev, <- elements_mapsto_iff. firstorder.
        intros (a,b).
        rewrite InA_cons, 2 InA_rev, <- 2 elements_mapsto_iff,
          2 find_mapsto_iff.
        unfold eq_key_elt; simpl.
        rewrite H0.
        rewrite add_o.
        destruct (O.eq_dec k a) as [EQ|NEQ]; split; auto with ordered_type.
        intros EQ'; inversion EQ'; auto with ordered_type.
        intuition; subst; auto with ordered_type.
        elim H. exists b. rewrite EQ.
        auto with map.
        intuition.
        elim NEQ; auto with ordered_type.
      Qed.

      Lemma fold_add :
        forall (m : t elt) k e i,
          ~ In k m ->
          eqA (fold f (add k e m) i) (f k e (fold f m i)).
      Proof.
        intros. apply fold_Add; try red; auto.
      Qed.

    End Fold_More.

    Lemma cardinal_fold : forall m : t elt,
        cardinal m = fold (fun _ _ => S) m 0.
    Proof.
      intros; rewrite cardinal_1, fold_1.
      symmetry; apply fold_left_length; auto.
    Qed.

    Lemma cardinal_Empty : forall m : t elt,
        Empty m <-> cardinal m = 0.
    Proof.
      intros.
      rewrite cardinal_1, elements_Empty.
      destruct (elements m); intuition; discriminate.
    Qed.

    Lemma Equal_cardinal : forall m m' : t elt,
        Equal m m' -> cardinal m = cardinal m'.
    Proof.
      intros; do 2 rewrite cardinal_fold.
      apply fold_Equal1 with (eqA:=Logic.eq); compute; auto.
    Qed.

    (* Renamed from cardinal_1, which is duplicate *)
    Lemma cardinal_0 : forall m : t elt, Empty m -> cardinal m = 0.
    Proof.
      intros; rewrite <- cardinal_Empty; auto.
    Qed.

    Lemma cardinal_2 :
      forall (m m' : t elt) x e, ~ In x m -> Add x e m m' -> cardinal m' = S (cardinal m).
    Proof.
      intros; do 2 rewrite cardinal_fold.
      change S with ((fun _ _ => S) x e).
      apply fold_Add with (eqA:=Logic.eq); compute; auto.
    Qed.

    Lemma cardinal_inv_1 : forall m : t elt,
        cardinal m = 0 -> Empty m.
    Proof.
      intros; rewrite cardinal_Empty; auto.
    Qed.

    Local Hint Resolve cardinal_inv_1 : map.

    Lemma cardinal_inv_2 :
      forall (m : t elt) n, cardinal m = S n -> { p : key * elt | MapsTo (fst p) (snd p) m }.
    Proof.
      intros m n H; rewrite cardinal_1 in H.
      generalize (elements_mapsto_iff m).
      destruct (elements m); try discriminate.
      exists p; auto.
      rewrite H0; destruct p; simpl; auto.
      constructor; red; auto with ordered_type.
    Qed.

    Lemma cardinal_inv_2b :
      forall (m : t elt), cardinal m <> 0 -> { p : key * elt | MapsTo (fst p) (snd p) m }.
    Proof.
      intros.
      generalize (@cardinal_inv_2 m); destruct cardinal.
      elim H;auto.
      eauto.
    Qed.

    Definition Disjoint (m m' : t elt) :=
      forall k, ~ (In k m /\ In k m').

    Definition Partition (m m1 m2 : t elt) :=
      Disjoint m1 m2 /\
        (forall k e, MapsTo k e m <-> MapsTo k e m1 \/ MapsTo k e m2).

    Definition filter (f : key -> elt -> bool) (m : t elt) :=
      fold (fun k e m => if f k e then add k e m else m) m (empty (t:=t) _).

    Definition for_all (f : key -> elt -> bool) (m : t elt) :=
      fold (fun k e b => if f k e then b else false) m true.

    Definition exists_ (f : key -> elt -> bool) (m : t elt) :=
      fold (fun k e b => if f k e then true else b) m false.

    Definition partition (f : key -> elt -> bool) (m : t elt) :=
      (filter f m, filter (fun k e => negb (f k e)) m).

    Definition update (m1 m2 : t elt) := fold (@add _ _ _) m2 m1.

    Definition restrict (m1 m2 : t elt) := filter (fun k _ => mem k m2) m1.

    Definition diff (m1 m2 : t elt) := filter (fun k _ => negb (mem k m2)) m1.

    Section Specs.

      Variable f : key -> elt -> bool.
      Hypothesis Hf : Proper (oeq ==> Logic.eq ==> Logic.eq) f.

      Lemma filter_iff : forall (m : t elt) k e,
          MapsTo k e (filter f m) <-> MapsTo k e m /\ f k e = true.
      Proof.
        unfold filter.
        set (f':=fun k e m => if f k e then add k e m else m).
        intro m. pattern m, (fold f' m (empty _)). apply fold_rec.

        intros m' Hm' k e. rewrite empty_mapsto_iff. intuition.
        elim (Hm' k e); auto.

        intros k e acc m1 m2 Hke Hn Hadd IH k' e'.
        change (Equal m2 (add k e m1)) in Hadd. rewrite Hadd.
        unfold f'; simpl.
        case_eq (f k e); intros Hfke; simpl;
          rewrite !add_mapsto_iff, IH; clear IH; intuition.
        rewrite <- Hfke; apply Hf; auto with ordered_type.
        destruct (O.eq_dec k k') as [Hk|Hk]; [left|right]; eauto with ordered_type.
        elim Hn; exists e'. rewrite Hk; auto.
        assert (f k e = f k' e') by (apply Hf; auto). congruence.
      Qed.

      Lemma for_all_iff : forall (m : t elt),
          for_all f m = true <-> (forall k e, MapsTo k e m -> f k e = true).
      Proof.
        unfold for_all.
        set (f':=fun k e b => if f k e then b else false).
        intro m. pattern m, (fold f' m true). apply fold_rec.

        intros m' Hm'. split; auto. intros _ k e Hke. elim (Hm' k e); auto.

        intros k e b m1 m2 _ Hn Hadd IH. clear m.
        change (Equal m2 (add k e m1)) in Hadd.
        unfold f'; simpl. case_eq (f k e); intros Hfke.
        (* f k e = true *)
        rewrite IH. clear IH. split; intros Hmapsto k' e' Hke'.
        rewrite Hadd, add_mapsto_iff in Hke'.
        destruct Hke' as [(?,?)|(?,?)]; auto.
        rewrite <- Hfke; apply Hf; auto with ordered_type.
        apply Hmapsto. rewrite Hadd, add_mapsto_iff; right; split; auto.
        contradict Hn; exists e'; rewrite Hn; auto.
        (* f k e = false *)
        split; try discriminate.
        intros Hmapsto. rewrite <- Hfke. apply Hmapsto.
        rewrite Hadd, add_mapsto_iff; auto with ordered_type.
      Qed.

      Lemma exists_iff : forall (m : t elt),
          exists_ f m = true <->
            (exists p, MapsTo (fst p) (snd p) m /\ f (fst p) (snd p) = true).
      Proof.
        unfold exists_.
        set (f':=fun k e b => if f k e then true else b).
        intro m. pattern m, (fold f' m false). apply fold_rec.

        intros m' Hm'. split; try discriminate.
        intros ((k,e),(Hke,_)); simpl in *. elim (Hm' k e); auto.

        intros k e b m1 m2 _ Hn Hadd IH. clear m.
        change (Equal m2 (add k e m1)) in Hadd.
        unfold f'; simpl. case_eq (f k e); intros Hfke.
        (* f k e = true *)
        split; [intros _|auto].
        exists (k,e); simpl; split; auto.
        rewrite Hadd, add_mapsto_iff; auto with ordered_type.
        (* f k e = false *)
        rewrite IH. clear IH. split; intros ((k',e'),(Hke1,Hke2)); simpl in *.
        exists (k',e'); simpl; split; auto.
        rewrite Hadd, add_mapsto_iff; right; split; auto.
        contradict Hn. exists e'; rewrite Hn; auto.
        rewrite Hadd, add_mapsto_iff in Hke1. destruct Hke1 as [(?,?)|(?,?)].
        assert (f k' e' = f k e) by (apply Hf; auto with ordered_type). congruence.
        exists (k',e'); auto.
      Qed.

    End Specs.

    Lemma Disjoint_alt : forall (m m' : t elt),
        Disjoint m m' <->
          (forall k e e', MapsTo k e m -> MapsTo k e' m' -> False).
    Proof.
      unfold Disjoint; split.
      intros H k v v' H1 H2.
      apply H with k; split.
      exists v; trivial.
      exists v'; trivial.
      intros H k ((v,Hv),(v',Hv')).
      eapply H; eauto.
    Qed.

    Section Partition.

      Variable f : key -> elt -> bool.
      Hypothesis Hf : Proper (oeq ==> Logic.eq ==> Logic.eq) f.

      Lemma partition_iff_1 : forall (m m1 : t elt) k e,
          m1 = fst (partition f m) ->
          (MapsTo k e m1 <-> MapsTo k e m /\ f k e = true).
      Proof.
        unfold partition; simpl; intros. subst m1.
        apply filter_iff; auto.
      Qed.

      Lemma partition_iff_2 : forall (m m2 : t elt) k e,
          m2 = snd (partition f m) ->
          (MapsTo k e m2 <-> MapsTo k e m /\ f k e = false).
      Proof.
        unfold partition; simpl; intros. subst m2.
        rewrite filter_iff.
        split; intros (H,H'); split; auto.
        destruct (f k e); simpl in *; auto.
        rewrite H'; auto.
        repeat red; intros. f_equal. apply Hf; auto.
      Qed.

      Lemma partition_Partition : forall (m m1 m2 : t elt),
          partition f m = (m1, m2) -> Partition m m1 m2.
      Proof.
        intros. split.
        rewrite Disjoint_alt. intros k e e'.
        rewrite (@partition_iff_1 m m1), (@partition_iff_2 m m2)
          by (rewrite H; auto).
        intros (U,V) (W,Z). rewrite <- (MapsTo_fun U W) in Z; congruence.
        intros k e.
        rewrite (@partition_iff_1 m m1), (@partition_iff_2 m m2)
          by (rewrite H; auto).
        destruct (f k e); intuition.
      Qed.

    End Partition.

    Lemma Partition_In : forall (m m1 m2 : t elt) k,
        Partition m m1 m2 -> In k m -> {In k m1} + {In k m2}.
    Proof.
      intros m m1 m2 k Hm Hk.
      destruct (In_dec m1 k) as [H|H]; [left|right]; auto.
      destruct Hm as (Hm,Hm').
      destruct Hk as (e,He); rewrite Hm' in He; destruct He.
      elim H; exists e; auto.
      exists e; auto.
    Defined.

    Lemma Disjoint_sym : forall (m1 m2 : t elt), Disjoint m1 m2 -> Disjoint m2 m1.
    Proof.
      intros m1 m2 H k (H1,H2). elim (H k); auto.
    Qed.

    Lemma Partition_sym : forall (m m1 m2 : t elt),
        Partition m m1 m2 -> Partition m m2 m1.
    Proof.
      intros m m1 m2 (H,H'); split.
      apply Disjoint_sym; auto.
      intros; rewrite H'; intuition.
    Qed.

    Lemma Partition_Empty : forall (m m1 m2 : t elt), Partition m m1 m2 ->
                                                      (Empty m <-> (Empty m1 /\ Empty m2)).
    Proof.
      intros m m1 m2 (Hdisj,Heq). split.
      intro He.
      split; intros k e Hke; elim (He k e); rewrite Heq; auto.
      intros (He1,He2) k e Hke. rewrite Heq in Hke. destruct Hke.
      elim (He1 k e); auto.
      elim (He2 k e); auto.
    Qed.

    Lemma Partition_Add :
      forall m m' x e , ~In x m -> Add x e m m' ->
                        forall m1 m2, Partition m' m1 m2 ->
                                      exists m3, (Add x e m3 m1 /\ Partition m m3 m2 \/
                                                    Add x e m3 m2 /\ Partition m m1 m3).
    Proof.
      unfold Partition. intros m m' x e Hn Hadd m1 m2 (Hdisj,Hor).
      assert (Heq : Equal m (remove x m')).
      change (Equal m' (add x e m)) in Hadd. rewrite Hadd.
      intro k. rewrite remove_o, add_o.
      destruct O.eq_dec as [He|Hne]; auto.
      rewrite <- He, <- not_find_in_iff; auto.
      assert (H : MapsTo x e m').
      change (Equal m' (add x e m)) in Hadd; rewrite Hadd.
      apply add_1; auto with ordered_type.
      rewrite Hor in H; destruct H.

      (* first case : x in m1 *)
      exists (remove x m1); left. split; [|split].
      (* add *)
      change (Equal m1 (add x e (remove x m1))).
      intro k.
      rewrite add_o, remove_o.
      destruct O.eq_dec as [He|Hne]; auto.
      rewrite <- He; apply find_1; auto.
      (* disjoint *)
      intros k (H1,H2). elim (Hdisj k). split; auto.
      rewrite remove_in_iff in H1; destruct H1; auto.
      (* mapsto *)
      intros k' e'.
      rewrite Heq, 2 remove_mapsto_iff, Hor.
      intuition.
      elim (Hdisj x); split; [exists e|exists e']; auto.
      apply MapsTo_1 with k'; auto with ordered_type.

      (* second case : x in m2 *)
      exists (remove x m2); right. split; [|split].
      (* add *)
      change (Equal m2 (add x e (remove x m2))).
      intro k.
      rewrite add_o, remove_o.
      destruct O.eq_dec as [He|Hne]; auto.
      rewrite <- He; apply find_1; auto.
      (* disjoint *)
      intros k (H1,H2). elim (Hdisj k). split; auto.
      rewrite remove_in_iff in H2; destruct H2; auto.
      (* mapsto *)
      intros k' e'.
      rewrite Heq, 2 remove_mapsto_iff, Hor.
      intuition.
      elim (Hdisj x); split; [exists e'|exists e]; auto.
      apply MapsTo_1 with k'; auto with ordered_type.
    Qed.

    Lemma Partition_fold :
      forall (A : Type) (eqA : A -> A -> Prop) (st : Equivalence eqA) (f : key -> elt -> A -> A),
        Proper (oeq ==> Logic.eq ==> eqA ==> eqA) f ->
        transpose_neqkey eqA f ->
        forall m m1 m2 i,
          Partition m m1 m2 ->
          eqA (fold f m i) (fold f m1 (fold f m2 i)).
    Proof.
      intros A eqA st f Comp Tra.
      induction m as [m Hm|m m' IH k e Hn Hadd] using map_induction.

      intros m1 m2 i Hp. rewrite (fold_Empty (eqA:=eqA)); auto.
      rewrite (Partition_Empty Hp) in Hm. destruct Hm.
      rewrite 2 (fold_Empty (eqA:=eqA)); auto. reflexivity.

      intros m1 m2 i Hp.
      destruct (Partition_Add Hn Hadd Hp) as (m3,[(Hadd',Hp')|(Hadd',Hp')]).
      (* fst case: m3 is (k,e)::m1 *)
      assert (~In k m3).
      contradict Hn. destruct Hn as (e',He').
      destruct Hp' as (Hp1,Hp2). exists e'. rewrite Hp2; auto.
      transitivity (f k e (fold f m i)).
      apply fold_Add with (eqA:=eqA); auto.
      symmetry.
      transitivity (f k e (fold f m3 (fold f m2 i))).
      apply fold_Add with (eqA:=eqA); auto.
      apply Comp; auto with ordered_type.
      symmetry; apply IH; auto.
      (* snd case: m3 is (k,e)::m2 *)
      assert (~In k m3).
      contradict Hn. destruct Hn as (e',He').
      destruct Hp' as (Hp1,Hp2). exists e'. rewrite Hp2; auto.
      assert (~In k m1).
      contradict Hn. destruct Hn as (e',He').
      destruct Hp' as (Hp1,Hp2). exists e'. rewrite Hp2; auto.
      transitivity (f k e (fold f m i)).
      apply fold_Add with (eqA:=eqA); auto.
      transitivity (f k e (fold f m1 (fold f m3 i))).
      apply Comp; auto using IH with ordered_type.
      transitivity (fold f m1 (f k e (fold f m3 i))).
      symmetry.
      apply fold_commutes with (eqA:=eqA); auto.
      apply fold_init with (eqA:=eqA); auto.
      symmetry.
      apply fold_Add with (eqA:=eqA); auto.
    Qed.

    Lemma Partition_cardinal : forall m m1 m2, Partition m m1 m2 ->
                                               cardinal m = cardinal m1 + cardinal m2.
    Proof.
      intros.
      rewrite (cardinal_fold m), (cardinal_fold m1).
      set (f:=fun (_:key)(_:elt)=>S).
      replace (fold f m 0) with (fold f m1 (fold f m2 0)).
      (* replace works but setoid_replace failed *)
      (* setoid_replace (fold f m 0) with (fold f m1 (fold f m2 0)). *)
      rewrite <- cardinal_fold.
      apply fold_rel with (R:=fun u v => u = v + cardinal m2); simpl; auto.
      (* added for using replace instead of setoid_replace *) symmetry.
      apply Partition_fold with (eqA:=Logic.eq); repeat red; auto.
    Qed.

    Lemma Partition_partition : forall m m1 m2, Partition m m1 m2 ->
                                                let f := fun k (_:elt) => mem k m1 in
                                                Equal m1 (fst (partition f m)) /\ Equal m2 (snd (partition f m)).
    Proof.
      intros m m1 m2 Hm f.
      assert (Hf : Proper (oeq==>Logic.eq==>Logic.eq) f).
      intros k k' Hk e e' _; unfold f; rewrite Hk; auto.
      set (m1':= fst (partition f m)).
      set (m2':= snd (partition f m)).
      split; rewrite Equal_mapsto_iff; intros k e.
      rewrite (@partition_iff_1 f Hf m m1') by auto.
      unfold f.
      rewrite <- mem_in_iff.
      destruct Hm as (Hm,Hm').
      rewrite Hm'.
      intuition.
      exists e; auto.
      elim (Hm k); split; auto; exists e; auto.
      rewrite (@partition_iff_2 f Hf m m2') by auto.
      unfold f.
      rewrite <- not_mem_in_iff.
      destruct Hm as (Hm,Hm').
      rewrite Hm'.
      intuition.
      elim (Hm k); split; auto; exists e; auto.
      elim H1; exists e; auto.
    Qed.

    Lemma update_mapsto_iff : forall m m' k e,
        MapsTo k e (update m m') <->
          (MapsTo k e m' \/ (MapsTo k e m /\ ~In k m')).
    Proof.
      unfold update.
      intros m m'.
      pattern m', (fold (@add _ _ _) m' m). apply fold_rec.

      intros m0 Hm0 k e.
      assert (~In k m0) by (intros (e0,He0); apply (Hm0 k e0); auto).
      intuition.
      elim (Hm0 k e); auto.

      intros k e m0 m1 m2 _ Hn Hadd IH k' e'.
      change (Equal m2 (add k e m1)) in Hadd.
      rewrite Hadd, 2 add_mapsto_iff, IH, add_in_iff. clear IH. intuition.
    Qed.

    Lemma update_dec : forall m m' k e, MapsTo k e (update m m') ->
                                        { MapsTo k e m' } + { MapsTo k e m /\ ~In k m'}.
    Proof.
      intros m m' k e H. rewrite update_mapsto_iff in H.
      destruct (In_dec m' k) as [H'|H']; [left|right]; intuition.
      elim H'; exists e; auto.
    Defined.

    Lemma update_in_iff : forall m m' k,
        In k (update m m') <-> In k m \/ In k m'.
    Proof.
      intros m m' k. split.
      intros (e,H); rewrite update_mapsto_iff in H.
      destruct H; [right|left]; exists e; intuition.
      destruct (In_dec m' k) as [H|H].
      destruct H as (e,H). intros _; exists e.
      rewrite update_mapsto_iff; left; auto.
      destruct 1 as [H'|H']; [|elim H; auto].
      destruct H' as (e,H'). exists e.
      rewrite update_mapsto_iff; right; auto.
    Qed.

    Lemma diff_mapsto_iff : forall m m' k e,
        MapsTo k e (diff m m') <-> MapsTo k e m /\ ~ In k m'.
    Proof.
      intros m m' k e.
      unfold diff.
      rewrite filter_iff.
      intuition.
      rewrite mem_1 in H1; auto; discriminate.
      intros ? ? Hk _ _ _; rewrite Hk; auto.
    Qed.

    Lemma diff_in_iff : forall m m' k,
        In k (diff m m') <-> In k m /\ ~ In k m'.
    Proof.
      intros m m' k. split.
      intros (e,H); rewrite diff_mapsto_iff in H.
      destruct H; split; auto. exists e; auto.
      intros ((e,H),H'); exists e; rewrite diff_mapsto_iff; auto.
    Qed.

    Lemma restrict_mapsto_iff : forall m m' k e,
        MapsTo k e (restrict m m') <-> MapsTo k e m /\ In k m'.
    Proof.
      intros m m' k e.
      unfold restrict.
      rewrite filter_iff.
      intuition.
      intros ? ? Hk _ _ _; rewrite Hk; auto.
    Qed.

    Lemma restrict_in_iff : forall m m' k,
        In k (restrict m m') <-> In k m /\ In k m'.
    Proof.
      intros m m' k. split.
      intros (e,H); rewrite restrict_mapsto_iff in H.
      destruct H; split; auto. exists e; auto.
      intros ((e,H),H'); exists e; rewrite restrict_mapsto_iff; auto.
    Qed.

    Definition filter_dom (f : key -> bool) := filter (fun k _ => f k).
    Definition filter_range (f : elt -> bool) := filter (fun _ => f).
    Definition for_all_dom (f : key -> bool) := for_all (fun k _ => f k).
    Definition for_all_range (f : elt -> bool) := for_all (fun _ => f).
    Definition exists_dom (f : key -> bool) := exists_ (fun k _ => f k).
    Definition exists_range (f : elt -> bool) := exists_ (fun _ => f).
    Definition partition_dom (f : key -> bool) := partition (fun k _ => f k).
    Definition partition_range (f : elt -> bool) := partition (fun _ => f).

  End Elt.

  Add Parametric Morphism key t elt : (@cardinal key t elt)
      with signature (@Equal key t elt) ==> Logic.eq as cardinal_m.
  Proof. intros; apply Equal_cardinal; auto. Qed.

  Add Parametric Morphism key t elt : (@Disjoint key t elt)
      with signature (@Equal key t elt) ==> (@Equal key t elt) ==> iff as Disjoint_m.
  Proof.
    intros m1 m1' Hm1 m2 m2' Hm2. unfold Disjoint. split; intros.
    rewrite <- Hm1, <- Hm2; auto.
    rewrite Hm1, Hm2; auto.
  Qed.

  Add Parametric Morphism key t elt : (@Partition key t elt)
      with signature (@Equal key t elt) ==> (@Equal key t elt) ==> (@Equal key t elt) ==> iff as Partition_m.
  Proof.
    intros m1 m1' Hm1 m2 m2' Hm2 m3 m3' Hm3. unfold Partition.
    rewrite <- Hm2, <- Hm3.
    split; intros (H,H'); split; auto; intros.
    rewrite <- Hm1, <- Hm2, <- Hm3; auto.
    rewrite Hm1, Hm2, Hm3; auto.
  Qed.

  Add Parametric Morphism key t elt : (@update key t elt)
      with signature (@Equal key t elt) ==> (@Equal key t elt) ==> (@Equal key t elt) as update_m.
  Proof.
    intros m1 m1' Hm1 m2 m2' Hm2.
    setoid_replace (update m1 m2) with (update m1' m2); unfold update.
    apply fold_Equal1 with (eqA:=(@Equal key t elt)); auto.
    intros k k' Hk e e' He m m' Hm; rewrite Hk,He,Hm; red; auto.
    intros k k' e e' i Hneq x.
    rewrite !add_o; do 2 destruct O.eq_dec; auto. elim Hneq; eauto with ordered_type.
    apply fold_init with (eqA:=(@Equal key t elt)); auto.
    intros k k' Hk e e' He m m' Hm; rewrite Hk,He,Hm; red; auto.
  Qed.

  Add Parametric Morphism key t elt : (@restrict key t elt)
      with signature (@Equal key t elt) ==> (@Equal key t elt) ==> (@Equal key t elt) as restrict_m.
  Proof.
    intros m1 m1' Hm1 m2 m2' Hm2.
    setoid_replace (restrict m1 m2) with (restrict m1' m2);
      unfold restrict, filter.
    apply fold_rel with (R:=(@Equal key t elt)); try red; auto.
    intros k e i i' H Hii' x.
    pattern (mem k m2); rewrite Hm2. (* UGLY, see with Matthieu *)
    destruct mem; rewrite Hii'; auto.
    apply fold_Equal1 with (eqA:=(@Equal key t elt)); auto.
    intros k k' Hk e e' He m m' Hm; simpl in *.
    pattern (mem k m2); rewrite Hk. (* idem *)
    destruct mem; rewrite ?Hk,?He,Hm; red; auto.
    intros k k' e e' i Hneq x.
    case_eq (mem k m2); case_eq (mem k' m2); intros; auto.
    rewrite !add_o; do 2 destruct O.eq_dec; auto. elim Hneq; eauto with ordered_type.
  Qed.

  Add Parametric Morphism key t elt : (@diff key t elt)
      with signature (@Equal key t elt) ==> (@Equal key t elt) ==> (@Equal key t elt) as diff_m.
  Proof.
    intros m1 m1' Hm1 m2 m2' Hm2.
    setoid_replace (diff m1 m2) with (diff m1' m2);
      unfold diff, filter.
    apply fold_rel with (R:=(@Equal key t elt)); try red; auto.
    intros k e i i' H Hii' x.
    pattern (mem k m2); rewrite Hm2. (* idem *)
    destruct mem; simpl; rewrite Hii'; auto.
    apply fold_Equal1 with (eqA:=(@Equal key t elt)); auto.
    intros k k' Hk e e' He m m' Hm; simpl in *.
    pattern (mem k m2); rewrite Hk. (* idem *)
    destruct mem; simpl; rewrite ?Hk,?He,Hm; red; auto.
    intros k k' e e' i Hneq x.
    case_eq (mem k m2); case_eq (mem k' m2); intros; simpl; auto.
    rewrite !add_o; do 2 destruct O.eq_dec; auto. elim Hneq; eauto with ordered_type.
  Qed.

End P.


(** ** Lemmas from FMapFacts.OrdProperties *)

Module OP.

  Import Orders.F Orders.OT F P.

  Local Open Scope ordered_scope.

  Section OrdProperties.

    Context {key : orderedType}.
    Context {t : fmapType key}.

    Variable elt : Type.

    Notation eqke := (@KO.eqke key elt).
    Notation eqk := (@KO.eqk key elt).
    Notation ltk := (@KO.ltk key elt).
    Notation cardinal := (@cardinal key t elt).
    Notation Equal := (@Equal key t elt).
    Notation Add := (@Add key t elt).

    Definition Above x (m : t elt) := forall y, In y m -> O.lt y x.
    Definition Below x (m : t elt) := forall y, In y m -> O.lt x y.

    Section Elements.

      Lemma sort_equivlistA_eqlistA : forall l l' : list (key*elt),
          sort ltk l -> sort ltk l' -> equivlistA eqke l l' -> eqlistA eqke l l'.
      Proof.
        apply SortA_equivlistA_eqlistA; auto with typeclass_instances.
      Qed.

      Ltac clean_eauto := unfold KO.eqke, KO.ltk; simpl; intuition; eauto.

      Definition gtb (p p': key * elt) :=
        match O.compare (fst p) (fst p') with GT _ => true | _ => false end.

      Definition leb p := fun p' => negb (gtb p p').

      Definition elements_lt p (m : t elt) := List.filter (gtb p) (elements m).
      Definition elements_ge p (m : t elt) := List.filter (leb p) (elements m).

      Lemma gtb_1 : forall p p', gtb p p' = true <-> ltk p' p.
      Proof.
        intros (x,e) (y,e'); unfold gtb, KO.ltk; simpl.
        destruct (O.compare x y); intuition; try discriminate; order.
      Qed.

      Lemma leb_1 : forall p p', leb p p' = true <-> ~ltk p' p.
      Proof.
        intros (x,e) (y,e'); unfold leb, gtb, KO.ltk; simpl.
        destruct (O.compare x y); intuition; try discriminate; order.
      Qed.

      Lemma gtb_compat : forall p, Proper (eqke==>Logic.eq) (gtb p).
      Proof.
        red; intros (x,e) (a,e') (b,e'') H; red in H; simpl in *; destruct H.
        generalize (gtb_1 (x,e) (a,e'))(gtb_1 (x,e) (b,e''));
          destruct (gtb (x,e) (a,e')); destruct (gtb (x,e) (b,e'')); auto.
        unfold KO.ltk in *; simpl in *; intros.
        symmetry; rewrite H2.
        apply eq_lt with a; auto with ordered_type.
        rewrite <- H1; auto.
        unfold KO.ltk in *; simpl in *; intros.
        rewrite H1.
        apply eq_lt with b; auto.
        rewrite <- H2; auto.
      Qed.

      Lemma leb_compat : forall p, Proper (eqke==>Logic.eq) (leb p).
      Proof.
        red; intros x a b H.
        unfold leb; f_equal; apply gtb_compat; auto.
      Qed.

      #[local]
       Hint Resolve gtb_compat leb_compat elements_3 : map.

      Lemma elements_split : forall p m,
          elements m = elements_lt p m ++ elements_ge p m.
      Proof.
        unfold elements_lt, elements_ge, leb; intros.
        apply filter_split with (eqA:=eqk) (ltA:=ltk).
        1-3: auto with typeclass_instances.
        2: auto with map.
        intros; destruct x; destruct y; destruct p.
        rewrite gtb_1 in H; unfold KO.ltk in H; simpl in *.
        assert (~ltk (s0,e0) (s1,e1)).
        unfold gtb, KO.ltk in *; simpl in *.
        destruct (O.compare s1 s0); intuition; try discriminate; order.
        unfold KO.ltk in *; simpl in *; order.
      Qed.

      Lemma elements_Add :
        forall (m m' : t elt) x e, ~In x m -> Add x e m m' ->
                                   eqlistA eqke (elements m')
                                           (elements_lt (x,e) m ++ (x,e):: elements_ge (x,e) m).
      Proof.
        intros; unfold elements_lt, elements_ge.
        apply sort_equivlistA_eqlistA. auto with map.
        apply (@SortA_app _ eqke). auto with typeclass_instances.
        apply (@filter_sort _ eqke). 1-3: auto with typeclass_instances. auto with map.
        constructor; auto with map.
        apply (@filter_sort _ eqke). 1-3: auto with typeclass_instances. auto with map.
        rewrite (@InfA_alt _ eqke). 2-4: auto with typeclass_instances.
        intros.
        rewrite filter_InA in H1 by auto with map. destruct H1.
        rewrite leb_1 in H2.
        destruct y; unfold KO.ltk in *; simpl in *.
        rewrite <- elements_mapsto_iff in H1.
        assert (~oeq x s).
        contradict H.
        exists e0; apply MapsTo_1 with s; auto with ordered_type.
        order.
        apply (@filter_sort _ eqke). 1-3: auto with typeclass_instances. auto with map.
        intros.
        rewrite filter_InA in H1 by auto with map. destruct H1.
        rewrite gtb_1 in H3.
        destruct y; destruct x0; unfold KO.ltk in *; simpl in *.
        inversion_clear H2.
        red in H4; simpl in *; destruct H4.
        order.
        rewrite filter_InA in H4 by auto with map. destruct H4.
        rewrite leb_1 in H4.
        unfold KO.ltk in *; simpl in *; order.
        red; intros a; destruct a.
        rewrite InA_app_iff, InA_cons, 2 filter_InA,
          <-2 elements_mapsto_iff, leb_1, gtb_1,
          find_mapsto_iff, (H0 s), <- find_mapsto_iff,
          add_mapsto_iff by auto with map.
        unfold KO.eqke, KO.ltk; simpl.
        destruct (O.compare s x); intuition; try fold (~oeq x s); auto with ordered_type.
        - elim H; exists e0; apply MapsTo_1 with s; auto.
        - fold (~O.lt s x); auto with ordered_type.
      Qed.

      Lemma elements_Add_Above : forall m m' x e,
          Above x m -> Add x e m m' ->
          eqlistA eqke (elements m') (elements m ++ (x,e)::nil).
      Proof.
        intros.
        apply sort_equivlistA_eqlistA. auto with map.
        apply (@SortA_app _ eqke). auto with typeclass_instances. auto with map. auto.
        intros.
        inversion_clear H2.
        destruct x0; destruct y.
        rewrite <- elements_mapsto_iff in H1.
        unfold KO.eqke, KO.ltk in *; simpl in *; destruct H3.
        apply lt_eq with x; auto with ordered_type.
        apply H; firstorder.
        inversion H3.
        red; intros a; destruct a.
        rewrite InA_app_iff, InA_cons, InA_nil, <- 2 elements_mapsto_iff,
          find_mapsto_iff, (H0 s), <- find_mapsto_iff,
          add_mapsto_iff.
        unfold KO.eqke; simpl. intuition.
        destruct (eq_dec x s) as [Heq|Hneq]; auto.
        exfalso.
        assert (In s m).
        exists e0; auto.
        generalize (H s H1).
        order.
      Qed.

      Lemma elements_Add_Below : forall m m' x e,
          Below x m -> Add x e m m' ->
          eqlistA eqke (elements m') ((x,e)::elements m).
      Proof.
        intros.
        apply sort_equivlistA_eqlistA. auto with map.
        change (sort ltk (((x,e)::nil) ++ elements m)).
        apply (@SortA_app _ eqke). auto with typeclass_instances. auto. auto with map.
        intros.
        inversion_clear H1.
        destruct y; destruct x0.
        rewrite <- elements_mapsto_iff in H2.
        unfold KO.eqke, KO.ltk in *; simpl in *; destruct H3.
        apply eq_lt with x; auto.
        apply H; firstorder.
        inversion H3.
        red; intros a; destruct a.
        rewrite InA_cons, <- 2 elements_mapsto_iff,
          find_mapsto_iff, (H0 s), <- find_mapsto_iff,
          add_mapsto_iff.
        unfold KO.eqke; simpl. intuition.
        destruct (eq_dec x s) as [Heq|Hneq]; auto.
        exfalso.
        assert (In s m).
        exists e0; auto.
        generalize (H s H1).
        order.
      Qed.

      Lemma elements_Equal_eqlistA : forall (m m': t elt),
          Equal m m' -> eqlistA eqke (elements m) (elements m').
      Proof.
        intros.
        apply sort_equivlistA_eqlistA. 1-2: auto with map.
        red; intros.
        destruct x; do 2 rewrite <- elements_mapsto_iff.
        do 2 rewrite find_mapsto_iff; rewrite H; split; auto.
      Qed.

    End Elements.

    Section Min_Max_Elt.

      Fixpoint max_elt_aux (l:list (key * elt)) := match l with
                                                   | nil => None
                                                   | (x,e)::nil => Some (x,e)
                                                   | (x,e)::l => max_elt_aux l
                                                   end.
      Definition max_elt (m : t elt) := max_elt_aux (elements m).

      Lemma max_elt_Above :
        forall m x e, max_elt m = Some (x,e) -> Above x (remove x m).
      Proof.
        red; intros.
        rewrite remove_in_iff in H0.
        destruct H0.
        rewrite elements_in_iff in H1.
        destruct H1.
        unfold max_elt in *.
        generalize (elements_3 m).
        revert x e H y x0 H0 H1.
        induction (elements m).
        simpl; intros; try discriminate.
        intros.
        destruct a; destruct l; simpl in *.
        injection H as [= -> ->].
        inversion_clear H1.
        red in H; simpl in *; intuition.
        elim H0; eauto with ordered_type.
        inversion H.
        change (max_elt_aux (p::l) = Some (x,e)) in H.
        generalize (IHl x e H); clear IHl; intros IHl.
        inversion_clear H1; [ | inversion_clear H2; eauto ].
        red in H3; simpl in H3; destruct H3.
        destruct p as (p1,p2).
        destruct (eq_dec p1 x) as [Heq|Hneq].
        apply lt_eq with p1; auto.
        inversion_clear H2.
        inversion_clear H5.
        red in H2; simpl in H2; order.
        apply lt_trans with p1; auto.
        inversion_clear H2.
        inversion_clear H5.
        red in H2; simpl in H2; order.
        eapply IHl; eauto with ordered_type.
        econstructor; eauto.
        red; eauto with ordered_type.
        inversion H2; auto.
      Qed.

      Lemma max_elt_MapsTo :
        forall m x e, max_elt m = Some (x,e) -> MapsTo x e m.
      Proof.
        intros.
        unfold max_elt in *.
        rewrite elements_mapsto_iff.
        induction (elements m).
        simpl; try discriminate.
        destruct a; destruct l; simpl in *.
        injection H; intros; subst; constructor; red; auto with ordered_type.
        constructor 2; auto.
      Qed.

      Lemma max_elt_Empty :
        forall m, max_elt m = None -> Empty m.
      Proof.
        intros.
        unfold max_elt in *.
        rewrite elements_Empty.
        induction (elements m); auto.
        destruct a; destruct l; simpl in *; try discriminate.
        assert (H':=IHl H); discriminate.
      Qed.

      Definition min_elt (m : t elt) : option (key * elt) := match elements m with
                                                             | nil => None
                                                             | (x,e)::_ => Some (x,e)
                                                             end.

      Lemma min_elt_Below :
        forall m x e, min_elt m = Some (x,e) -> Below x (remove x m).
      Proof.
        unfold min_elt, Below; intros.
        rewrite remove_in_iff in H0; destruct H0.
        rewrite elements_in_iff in H1.
        destruct H1.
        generalize (elements_3 m).
        destruct (elements m).
        try discriminate.
        destruct p; injection H as [= -> ->]; intros H4.
        inversion_clear H1 as [? ? H2|? ? H2].
        red in H2; destruct H2; simpl in *; order.
        inversion_clear H4. rename H1 into H3.
        rewrite (@InfA_alt _ eqke) in H3 by auto with typeclass_instances.
        apply (H3 (y,x0)); auto.
      Qed.

      Lemma min_elt_MapsTo :
        forall m x e, min_elt m = Some (x,e) -> MapsTo x e m.
      Proof.
        intros.
        unfold min_elt in *.
        rewrite elements_mapsto_iff.
        destruct (elements m).
        simpl; try discriminate.
        destruct p; simpl in *.
        injection H; intros; subst; constructor; red; auto with ordered_type.
      Qed.

      Lemma min_elt_Empty :
        forall m, min_elt m = None -> Empty m.
      Proof.
        intros.
        unfold min_elt in *.
        rewrite elements_Empty.
        destruct (elements m); auto.
        destruct p; simpl in *; discriminate.
      Qed.

    End Min_Max_Elt.

    Section Induction_Principles.

      Lemma map_induction_max :
        forall P : t elt -> Type,
          (forall m, Empty m -> P m) ->
          (forall m m', P m -> forall x e, Above x m -> Add x e m m' -> P m') ->
          forall m, P m.
      Proof.
        intros; remember (cardinal m) as n; revert m Heqn; induction n; intros.
        apply X; apply cardinal_inv_1; auto.

        case_eq (max_elt m); intros.
        destruct p.
        assert (Add s e (remove s m) m).
        red; intros.
        rewrite add_o; rewrite remove_o; destruct (Orders.F.eq_dec s y); eauto.
        apply find_1; apply MapsTo_1 with s; auto.
        apply max_elt_MapsTo; auto.
        apply X0 with (remove s m) s e; auto with map.
        apply IHn.
        assert (S n = S (cardinal (remove s m))).
        rewrite Heqn.
        eapply cardinal_2; eauto with map ordered_type.
        inversion H1; auto.
        eapply max_elt_Above; eauto.

        apply X; apply max_elt_Empty; auto.
      Qed.

      Lemma map_induction_min :
        forall P : t elt -> Type,
          (forall m, Empty m -> P m) ->
          (forall m m', P m -> forall x e, Below x m -> Add x e m m' -> P m') ->
          forall m, P m.
      Proof.
        intros; remember (cardinal m) as n; revert m Heqn; induction n; intros.
        apply X; apply cardinal_inv_1; auto.

        case_eq (min_elt m); intros.
        destruct p.
        assert (Add s e (remove s m) m).
        red; intros.
        rewrite add_o; rewrite remove_o; destruct (O.eq_dec s y); eauto.
        apply find_1; apply MapsTo_1 with s; auto.
        apply min_elt_MapsTo; auto.
        apply X0 with (remove s m) s e; auto.
        apply IHn.
        assert (S n = S (cardinal (remove s m))).
        rewrite Heqn.
        eapply cardinal_2; eauto with map ordered_type.
        inversion H1; auto.
        eapply min_elt_Below; eauto.

        apply X; apply min_elt_Empty; auto.
      Qed.

    End Induction_Principles.

    Section Fold_properties.

      Lemma fold_Equal :
        forall (m1 m2 : t elt) (A : Type) (eqA : A -> A -> Prop) (st : Equivalence  eqA)
               (f : key -> elt -> A -> A) (i : A),
          Proper (oeq==>Logic.eq==>eqA==>eqA) f ->
          Equal m1 m2 ->
          eqA (fold f m1 i) (fold f m2 i).
      Proof.
        intros m1 m2 A eqA st f i Hf Heq.
        rewrite 2 fold_spec_right.
        apply fold_right_eqlistA with (eqA:=eqke) (eqB:=eqA); auto.
        intros (k,e) (k',e') (Hk,He) a a' Ha; simpl in *; apply Hf; auto.
        apply eqlistA_rev. apply elements_Equal_eqlistA. auto.
      Qed.

      Lemma fold_Add_Above : forall m1 m2 x e (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA)
                                    (f:key->elt->A->A)(i:A) (P:Proper (oeq==>Logic.eq==>eqA==>eqA) f),
          Above x m1 -> Add x e m1 m2 ->
          eqA (fold f m2 i) (f x e (fold f m1 i)).
      Proof.
        intros. rewrite 2 fold_spec_right. set (f':=uncurry f).
        transitivity (fold_right f' i (rev (elements m1 ++ (x,e)::nil))).
        apply fold_right_eqlistA with (eqA:=eqke) (eqB:=eqA); auto.
        intros (k1,e1) (k2,e2) (Hk,He) a1 a2 Ha; unfold f'; simpl in *. apply P; auto.
        apply eqlistA_rev.
        apply elements_Add_Above; auto.
        rewrite distr_rev; simpl.
        reflexivity.
      Qed.

      Lemma fold_Add_Below : forall m1 m2 x e (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA)
                                    (f:key->elt->A->A)(i:A) (P:Proper (oeq==>Logic.eq==>eqA==>eqA) f),
          Below x m1 -> Add x e m1 m2 ->
          eqA (fold f m2 i) (fold f m1 (f x e i)).
      Proof.
        intros. rewrite 2 fold_spec_right. set (f':=uncurry f).
        transitivity (fold_right f' i (rev (((x,e)::nil)++elements m1))).
        apply fold_right_eqlistA with (eqA:=eqke) (eqB:=eqA); auto.
        intros (k1,e1) (k2,e2) (Hk,He) a1 a2 Ha; unfold f'; simpl in *; apply P; auto.
        apply eqlistA_rev.
        simpl; apply elements_Add_Below; auto.
        rewrite distr_rev; simpl.
        rewrite fold_right_app.
        reflexivity.
      Qed.

    End Fold_properties.

  End OrdProperties.

End OP.


(** ** Additional Lemmas *)

From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Module L.

  Module F := F.
  Module P := P.
  Module OP := OP.

  Include F.
  Include OP.

  Import FS O FM P.

  Local Open Scope seq_scope.

  Local Notation eqb := Orders.F.eqb.

  Section FMapLemmas.

    Context {key : orderedType}.
    Context {t : fmapType key}.

    Variable elt elt' : Type.

    Lemma memP (k : key) (m : t elt) : reflect (In k m) (mem k m).
    Proof.
      case H: (mem k m).
      - apply: ReflectT. exact: (mem_2 H).
      - apply: ReflectF. move=> Hin; move: (mem_1 Hin). rewrite H; discriminate.
    Qed.

    Lemma find_some_mapsto (m : t elt) x e : find x m = Some e -> MapsTo x e m.
    Proof. exact: (proj2 (find_mapsto_iff m x e)). Qed.

    Lemma mapsto_find_some (m : t elt) x e : MapsTo x e m -> find x m = Some e.
    Proof. exact: (proj1 (find_mapsto_iff m x e)). Qed.

    Lemma find_none_not_in (m : t elt) x : find x m = None -> ~ In x m.
    Proof. exact: (proj2 (not_find_in_iff m x)). Qed.

    Lemma not_in_find_none (m : t elt) x : ~ In x m -> find x m = None.
    Proof. exact: (proj1 (not_find_in_iff m x)). Qed.

    Lemma find_some_in (m : t elt) x e : find x m = Some e -> In x m.
    Proof. move=> H; exists e. exact: (find_some_mapsto H). Qed.

    Lemma in_find_some (m : t elt) x : In x m -> exists e, find x m = Some e.
    Proof. move=> [e H]. exists e. exact: (mapsto_find_some H). Qed.

    Lemma find_none_not_mem (m : t elt) x : find x m = None -> mem x m = false.
    Proof. move=> H. apply/memP. exact: (find_none_not_in H). Qed.

    Lemma not_mem_find_none (m : t elt) x : ~~ mem x m -> find x m = None.
    Proof. move/memP=> H. exact: (not_in_find_none H). Qed.

    Lemma find_some_mem (m : t elt) x e : find x m = Some e -> mem x m.
    Proof. move=> H. apply/memP. exact: (find_some_in H). Qed.

    Lemma mem_find_some (m : t elt) x : mem x m -> exists e, find x m = Some e.
    Proof. move/memP=> H. exact: (in_find_some H). Qed.


    Lemma find_add_eq {m : t elt} {x y : key} {e : elt} :
      oeq x y -> find x (add y e m) = Some e.
    Proof.
      move=> Hxy. apply: add_eq_o. apply: O.eq_sym. exact: Hxy.
    Qed.

    Lemma find_add_neq {m : t elt} {x y : key} {e : elt} :
      ~(oeq x y) -> find x (add y e m) = find x m.
    Proof.
      move=> Hne. apply: add_neq_o. move=> Heq; apply: Hne; apply: O.eq_sym.
      exact: Heq.
    Qed.

    Lemma mem_add_eq {m : t elt} {x y : key} {e : elt} :
      oeq x y -> mem x (add y e m).
    Proof.
      move=> Hxy. apply: add_eq_b. apply: O.eq_sym. exact: Hxy.
    Qed.

    Lemma mem_add_neq {m : t elt} {x y : key} {e : elt} :
      ~ (oeq x y) -> mem x (add y e m) = mem x m.
    Proof.
      move=> Hne. apply: add_neq_b. move=> Heq; apply: Hne; apply: O.eq_sym.
      exact: Heq.
    Qed.

    Lemma find_some_map {f : elt -> elt'} {m : t elt} {x : key} {e : elt} :
      find x m = Some e ->
      find x (map f m) = Some (f e).
    Proof.
      move=> H. rewrite map_o. rewrite /option_map. rewrite H. reflexivity.
    Qed.

    Lemma find_none_map {f : elt -> elt'} {m : t elt} {x : key} :
      find x m = None ->
      find x (map f m) = None.
    Proof.
      move=> H. rewrite map_o. rewrite /option_map. rewrite H. reflexivity.
    Qed.

    Lemma find_map_some (f : elt -> elt') (m : t elt) (x : key) (e : elt') :
      find x (map f m) = Some e ->
      exists a, e = f a /\ find x m = Some a.
    Proof.
      move=> H. move: (find_2 H) => {} H. case: (map_mapsto_iff m x e f) => Hf _.
      move: (Hf H) => {H Hf} [] => a [Hea Hxa]. exists a. split.
      - assumption.
      - apply: find_1. assumption.
    Qed.

    Lemma find_map_none (f : elt -> elt') (m : t elt) (x : key) :
      find x (map f m) = None ->
      find x m = None.
    Proof.
      rewrite map_o. rewrite /option_map. case: (find x m).
      - discriminate.
      - reflexivity.
    Qed.

    Lemma mem_map (f : elt -> elt') (m : t elt) (x : key) :
      mem x (map f m) = mem x m.
    Proof. exact: map_b. Qed.

    Lemma Empty_mem (m : t elt) (x : key) :
      Empty m -> mem x m = false.
    Proof.
      move=> Hempty. apply/negP => Hmem. move/memP: Hmem => [e Hmapsto].
      move: (Hempty x e); apply. exact: Hmapsto.
    Qed.

    Lemma find_eq_mem_eq (m1 m2 : t elt) (x1 x2 : key) :
      find x1 m1 = find x2 m2 -> mem x1 m1 = mem x2 m2.
    Proof.
      case Hfind1: (find x1 m1); move=> Hfind2;
      rewrite mem_find_b mem_find_b Hfind1 -Hfind2; reflexivity.
    Qed.

    Lemma Empty_in (m : t elt) (x : key) :
      Empty m -> In x m -> False.
    Proof.
      move=> Hemp Hin. case: Hin => [v Hmapsto]. exact: (Hemp x v Hmapsto).
    Qed.

    Lemma Empty_not_mem (m : t elt) (x : key) :
      Empty m -> ~~ mem x m.
    Proof.
      move=> Hemp. apply/negP => Hmem. move/memP: Hmem. exact: Empty_in.
    Qed.

    Lemma Empty_find (m : t elt) (x : key) :
      Empty m -> find x m = None.
    Proof.
      move=> Hemp. move: (not_find_in_iff m x) => [H _]. apply: H => H.
      exact: (Empty_in Hemp H).
    Qed.

    Lemma find_some_none_neq (m : t elt) (x y : key) (v : elt) :
      find x m = Some v -> find y m = None ->
      ~ (oeq x y).
    Proof.
      move=> Hx Hy Heq. rewrite (F.find_o _ Heq) in Hx. rewrite Hx in Hy. discriminate.
    Qed.

    Lemma Add_mem_add x k e (m m' : t elt) :
      Add k e m m' ->
      mem x m' = mem x (add k e m).
    Proof.
      move=> Hadd. move: (Hadd x). rewrite 2!mem_find_b.
      move=> ->. reflexivity.
    Qed.

    Lemma Add_in k e (m m' : t elt) :
      Add k e m m' -> In k m'.
    Proof.
      move=> Hadd. move: (Hadd k). rewrite (add_eq_o _ _ (O.eq_refl k)).
      exact: find_some_in.
    Qed.

    Lemma in_Add_in k e k' (m m' : t elt) :
      In k' m -> Add k e m m' -> In k' m'.
    Proof.
      move=> Hin Hadd. case: (O.eq_dec k k').
      - move=> Heq. rewrite -Heq. exact: (Add_in Hadd).
      - move=> Hneq. apply/memP. rewrite (Add_mem_add k' Hadd).
        rewrite (add_neq_b _ _ Hneq). apply/memP. exact: Hin.
    Qed.

    Lemma mem_combine_cons (x : key) k (keys : list key) v (vals : list elt) :
      (mem (t:=t) x (of_list (List.combine (k::keys) (v::vals)))) =
       ((eqb k x) || (mem (t:=t) x (of_list (List.combine keys vals)))).
    Proof.
      rewrite /= /uncurry /=. rewrite /eqb. case: (O.eq_dec k x).
      - move=> Heq. rewrite (F.add_eq_b _ _ Heq) orTb. reflexivity.
      - move=> Hneq. rewrite (F.add_neq_b _ _ Hneq) orFb. reflexivity.
    Qed.

    Lemma mem_combine_in (x : key) (keys : list key) (vals : list elt) :
      mem (t:=t) x (of_list (List.combine keys vals)) ->
      SetoidList.InA oeq x keys.
    Proof.
      elim: keys vals.
      - move=> /= vals Hmem. rewrite empty_a in Hmem. discriminate.
      - move=> key_hd key_tl IH. case.
        + move=> /= Hmem. rewrite empty_a in Hmem. discriminate.
        + move=> val_hd val_tl Hmem. rewrite mem_combine_cons in Hmem.
          move/orP: Hmem; case.
          * rewrite /eqb /=. case: (O.eq_dec key_hd x); last by discriminate.
            move=> H _. apply: InA_cons_hd. apply: O.eq_sym. exact: H.
          * move=> H. apply: InA_cons_tl. exact: (IH _ H).
    Qed.

    Lemma add_diag (x : key) (e : elt) (m : t elt) :
      Equal (add x e (add x e m)) (add x e m).
    Proof.
      move=> y. case: (O.eq_dec y x).
      - move=> Hyx. rewrite !(find_add_eq Hyx). reflexivity.
      - move=> Hyx. rewrite !(find_add_neq Hyx). reflexivity.
    Qed.

    Lemma add_same (x : key) (e : elt) (m : t elt) :
      find x m = Some e -> Equal (add x e m) m.
    Proof.
      move=> Hfind y. case: (O.eq_dec y x) => Hyx.
      - rewrite (find_add_eq Hyx). rewrite -Hfind Hyx. reflexivity.
      - rewrite (find_add_neq Hyx). reflexivity.
    Qed.

    Lemma add_comm (x1 x2 : key) (e1 e2 : elt) (m : t elt) :
      ~ oeq x1 x2 ->
      Equal (add x1 e1 (add x2 e2 m)) (add x2 e2 (add x1 e1 m)).
    Proof.
      move=> Hne y. case: (O.eq_dec y x1); case: (O.eq_dec y x2).
      - move=> Heq2 Heq1. apply: False_ind. apply: Hne. rewrite -Heq1 -Heq2.
        reflexivity.
      - move=> Hne2 Heq1. rewrite (find_add_eq Heq1) (find_add_neq Hne2).
        rewrite (find_add_eq Heq1). reflexivity.
      - move=> Heq2 Hne1. rewrite (find_add_neq Hne1) !(find_add_eq Heq2).
        reflexivity.
      - move=> Hne2 Hne1. rewrite (find_add_neq Hne1) !(find_add_neq Hne2).
        rewrite (find_add_neq Hne1). reflexivity.
    Qed.

    Lemma add2_equal k1 k2 v (m1 m2 : t elt) :
      oeq k1 k2 ->
      Equal m1 m2 ->
      Equal (add k1 v m1) (add k2 v m2).
    Proof. move=> Heq. by apply: F.add_m. Qed.

  End FMapLemmas.


  Section Proper.

    Context {key : orderedType}.
    Context {t : fmapType key}.

    Variable elt elt' : Type.
    Variable f : elt -> elt'.

    Global Instance add_f_proper :
      Proper (oeq ==> Logic.eq ==> (@Equal key t elt') ==> (@Equal key t elt'))
             (fun (k : key) (e : elt) (m : t elt') => add k (f e) m).
    Proof.
      move=> x1 x2 Heqx. move=> y1 y2 Heqy. move=> m1 m2 Heqm.
      have Heq: (f y1 = f y2) by rewrite Heqy. exact: (add_m Heqx Heq Heqm).
    Qed.

    Lemma add_f_transpose_neqkey :
      transpose_neqkey
        (Equal (elt:=elt'))
        (fun (k : key) (e : elt) (m : t elt') => add k (f e) m).
    Proof.
      move=> k1 k2 e1 e2 m Hneq x. rewrite 4!add_o.
      case: (eq_dec k1 x); case: (eq_dec k2 x); try reflexivity.
      move=> Heq2 Heq1. move: (O.eq_sym Heq2) => {} Heq2.
      move: (O.eq_trans Heq1 Heq2) => Heq. apply: False_ind; apply: Hneq.
      exact: Heq.
    Qed.

  End Proper.


  Section Split.

    Context {key : orderedType}.
    Context {t : fmapType key}.

    Variable elt elt' : Type.

    Local Open Scope type_scope.

    Definition split (m : t (elt * elt')) : (t elt) * (t elt') :=
      (fold (fun k e m1 => add k (fst e) m1) m (empty elt),
        fold (fun k e m2 => add k (snd e) m2) m (empty elt')).

    Lemma mem_split1 (m : t (elt * elt')) (x : key) :
      mem x m = mem x (fst (split m)).
    Proof.
      rewrite /split /=. move: m. eapply map_induction.
      - move=> m Hemp. rewrite (fold_Empty (Equal_ST elt) _ _ Hemp).
        rewrite empty_a. rewrite (negbTE (Empty_not_mem _ Hemp)). reflexivity.
      - move=> m m' IH y e Hin Hadd. rewrite (Add_mem_add _ Hadd).
        rewrite (fold_Add (Equal_ST elt)
                          (add_f_proper fst)
                          (add_f_transpose_neqkey fst) _ Hin Hadd).
        case: (eq_dec y x).
        + move=> Heq. rewrite 2!(add_eq_b _ _ Heq). reflexivity.
        + move=> Hneq. rewrite 2!(add_neq_b _ _ Hneq). exact: IH.
    Qed.

    Lemma mem_split2 (m : t (elt * elt')) (x : key) :
      mem x m = mem x (snd (split m)).
    Proof.
      rewrite /split /=. move: m. eapply map_induction.
      - move=> m Hemp. rewrite (fold_Empty (Equal_ST elt') _ _ Hemp).
        rewrite empty_a. rewrite (negbTE (Empty_not_mem x Hemp)). reflexivity.
      - move=> m m' IH y e Hin Hadd. rewrite (Add_mem_add _ Hadd).
        rewrite (fold_Add (Equal_ST elt')
                          (add_f_proper snd)
                          (add_f_transpose_neqkey snd) _ Hin Hadd).
        case: (eq_dec y x).
        + move=> Heq. rewrite 2!(add_eq_b _ _ Heq). reflexivity.
        + move=> Hneq. rewrite 2!(add_neq_b _ _ Hneq). exact: IH.
    Qed.

    Lemma find_split1_none (m : t (elt * elt')) (x : key) :
      find x m = None ->
      find x (fst (split m)) = None.
    Proof.
      rewrite /split /=. move: m. apply: map_induction.
      - move=> m Hemp. rewrite (fold_Empty (Equal_ST elt) _ _ Hemp).
        rewrite empty_o. reflexivity.
      - move=> m m' IH y e Hin Hadd. rewrite (Hadd x).
        rewrite (fold_Add (Equal_ST elt)
                          (add_f_proper fst)
                          (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite 2!add_o. case: (eq_dec y x).
        + discriminate.
        + move=> _ H. exact: (IH H).
    Qed.

    Lemma find_split2_none (m : t (elt * elt')) (x : key) :
      find x m = None ->
      find x (snd (split m)) = None.
    Proof.
      rewrite /split /=. move: m. apply: map_induction.
      - move=> m Hemp. rewrite (fold_Empty (Equal_ST elt') _ _ Hemp).
        rewrite empty_o. reflexivity.
      - move=> m m' IH y e Hin Hadd. rewrite (Hadd x).
        rewrite (fold_Add (Equal_ST elt')
                          (add_f_proper snd)
                          (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 2!add_o. case: (eq_dec y x).
        + discriminate.
        + move=> _ H. exact: (IH H).
    Qed.

    Lemma find_split1_some (m : t (elt * elt')) (x : key) e1 e2 :
      find x m = Some (e1, e2) ->
      find x (fst (split m)) = Some e1.
    Proof.
      rewrite /split /=. move: m e1 e2. apply: map_induction.
      - move=> m Hemp e1 e2. rewrite (Empty_find _ Hemp). discriminate.
      - move=> m m' IH y e Hin Hadd e1 e2. rewrite (Hadd x).
        rewrite (fold_Add (Equal_ST elt)
                          (add_f_proper fst)
                          (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite 2!add_o. case: (eq_dec y x).
        + move=> Heq [] He. by rewrite He.
        + move=> Hneq H. exact: (IH _ _ H).
    Qed.

    Lemma find_split2_some (m : t (elt * elt')) (x : key) e1 e2 :
      find x m = Some (e1, e2) ->
      find x (snd (split m)) = Some e2.
    Proof.
      rewrite /split /=. move: m e1 e2. apply: map_induction.
      - move=> m Hemp e1 e2. rewrite (Empty_find _ Hemp). discriminate.
      - move=> m m' IH y e Hin Hadd e1 e2. rewrite (Hadd x).
        rewrite (fold_Add (Equal_ST elt')
                          (add_f_proper snd)
                          (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 2!add_o. case: (eq_dec y x).
        + move=> Heq [] He. by rewrite He.
        + move=> Hneq H. exact: (IH _ _ H).
    Qed.

    Lemma split1_find_none (m : t (elt * elt')) (x : key) :
      find x (fst (split m)) = None ->
      find x m = None.
    Proof.
      rewrite /split /=. move: m. apply: map_induction.
      - move=> m Hemp _. exact: (Empty_find _ Hemp).
      - move=> m m' IH y e Hin Hadd. rewrite (Hadd x).
        rewrite (fold_Add (Equal_ST elt)
                          (add_f_proper fst)
                          (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite 2!add_o. case: (eq_dec y x).
        + discriminate.
        + move=> _ H. exact: (IH H).
    Qed.

    Lemma split2_find_none (m : t (elt * elt')) (x : key) :
      find x (snd (split m)) = None ->
      find x m = None.
    Proof.
      rewrite /split /=. move: m. apply: map_induction.
      - move=> m Hemp _. exact: (Empty_find _ Hemp).
      - move=> m m' IH y e Hin Hadd. rewrite (Hadd x).
        rewrite (fold_Add (Equal_ST elt')
                          (add_f_proper snd)
                          (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 2!add_o. case: (eq_dec y x).
        + discriminate.
        + move=> _ H. exact: (IH H).
    Qed.

    Lemma split1_find_some (m : t (elt * elt')) (x : key) e1 :
      find x (fst (split m)) = Some e1 ->
      exists e2, find x m = Some (e1, e2).
    Proof.
      rewrite /split /=. move: m e1. apply: map_induction.
      - move=> m Hemp e1. rewrite (fold_Empty (Equal_ST elt) _ _ Hemp).
        rewrite empty_o. discriminate.
      - move=> m m' IH y e Hin Hadd e1. rewrite (Hadd x).
        rewrite (fold_Add (Equal_ST elt)
                          (add_f_proper fst)
                          (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite 2!add_o. case: (eq_dec y x).
        + move=> Heq [] He. exists (snd e). rewrite -He -surjective_pairing.
          reflexivity.
        + move=> Hneq H. exact: (IH _ H).
    Qed.

    Lemma split2_find_some (m : t (elt * elt')) (x : key) e2 :
      find x (snd (split m)) = Some e2 ->
      exists e1, find x m = Some (e1, e2).
    Proof.
      rewrite /split /=. move: m e2. apply: map_induction.
      - move=> m Hemp e2. rewrite (fold_Empty (Equal_ST elt') _ _ Hemp).
        rewrite empty_o. discriminate.
      - move=> m m' IH y e Hin Hadd e2. rewrite (Hadd x).
        rewrite (fold_Add (Equal_ST elt')
                          (add_f_proper snd)
                          (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 2!add_o. case: (eq_dec y x).
        + move=> Heq [] He. exists (fst e). rewrite -He -surjective_pairing.
          reflexivity.
        + move=> Hneq H. exact: (IH _ H).
    Qed.

    Lemma split_find_some (m : t (elt * elt')) (x : key) e1 e2 :
      find x (fst (split m)) = Some e1 ->
      find x (snd (split m)) = Some e2 ->
      find x m = Some (e1, e2).
    Proof.
      rewrite /split /=. move: m e1 e2. apply: map_induction.
      - move=> m Hemp e1 e2. rewrite (fold_Empty (Equal_ST elt) _ _ Hemp).
        rewrite empty_o. discriminate.
      - move=> m m' IH y e Hin Hadd e1 e2. rewrite (Hadd x).
        rewrite (fold_Add (Equal_ST elt)
                          (add_f_proper fst)
                          (add_f_transpose_neqkey fst) _ Hin Hadd).
        rewrite (fold_Add (Equal_ST elt')
                          (add_f_proper snd)
                          (add_f_transpose_neqkey snd) _ Hin Hadd).
        rewrite 3!add_o. case: (eq_dec y x).
        + move=> Heq [] He1 [] He2. rewrite -He1 -He2 -surjective_pairing.
          reflexivity.
        + move=> Hneq H1 H2. exact: (IH _ _ H1 H2).
    Qed.

  End Split.


  Section Submap.

    Context {key : orderedType}.
    Context {t : fmapType key}.

    Unset Implicit Arguments.

    Context {elt : Type}.

    Definition submap (m m' : t elt) :=
      forall {k v}, find k m = Some v -> find k m' = Some v.

    Lemma submap_refl (m : t elt) : submap m m.
    Proof. move=> k v Hfind. exact: Hfind. Qed.

    Lemma submap_trans {m2 m1 m3 : t elt} :
      submap m1 m2 -> submap m2 m3 -> submap m1 m3.
    Proof.
      move=> H12 H23 k v Hf1. apply: H23. apply: H12. exact: Hf1.
    Qed.

    Lemma submap_none_add {m1 m2 : t elt} {k : key} (e : elt) :
      submap m1 m2 -> find k m1 = None -> submap m1 (add k e m2).
    Proof.
      move=> Hsub Hfind k' v' Hfind'. rewrite add_o. case: (eq_dec k k').
      - move=> Heq. rewrite (find_o m1 Heq) in Hfind. rewrite Hfind in Hfind'.
        discriminate.
      - move=> Hneq. exact: (Hsub k' v' Hfind').
    Qed.

    Lemma submap_not_mem_add {m1 m2 : t elt} {k : key} (e : elt) :
      submap m1 m2 -> ~~ mem k m1 -> submap m1 (add k e m2).
    Proof.
      move=> Hsub Hmem. exact: (submap_none_add _ Hsub (not_mem_find_none Hmem)).
    Qed.

    Lemma submap_some_add {m1 m2 : t elt} {k : key} {e : elt} :
      submap m1 m2 -> find k m1 = Some e -> submap m1 (add k e m2).
    Proof.
      move=> Hsub Hfind k' v' Hfind'. rewrite add_o. case: (eq_dec k k').
      - move=> Heq. rewrite (F.find_o m1 Heq) in Hfind. rewrite Hfind in Hfind'.
        exact: Hfind'.
      - move=> Hneq. exact: (Hsub k' v' Hfind').
    Qed.

    Lemma submap_add_diag {m : t elt} {k : key} (e : elt) :
      ~~ mem k m -> submap m (add k e m).
    Proof.
      move=> Hmem. apply: (submap_not_mem_add _ _ Hmem). exact: submap_refl.
    Qed.

    Lemma submap_mem {m1 m2 : t elt} {k : key} :
      submap m1 m2 -> mem k m1 -> mem k m2.
    Proof.
      move=> Hsub Hmem1. move: (mem_find_some Hmem1) => {Hmem1} [e Hfind1].
      move: (Hsub k e Hfind1) => Hfind2. exact: (find_some_mem Hfind2).
    Qed.

    Lemma submap_add_find {m1 m2 : t elt} {k : key} {e : elt} :
      submap (add k e m1) m2 -> find k m2 = Some e.
    Proof.
      move=> H. apply: (H k e). rewrite (find_add_eq (O.eq_refl k)). reflexivity.
    Qed.

    Lemma submap_add_find_none {m1 m2 : t elt} {k : key} {e : elt} :
      submap (add k e m1) m2 -> find k m1 = None -> submap m1 m2.
    Proof.
      move=> H Hfindk1 x ex Hfindx1. apply: H. case: (eq_dec x k).
      - move=> Heq. apply: False_ind. rewrite (F.find_o _ Heq) Hfindk1 in Hfindx1.
        discriminate.
      - move=> Hne. rewrite (find_add_neq Hne). assumption.
    Qed.

    Lemma submap_add_not_mem {m1 m2 : t elt} {k : key} {e : elt} :
      submap (add k e m1) m2 -> ~~ mem k m1 -> submap m1 m2.
    Proof.
      move=> H Hmem. move: (not_mem_find_none Hmem) => Hfind.
      exact: (submap_add_find_none H Hfind).
    Qed.

    Lemma submap_Equal {m1 m2 : t elt} :
      submap m1 m2 -> submap m2 m1 -> Equal m1 m2.
    Proof.
      move=> Hsub12 Hsub21. move=> x. case Hfind1: (find x m1).
      - rewrite (Hsub12 _ _ Hfind1). reflexivity.
      - case Hfind2: (find x m2).
        + rewrite (Hsub21 _ _ Hfind2) in Hfind1. discriminate.
        + reflexivity.
    Qed.

    Lemma Equal_submap {m1 m2 : t elt} : Equal m1 m2 -> submap m1 m2.
    Proof.
      move=> Heq x v Hfind. rewrite (Heq x) in Hfind. exact: Hfind.
    Qed.

    Lemma submap_add {te1 te2: t elt} x v :
      submap te1 te2 ->
      submap (add x v te1) (add x v te2).
    Proof.
      move=> Hsm k typ. case: (eq_dec k x).
      - move=> H. by rewrite !(find_add_eq H).
      - move=> Hne. rewrite !(find_add_neq Hne). exact: Hsm.
    Qed.

    Set Implicit Arguments.

  End Submap.


  Section MaxMin.

    Context {key : orderedType}.
    Context {t : fmapType key}.

    Variable elt : Type.

    Lemma eqb_key_refl : forall (k : key), eqb k k.
    Proof.
      move=> k. rewrite /eqb. case: (eq_dec k k); first by done.
      move=> H; apply: False_ind; apply: H. exact: O.eq_refl.
    Qed.

    (* max_key *)

    Definition max_opt (k : key) (o : option key) : key :=
      match o with
      | None => k
      | Some k' => match ocompare k k' with
                   | LT _ => k'
                   | _ => k
                   end
      end.

    Lemma max_opt_cases k x o :
      max_opt k o = x ->
      (o = None /\ x = k) \/
      (exists k', o = Some k' /\ olt k k' /\ x = k') \/
      (exists k', o = Some k' /\ ~(olt k k') /\ x = k).
    Proof.
      case: o=> /=.
      - move=> k'. dcase (ocompare k k'). case.
        + move=> Hlt Hcomp Hx. right; left. exists k'. rewrite -Hx.
          repeat split; try reflexivity. exact: Hlt.
        + move=> Heq Hcomp Hx. right; right. exists k'. rewrite -Hx.
          repeat split; try reflexivity. exact: (Orders.F.eq_not_lt Heq).
        + move=> Hgt Hcomp Hx. right; right. exists k'. rewrite -Hx.
          repeat split; try reflexivity. move=> Hlt. move: (O.lt_trans Hgt Hlt).
          exact: (@Orders.F.lt_antirefl _ k').
      - move=> Hx. rewrite -Hx. by left.
    Qed.

    Lemma max_opt_none k : max_opt k None = k.
    Proof. reflexivity. Qed.

    Lemma max_opt_lt k k' : olt k k' -> max_opt k (Some k') = k'.
    Proof.
      move=> Hlt /=. move: (Orders.F.elim_compare_lt Hlt)=> {Hlt} [Hlt ->].
      reflexivity.
    Qed.

    Lemma max_opt_eq k k' : oeq k k' -> max_opt k (Some k') = k.
    Proof.
      move=> Heq /=. move: (Orders.F.elim_compare_eq Heq) => {Heq} [Heq ->].
      reflexivity.
    Qed.

    Lemma max_opt_gt k k' : olt k' k -> max_opt k (Some k') = k.
    Proof.
      move=> Hgt /=. move: (Orders.F.elim_compare_gt Hgt) => {Hgt} [Hgt ->].
      reflexivity.
    Qed.

    Lemma max_opt_not_lt_l k o x : max_opt k o = x -> ~ olt x k.
    Proof.
      move=> Hmax. case: (max_opt_cases Hmax); last case.
      - move=> [Ho Hx]. rewrite Hx. exact: (@Orders.F.lt_antirefl _ k).
      - move=> [k' [Ho [Hlt Hx]]]. rewrite Hx => H. move: (O.lt_trans Hlt H).
        exact: (@Orders.F.lt_antirefl _ k).
      - move=> [k' [Ho [Hlt Hx]]]. rewrite Hx. exact: (@Orders.F.lt_antirefl _ k).
    Qed.

    Lemma max_opt_not_lt_r k k' x : max_opt k (Some k') = x -> ~ olt x k'.
    Proof.
      move=> Hmax. case: (max_opt_cases Hmax); last case.
      - move=> [H1 H2]; discriminate.
      - move=> [k'' [[] Hk'' [Hk Hx]]]. rewrite Hx -Hk''.
        exact: (@Orders.F.lt_antirefl _ k').
      - move=> [k'' [[] Hk'' [Hk Hx]]]. rewrite Hx Hk''. assumption.
    Qed.

    Fixpoint max_key_elements (l : list (key * elt)) : option key :=
      match l with
      | [::] => None
      | (k, _)::tl => Some (max_opt k (max_key_elements tl))
      end.

    Definition max_key (m : t elt) : option key :=
      max_key_elements (elements m).

    Lemma max_key_elements_mem :
      forall (elements : seq (key * elt)) (k : key),
        max_key_elements elements = Some k ->
        existsb (fun p : key * elt => eqb k (fst p)) elements.
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
      forall (m : t elt) k, max_key m = Some k -> mem k m.
    Proof.
      rewrite /max_key=> m k Hmax. rewrite elements_b. move: k Hmax.
      move: (elements m) => {m}. exact: max_key_elements_mem.
    Qed.

    Lemma max_key_elements_none :
      forall l, max_key_elements l = None -> l = [::].
    Proof.
      case => /=.
      - reflexivity.
      - move=> [k v] tl H. discriminate.
    Qed.

    Lemma max_key_none :
      forall (m : t elt), max_key m = None -> Empty m.
    Proof.
      rewrite /max_key=> m Hmax. apply/elements_Empty. move: Hmax.
      move: (elements m) => {m}. exact: max_key_elements_none.
    Qed.

    Lemma max_key_elements_not_lt :
      forall (elements : seq (key * elt)) (k1 k2 : key),
        max_key_elements elements = Some k1 ->
        existsb (fun p : key * elt => eqb k2 (fst p)) elements -> ~ olt k1 k2.
    Proof.
      elim=> /=.
      - discriminate.
      - move=> [k_hd v_hd] tl IH k1 k2 [] Hmax /=. case/orP.
        + move=> Hk2 Hlt. apply: (max_opt_not_lt_l Hmax).
          move/Orders.F.eqb_eq: Hk2 => Hk2. exact: (Orders.F.lt_eq Hlt Hk2).
        + case: (max_opt_cases Hmax); last case.
          * move=> [Hmax_tl Hk1]. rewrite (max_key_elements_none Hmax_tl) /=. done.
          * move=> [k_tl [Hmax_tl [Hk_tl Hk1]]]. move=> H; apply: (IH _ _ _ H).
            rewrite Hk1; assumption.
          * move=> [k_tl [Hmax_tl [Hk_tl Hk1]]]. move=> H. move: (IH _ _ Hmax_tl H).
            move=> Hlt_tl Hlt_k1. rewrite Hk1 in Hlt_k1 => {Hmax Hk1}.
            case: (Orders.F.lt_total k_hd k_tl); last case; move=> Hlt_hd.
            -- apply: Hk_tl; assumption.
            -- apply: Hlt_tl. exact: (Orders.F.eq_lt (O.eq_sym Hlt_hd) Hlt_k1).
            -- apply: Hlt_tl. exact: (O.lt_trans Hlt_hd Hlt_k1).
    Qed.

    Lemma max_key_not_lt :
      forall (m : t elt) k1 k2,
        max_key m = Some k1 -> mem k2 m -> ~ olt k1 k2.
    Proof.
      rewrite /max_key=> m k1 k2. rewrite elements_b. move: k1 k2.
      move: (elements m) => {m}. exact: max_key_elements_not_lt.
    Qed.

    (* min_key *)

    Definition min_opt (k : key) (o : option key) : key :=
      match o with
      | None => k
      | Some k' => match ocompare k k' with
                   | GT _ => k'
                   | _ => k
                   end
      end.

    Lemma min_opt_cases k x o :
      min_opt k o = x ->
      (o = None /\ x = k) \/
      (exists k', o = Some k' /\ olt k' k /\ x = k') \/
      (exists k', o = Some k' /\ ~(olt k' k) /\ x = k).
    Proof.
      case: o=> /=.
      - move=> k'. dcase (ocompare k k'). case.
        + move=> Hlt Hcomp Hx. right; right; exists k'. rewrite -Hx.
          repeat split; try reflexivity. exact: (Orders.F.lt_le Hlt).
        + move=> Heq Hcomp Hx. right; right; exists k'. rewrite -Hx.
          repeat split; try reflexivity. exact: (Orders.F.eq_not_lt (O.eq_sym Heq)).
        + move=> Hgt Hcomp Hx. right; left; exists k'. rewrite -Hx.
          repeat split; try reflexivity. assumption.
      - move=> Hx. rewrite -Hx. by left.
    Qed.

    Lemma min_opt_none k : min_opt k None = k.
    Proof. reflexivity. Qed.

    Lemma min_opt_lt k k' : olt k k' -> min_opt k (Some k') = k.
    Proof.
      move=> Hlt /=. move: (Orders.F.elim_compare_lt Hlt)=> {Hlt} [Hlt ->].
      reflexivity.
    Qed.

    Lemma min_opt_eq k k' : O.eq k k' -> min_opt k (Some k') = k.
    Proof.
      move=> Heq /=. move: (Orders.F.elim_compare_eq Heq) => {Heq} [Heq ->].
      reflexivity.
    Qed.

    Lemma min_opt_gt k k' : olt k' k -> min_opt k (Some k') = k'.
    Proof.
      move=> Hgt /=. move: (Orders.F.elim_compare_gt Hgt) => {Hgt} [Hgt ->].
      reflexivity.
    Qed.

    Lemma min_opt_not_lt_l k o x : min_opt k o = x -> ~ olt k x.
    Proof.
      move=> Hmin. case: (min_opt_cases Hmin); last case.
      - move=> [Ho Hx]. rewrite Hx. exact: (@Orders.F.lt_antirefl _ k).
      - move=> [k' [Ho [Hlt Hx]]]. rewrite Hx => H. move: (O.lt_trans Hlt H).
        exact: (@Orders.F.lt_antirefl _ k').
      - move=> [k' [Ho [Hlt Hx]]]. rewrite Hx. exact: (@Orders.F.lt_antirefl _ k).
    Qed.

    Lemma min_opt_not_lt_r k k' x : min_opt k (Some k') = x -> ~ olt k' x.
    Proof.
      move=> Hmin. case: (min_opt_cases Hmin); last case.
      - move=> [H1 H2]; discriminate.
      - move=> [k'' [[] Hk'' [Hk Hx]]]. rewrite Hx -Hk''.
        exact: (@Orders.F.lt_antirefl _ k').
      - move=> [k'' [[] Hk'' [Hk Hx]]]. rewrite Hx Hk''. assumption.
    Qed.

    Fixpoint min_key_elements (l : list (key * elt)) : option key :=
      match l with
      | [::] => None
      | (k, _)::tl => Some (min_opt k (min_key_elements tl))
      end.

    Definition min_key (m : t elt) : option key :=
      min_key_elements (elements m).

    Lemma min_key_elements_mem :
      forall (elements : seq (key * elt)) (k : key),
        min_key_elements elements = Some k ->
        existsb (fun p : key * elt => eqb k (fst p)) elements.
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
      forall (m : t elt) k, min_key m = Some k -> mem k m.
    Proof.
      rewrite /min_key=> m k Hmin. rewrite elements_b. move: k Hmin.
      move: (elements m) => {m}. exact: min_key_elements_mem.
    Qed.

    Lemma min_key_elements_none :
      forall l, min_key_elements l = None -> l = [::].
    Proof.
      case => /=.
      - reflexivity.
      - move=> [k v] tl H. discriminate.
    Qed.

    Lemma min_key_none :
      forall (m : t elt), min_key m = None -> Empty m.
    Proof.
      rewrite /min_key=> m Hmin. apply/elements_Empty. move: Hmin.
      move: (elements m) => {m}. exact: min_key_elements_none.
    Qed.

    Lemma min_key_elements_not_lt :
      forall (elements : seq (key * elt)) (k1 k2 : key),
        min_key_elements elements = Some k1 ->
        existsb (fun p : key * elt => eqb k2 (fst p)) elements -> ~ olt k2 k1.
    Proof.
      elim=> /=.
      - discriminate.
      - move=> [k_hd v_hd] tl IH k1 k2 [] Hmin /=. case/orP.
        + move=> Hk2 Hlt. apply: (min_opt_not_lt_l Hmin).
          move/Orders.F.eqb_eq: Hk2 => Hk2. exact: (Orders.F.eq_lt (O.eq_sym Hk2) Hlt).
        + case: (min_opt_cases Hmin); last case.
          * move=> [Hmin_tl Hk1]. rewrite (min_key_elements_none Hmin_tl) /=. done.
          * move=> [k_tl [Hmin_tl [Hk_tl Hk1]]]. move=> H; apply: (IH _ _ _ H).
            rewrite Hk1; assumption.
          * move=> [k_tl [Hmin_tl [Hk_tl Hk1]]]. move=> H. move: (IH _ _ Hmin_tl H).
            move=> Hlt_tl Hlt_k1. rewrite Hk1 in Hlt_k1 => {Hmin Hk1}.
            case: (Orders.F.lt_total k_hd k_tl); last case; move=> Hlt_hd.
            -- apply: Hlt_tl. exact: (O.lt_trans Hlt_k1 Hlt_hd).
            -- apply: Hlt_tl. exact: (Orders.F.lt_eq Hlt_k1 Hlt_hd).
            -- apply: Hk_tl; assumption.
    Qed.

    Lemma min_key_not_lt :
      forall (m : t elt) k1 k2,
        min_key m = Some k1 -> mem k2 m -> ~ olt k2 k1.
    Proof.
      rewrite /min_key=> m k1 k2. rewrite elements_b. move: k1 k2.
      move: (elements m) => {m}. exact: min_key_elements_not_lt.
    Qed.

  End MaxMin.


  Section KeySet.

    Context {key : orderedType}.
    Context {s : fsetType key}.
    Context {t : fmapType key}.

    Variable elt : Type.

    Definition add_to_set x (e : elt) (ks : s) := FS.add x ks.

    (* Return the keys as a set *)
    Definition key_set (m : t elt) : s := fold add_to_set m FS.empty.

    Global Instance add_to_set_m :
      Proper (oeq ==> Logic.eq ==> FS.Equal ==> FS.Equal) add_to_set.
    Proof.
      move=> x y Hxy a b -> s1 s2 Heq. rewrite /add_to_set Hxy Heq. reflexivity.
    Qed.

    Global Instance key_set_m :
      Proper ((@Equal key t elt) ==> FS.Equal) key_set.
    Proof.
      move=> m1 m2 Heq. rewrite /key_set. apply: fold_Equal. assumption.
    Qed.

    Lemma add_to_set_transpose_neqkey :
      transpose_neqkey FS.Equal add_to_set.
    Proof.
      move=> x y a b ks Hxy. rewrite /add_to_set. exact: Sets.P.add_add.
    Qed.

    Lemma key_set_Empty m : Empty m -> FS.Empty (key_set m).
    Proof.
      rewrite /key_set => Hempty.
      rewrite (fold_Empty Sets.F.Equal_ST add_to_set FS.empty Hempty).
      exact: FS.empty_1.
    Qed.

    Lemma key_set_empty : key_set (empty elt) = FS.empty.
    Proof. rewrite /key_set. apply: fold_Empty. exact: empty_1. Qed.

    Lemma mem_key_set1 m :
      forall x, mem x m -> FS.mem x (key_set m).
    Proof.
      rewrite /key_set. eapply fold_rec.
      - move=> {} m Hempty x Hmem. rewrite (Empty_mem x Hempty) in Hmem.
        discriminate.
      - move=> x e m' E1 E2 _ _ Hadd Hind y Hmem. case: (O.eq_dec y x) => Hyx.
        + exact: (Sets.L.mem_add_eq _ Hyx).
        + rewrite (Sets.L.mem_add_neq Hyx). apply: Hind. move: (Hadd y) => {Hadd}.
          rewrite (find_add_neq Hyx) => {Hyx} Hfind.
          rewrite -(find_eq_mem_eq Hfind). exact: Hmem.
    Qed.

    Lemma mem_key_set2 m x : FS.mem x (key_set m) -> mem x m.
    Proof.
      move: m x. apply: map_induction.
      - move=> m Hempty x Hmem. move: (key_set_Empty Hempty) => {} Hempty.
        apply: False_ind. apply: (Hempty x). apply/Sets.L.memP. assumption.
      - move=> m m' IH x e Hin HAdd y Hmem. rewrite (Add_mem_add _ HAdd).
        case: (O.eq_dec y x) => Hyx.
        + rewrite Hyx in Hmem *. apply: mem_add_eq. reflexivity.
        + rewrite (mem_add_neq Hyx). rewrite /key_set in Hmem.
          move: (fold_Add
                   Sets.L.Equal_ST add_to_set_m
                   add_to_set_transpose_neqkey
                   FS.empty Hin HAdd) => Heq.
          move/Sets.L.memP: Hmem => Hiny. move: (Heq y) => {Heq} [H _].
          move: (H Hiny) => {H Hiny}. rewrite /add_to_set. move/Sets.L.memP.
          rewrite (Sets.L.mem_add_neq Hyx). exact: IH.
    Qed.

    Lemma mem_key_set m x : FS.mem x (key_set m) = mem x m.
    Proof.
      case H: (mem x m).
      - exact: (mem_key_set1 H).
      - apply/negP=> Hmem. move/negP: H. apply. exact: (mem_key_set2 Hmem).
    Qed.

    Lemma submap_key_set m1 m2 :
      submap m1 m2 -> FS.subset (key_set m1) (key_set m2).
    Proof.
      move=> Hsub. apply: FS.subset_1 => x Hin1. apply/Sets.L.memP.
      move/Sets.L.memP: Hin1 => Hmem1. rewrite !mem_key_set in Hmem1 *.
      exact: (submap_mem Hsub Hmem1).
    Qed.

    Lemma mem_key_set_add x v e m :
      FS.mem x (key_set (add v e m)) = (eqb x v)%OT || FS.mem x (key_set m).
    Proof.
      rewrite !mem_key_set. rewrite add_b. rewrite Orders.L.eqb_sym.
      reflexivity.
    Qed.

    Lemma key_set_add v e m :
      FS.Equal (key_set (add v e m)) (FS.add v (key_set m)).
    Proof.
      move=> x; split => Hin.
      - move/Sets.L.memP: Hin=> Hmem. rewrite mem_key_set_add in Hmem.
        apply/Sets.L.memP. rewrite Sets.L.add_b. case/orP: Hmem => Hmem.
        + rewrite Orders.L.eqb_sym Hmem orTb. reflexivity.
        + by rewrite Hmem orbT.
      - move/Sets.L.memP: Hin=> Hmem. apply/Sets.L.memP.
        rewrite mem_key_set_add. rewrite Sets.L.add_b in Hmem.
        case/orP: Hmem => Hmem.
        + rewrite Orders.L.eqb_sym Hmem orTb. reflexivity.
        + by rewrite Hmem orbT.
    Qed.

    Lemma mem_key_set_find v m :
      FS.mem v (key_set m) ->
      exists e, find v m = Some e.
    Proof. rewrite mem_key_set => Hmem. exact: (mem_find_some Hmem). Qed.

    Lemma not_mem_key_set_find v m :
      ~~ FS.mem v (key_set m) ->
      find v m = None.
    Proof. rewrite mem_key_set => Hmem. exact: (not_mem_find_none Hmem). Qed.

    Lemma memPks (k : key) (m : t elt) : reflect (mem k m) (FS.mem k (key_set m)).
    Proof.
      case Hks: (FS.mem k (key_set m)).
      - apply: ReflectT. exact: mem_key_set2.
      - apply: ReflectF. move=> Hkm. apply/negPf: Hks. exact: mem_key_set1.
    Qed.

  End KeySet.


  Section Map2Map.

    Context {key1 : orderedType}.
    Context {key2 : orderedType}.
    Context {t1 : fmapType key1}.
    Context {t2 : fmapType key2}.

    Variable elt1 elt2 : Type.
    Variable fk : key1 -> option key2.
    Variable fk_eq_none :
      forall k1 k2 : key1,
        oeq k1 k2 -> fk k1 = None -> fk k2 = None.
    Variable fk_eq_some :
      forall (k1 k2 : key1) (fk1 : key2),
        oeq k1 k2 -> fk k1 = Some fk1 ->
        exists fk2, fk k2 = Some fk2 /\ oeq fk1 fk2.
    Variable fk_neq_some :
      forall (k1 k2 : key1) (fk1 fk2 : key2),
        ~ oeq k1 k2 -> fk k1 = Some fk1 -> fk k2 = Some fk2 -> ~ oeq fk1 fk2.

    Variable fv : key1 -> elt1 -> elt2.
    Variable fv_eq_key :
      forall (k1 k2 : key1) (v : elt1),
        oeq k1 k2 -> fv k1 v = fv k2 v.

    Definition f (k1 : key1) (v1 : elt1) (m2 : t2 elt2) : t2 elt2 :=
      match fk k1 with
      | None => m2
      | Some k2 => add k2 (fv k1 v1) m2
      end.
    Definition map2map (m1 : t1 elt1) : t2 elt2 :=
      fold f m1 (empty elt2).

    Lemma f_eq_kv k1 k2 v1 v2 m :
      oeq k1 k2 -> v1 = v2 -> Equal (f k1 v1 m) (f k2 v2 m).
    Proof.
      move=> Heqk12 Heqv12 k. rewrite /f. dcase (fk k1). case.
      - move=> fk1 Hfk1. move: (fk_eq_some Heqk12 Hfk1). move=> [fk2 [Hfk2 Heqfk12]].
        rewrite Hfk2. rewrite Heqfk12 Heqv12. rewrite (fv_eq_key _ Heqk12). reflexivity.
      - move=> Hfk1. rewrite (fk_eq_none Heqk12 Hfk1). reflexivity.
    Qed.

    Lemma f_eq_kvm k1 k2 v1 v2 (m1 m2 : t2 elt2) :
      oeq k1 k2 -> v1 = v2 -> Equal m1 m2 -> Equal (f k1 v1 m1) (f k2 v2 m2).
    Proof.
      move=> Heqk12 Heqv12 Heqm12 k. rewrite /f. dcase (fk k1). case.
      - move=> fk1 Hfk1. move: (fk_eq_some Heqk12 Hfk1). move=> [fk2 [Hfk2 Heqfk12]].
        rewrite Hfk2. rewrite Heqfk12 Heqv12 Heqm12. rewrite (fv_eq_key _ Heqk12).
        reflexivity.
      - move=> Hfk1. rewrite (fk_eq_none Heqk12 Hfk1) Heqm12. reflexivity.
    Qed.

    Lemma f_eq_proper :
      Proper (oeq ==> Logic.eq ==> (@Equal key2 t2 elt2) ==> (@Equal key2 t2 elt2)) f.
    Proof.
      move=> k1 k2 Heqk. move=> v1 v2 Heqv. move=> m1 m2 Heqm.
      exact: (f_eq_kvm Heqk Heqv Heqm).
    Qed.

    Lemma f_eq_transpose_negkey :
      transpose_neqkey (@Equal key2 t2 elt2) f.
    Proof.
      move=> k1 k2 e1 e2 m Hneqk12 k. rewrite /f. dcase (fk k1); case.
      - move=> fk1 Hfk1. dcase (fk k2); case.
        + move=> fk2 Hfk2. move: (fk_neq_some Hneqk12 Hfk1 Hfk2) => Hneqfk12.
          case: (Orders.F.eq_dec fk2 k); case: (Orders.F.eq_dec fk1 k).
          * move=> Heqk1 Heqk2. apply: False_ind; apply: Hneqfk12.
            rewrite Heqk1 Heqk2. exact: O.eq_refl.
          * move=> Hneqk1 Heqk2. rewrite (F.add_neq_o _ _ Hneqk1).
            rewrite 2!(F.add_eq_o _ _ Heqk2). reflexivity.
          * move=> Heqk1 Hneqk2. rewrite (F.add_neq_o _ _ Hneqk2).
            rewrite 2!(F.add_eq_o _ _ Heqk1). reflexivity.
          * move=> Hneqk1 Hneqk2. rewrite (F.add_neq_o _ _ Hneqk1).
            rewrite 2!(F.add_neq_o _ _ Hneqk2) (F.add_neq_o _ _ Hneqk1).
            reflexivity.
        + move=> Hfk2. reflexivity.
      - move=> Hfk1. reflexivity.
    Qed.

    Lemma map2map_empty :
      Equal (map2map (empty elt1)) (empty elt2).
    Proof.
      rewrite /map2map. apply: (P.fold_Empty (F.Equal_ST elt2) f).
      exact: empty_1.
    Qed.

    Lemma map2map_Empty m :
      Empty m -> Empty (map2map m).
    Proof.
      rewrite /map2map => H1. rewrite (P.fold_Empty _ _ _ H1).
      exact: empty_1.
    Qed.

    Lemma map2map_not_in_Add m1 m1' k1 v1 :
      ~ In k1 m1 ->
      P.Add k1 v1 m1 m1' ->
      Equal (map2map m1') (f k1 v1 (map2map m1)).
    Proof.
      move=> Hin Hadd. rewrite /map2map.
      rewrite (P.fold_Add (F.Equal_ST elt2)
                          f_eq_proper f_eq_transpose_negkey
                          _ Hin Hadd). reflexivity.
    Qed.

    Lemma map2map_mem (m1 : t1 elt1) k1 fk1 :
      fk k1 = Some fk1 -> mem k1 m1 = mem fk1 (map2map m1).
    Proof.
      move=> Hfk1. move: m1.
      eapply (@P.map_induction
                key1 t1 elt1
                (fun (m1 : t1 elt1) =>
                   (mem k1 m1 = mem fk1 (map2map m1)))).
      - move=> m1 Hempty1. move: (map2map_Empty Hempty1) => Hempty2.
        rewrite (negPf (Empty_not_mem _ Hempty1)).
        rewrite (negPf (Empty_not_mem fk1 Hempty2)). reflexivity.
      - move=> m m' IH k2 e2 Hin2 Hadd2. rewrite (map2map_not_in_Add Hin2 Hadd2).
        rewrite (Add_mem_add _ Hadd2). case: (Orders.F.eq_dec k1 k2).
        + move=> Heq12. rewrite (F.add_eq_b _ _ (O.eq_sym Heq12)).
          rewrite /f -/f. move: (fk_eq_some Heq12 Hfk1) => [fk2 [Hfk2 Heqfk12]].
          rewrite Hfk2. rewrite (F.add_eq_b _ _ (O.eq_sym Heqfk12)).
          reflexivity.
        + move=> Hneq12. have Hneq21: ~ oeq k2 k1 by
              move=> H; apply: Hneq12; apply: O.eq_sym.
          rewrite (F.add_neq_b _ _ Hneq21). rewrite /f -/f. dcase (fk k2); case.
          * move=> fk2 Hfk2. move: (fk_neq_some Hneq12 Hfk1 Hfk2) => Hneqfk12.
            have Hneqfk21: ~ oeq fk2 fk1 by
                move=> H; apply: Hneqfk12; apply: O.eq_sym.
            rewrite (F.add_neq_b _ _ Hneqfk21) -IH. reflexivity.
          * move=> Hfk2. exact: IH.
    Qed.

    Lemma map2map_not_in (m1 : t1 elt1) k1 fk1 :
      fk k1 = Some fk1 -> ~ In k1 m1 -> ~ In fk1 (map2map m1).
    Proof.
      move=> Hfk1 Hink1. apply/memP. rewrite -(map2map_mem _ Hfk1).
      apply/memP. assumption.
    Qed.

    Lemma map2map_find_none (m1 : t1 elt1) k1 fk1 :
      fk k1 = Some fk1 -> find k1 m1 = None ->
      find fk1 (map2map m1) = None.
    Proof.
      move=> Hfk1 Hfind. apply: not_mem_find_none.
      rewrite -(map2map_mem _ Hfk1). apply/negPf. apply: find_none_not_mem.
      assumption.
    Qed.

    Lemma map2map_find_some (m1 : t1 elt1) k1 fk1 v1 :
      fk k1 = Some fk1 -> find k1 m1 = Some v1 ->
      find fk1 (map2map m1) = Some (fv k1 v1).
    Proof.
      move: m1.
      eapply (@P.map_induction
                key1 t1 elt1
                (fun (m1 : t1 elt1) =>
                   (fk k1 = Some fk1 ->
                    find k1 m1 = Some v1 ->
                    find fk1 (map2map m1) = Some (fv k1 v1)))).
      - move=> m1 Hempty Hfk1 Hfind1. rewrite (Empty_find _ Hempty) in Hfind1.
        discriminate.
      - move=> m1 m1' IH k2 v2 Hin2 Hadd2 Hfk1 Hfind1.
        rewrite (map2map_not_in_Add Hin2 Hadd2). case: (Orders.F.eq_dec k1 k2).
        + move=> Heqk12. move: (fk_eq_some Heqk12 Hfk1) => [fk2 [Hfk2 Heqfk12]].
          rewrite /f Hfk2. rewrite (F.add_eq_o _ _ (O.eq_sym Heqfk12)).
          rewrite (F.find_o _ Heqk12) in Hfind1. rewrite (Hadd2 k2) in Hfind1.
          rewrite (add_eq_o _ _ (O.eq_refl k2))in Hfind1.
          case: Hfind1 => ->. rewrite (fv_eq_key _ Heqk12). reflexivity.
        + move=> Hneqk12. rewrite (Hadd2 k1) in Hfind1.
          have Hneqk21: ~ oeq k2 k1 by
            move=> H; apply: Hneqk12; apply: O.eq_sym.
          rewrite (add_neq_o _ _ Hneqk21) in Hfind1.
          rewrite /f. dcase (fk k2); case.
          * move=> fk2 Hfk2. move: (fk_neq_some Hneqk12 Hfk1 Hfk2) => Hneqfk12.
            have Hneqfk21: ~ oeq fk2 fk1 by
              move=> H; apply: Hneqfk12; apply: O.eq_sym.
            rewrite (add_neq_o _ _ Hneqfk21). apply: (IH Hfk1). exact: Hfind1.
          * move=> Hfk. exact: (IH Hfk1 Hfind1).
    Qed.

  End Map2Map.


  Section AgreeDefn.

    Context {key : orderedType}.
    Context {set : fsetType key}.
    Context {t : fmapType key}.

    Variable elt : Type.
    Variable s : set.

    Definition agree (m1 m2 : t elt) : Prop :=
      forall x, FS.mem x s -> find x m1 = find x m2.

    Lemma agree_refl m : agree m m.
    Proof. move=> x Hmem. reflexivity. Qed.

    Lemma agree_sym m1 m2 : agree m1 m2 -> agree m2 m1.
    Proof. move=> H x Hmem. rewrite (H x Hmem). reflexivity. Qed.

    Lemma agree_trans m1 m2 m3 :
      agree m1 m2 -> agree m2 m3 -> agree m1 m3.
    Proof. move=> H12 H23 x Hmem. rewrite (H12 x Hmem). exact: (H23 x Hmem). Qed.

    Global Instance agree_equivalence : Equivalence agree.
    Proof. split; [ exact: agree_refl | exact: agree_sym | exact: agree_trans ]. Qed.

  End AgreeDefn.

  Add Parametric Relation
      (key : orderedType) (set : fsetType key) (t : fmapType key)
      (elt : Type) (s : set) : (t elt) (@agree key set t elt s)
      reflexivity proved by (@agree_refl _ _ _ elt s)
      symmetry proved by (@agree_sym _ _ _ elt s)
      transitivity proved by (@agree_trans _ _ _ elt s)
        as agree_rel.

  Add Parametric Morphism
      (key : orderedType) (set : fsetType key) (t : fmapType key)
      (elt : Type) (s : set) : (@agree key set t elt)
      with signature FS.Equal ==> (@Equal key t elt) ==> (@Equal key t elt) ==> iff as agree_m.
  Proof.
    move=> s1 s2 Heqs m1 m1' Heqm1 m2 m2' Heqm2. split => Ha x Hmemx.
    - rewrite -Heqm1 -Heqm2. apply: Ha. rewrite Heqs. exact: Hmemx.
    - rewrite Heqm1 Heqm2. apply: Ha. rewrite -Heqs. exact: Hmemx.
  Qed.

  Section AgreeLemmas.

    Context {key : orderedType}.
    Context {s : fsetType key}.
    Context {t : fmapType key}.

    Variable elt : Type.

    Lemma Empty_agree (vs : s) (m1 m2 : t elt) : FS.Empty vs -> agree vs m1 m2.
    Proof. move=> He x /FS.mem_2 Hmemx. move: (He _ Hmemx). done. Qed.

    Lemma agree_empty_set (m1 m2 : t elt) : agree (FS.empty : s) m1 m2.
    Proof. apply: Empty_agree. exact: FS.empty_1. Qed.

    Lemma agree_singleton_set x (m1 m2 : t elt) :
      agree (FS.singleton x : s) m1 m2 <-> find x m1 = find x m2.
    Proof.
      split=> H.
      - apply: H. apply: FS.mem_1. apply: FS.singleton_2. reflexivity.
      - move=> y /FS.mem_2/FS.singleton_1 Hin. rewrite -Hin. assumption.
    Qed.

    Lemma agree_mem v (vs : s) (E1 E2 : t elt) :
      agree vs E1 E2 -> FS.mem v vs -> mem v E1 = mem v E2.
    Proof.
      move=> Hag Hmem. move: (Hag _ Hmem).
      rewrite L.mem_find_b. move=> ->.
      rewrite -L.mem_find_b. reflexivity.
    Qed.

    Lemma agree_mem_singleton v (E1 E2 : t elt) :
      agree (FS.singleton (t:=s) v) E1 E2 -> mem v E1 = FM.mem v E2.
    Proof.
      move=> Hag. apply: (agree_mem Hag).
      apply: Sets.L.eq_mem_singleton. reflexivity.
    Qed.

    Lemma agree_empty_map_l (vs : s) (m : t elt) x :
      agree vs (empty elt) m -> FS.mem x vs -> find x m = None.
    Proof. move=> Ha Hmem. rewrite -(Ha _ Hmem). exact: empty_o. Qed.

    Lemma agree_empty_map_r (vs : s) (m : t elt) x :
      agree vs m (empty elt) -> FS.mem x vs -> find x m = None.
    Proof. move=> Ha Hmem. rewrite (Ha _ Hmem). exact: empty_o. Qed.

    Lemma Subset_set_agree (s1 s2 : s) (m1 m2 : t elt) :
      FS.Subset s1 s2 -> agree s2 m1 m2 -> agree s1 m1 m2.
    Proof.
      move=> Hsub Ha x /FS.mem_2 Hin1. apply: Ha.
      apply/FS.mem_1. exact: (Hsub _ Hin1).
    Qed.

    Lemma subset_set_agree (s1 s2 : s) (m1 m2 : t elt) :
      FS.subset s1 s2 -> agree s2 m1 m2 -> agree s1 m1 m2.
    Proof.
      move=> Hsub Ha. apply: (Subset_set_agree _ Ha).
      apply: FS.subset_2. exact: Hsub.
    Qed.

    Lemma not_mem_add_map_l (vs : s) (m1 m2 : t elt) x v :
      ~~ FS.mem x vs -> agree vs m1 m2 -> agree vs (add x v m1) m2.
    Proof.
      move=> Hmem Ha y Hmemy. rewrite add_neq_o.
      - exact: (Ha _ Hmemy).
      - move=> Heq. move/negP: Hmem; apply.
        rewrite (Sets.F.mem_b _ Heq). exact: Hmemy.
    Qed.

    Lemma not_mem_add_map_r (vs : s) (m1 m2 : t elt) x v :
      ~~ FS.mem x vs -> agree vs m1 m2 -> agree vs m1 (add x v m2).
    Proof.
      move=> Hmem /agree_sym Ha. apply: agree_sym.
      exact: (not_mem_add_map_l _ Hmem Ha).
    Qed.

    Lemma agree_add_map2 (vs : s) (m1 m2 : t elt) x v :
      agree vs m1 m2 -> agree vs (add x v m1) (add x v m2).
    Proof.
      move=> Ha y Hmemy. case: (O.eq_dec x y).
      - move=> Heq. rewrite 2!(add_eq_o _ _ Heq). reflexivity.
      - move=> Hneq. rewrite 2!(add_neq_o _ _ Hneq). exact: (Ha _ Hmemy).
    Qed.

    Lemma agree_add_map_l (vs : s) (m1 m2 : t elt) x v :
      agree vs m1 m2 -> find x m2 = Some v ->
      agree vs (add x v m1) m2.
    Proof.
      move=> Ha Hfind y Hmemy. case: (O.eq_dec x y).
      - move=> Heq. rewrite (add_eq_o _ _ Heq). rewrite -(find_o _ Heq).
        rewrite -Hfind. reflexivity.
      - move=> Hneq. rewrite (add_neq_o _ _ Hneq). exact: (Ha _ Hmemy).
    Qed.

    Lemma agree_add_map_r (vs : s) (m1 m2 : t elt) x v :
      agree vs m1 m2 -> find x m1 = Some v ->
      agree vs m1 (add x v m2).
    Proof.
      move=> /agree_sym Ha Hf. apply: agree_sym.
      exact: (agree_add_map_l Ha Hf).
    Qed.

    Lemma agree_add_set_l x (vs : s) (m1 m2 : t elt) :
      agree (FS.add x vs) m1 m2 -> agree (FS.singleton x : s) m1 m2.
    Proof.
      move=> Ha y Hmemy. apply: (Ha y). rewrite Sets.F.singleton_b in Hmemy.
      rewrite Sets.F.add_b Hmemy /=. reflexivity.
    Qed.

    Lemma agree_add_set_r x (vs : s) (m1 m2 : t elt) :
      agree (FS.add x vs) m1 m2 -> agree vs m1 m2.
    Proof.
      move=> Ha y Hmemy. apply: (Ha y).
      rewrite Sets.F.add_b Hmemy orbT. reflexivity.
    Qed.

    Lemma agree_union_set_l (vs1 vs2 : s) (m1 m2 : t elt) :
      agree (FS.union vs1 vs2) m1 m2 -> agree vs1 m1 m2.
    Proof.
      move=> Ha x Hmemx. apply: (Ha x).
      rewrite Sets.F.union_b Hmemx /=. reflexivity.
    Qed.

    Lemma agree_union_set_r (vs1 vs2 : s) (m1 m2 : t elt) :
      agree (FS.union vs1 vs2) m1 m2 -> agree vs2 m1 m2.
    Proof.
      move=> Ha x Hmemx. apply: (Ha x).
      rewrite Sets.F.union_b Hmemx /= orbT. reflexivity.
    Qed.

    Lemma agree_add_to_set x (vs : s) (m1 m2 : t elt) :
      agree vs m1 m2 -> find x m1 = find x m2 -> agree (FS.add x vs) m1 m2.
    Proof.
      move=> Ha Hf y /FS.mem_2 Hmem.
      case/Sets.F.add_iff: Hmem => H.
      - rewrite -2!(find_o _ H). exact: Hf.
      - move/FS.mem_1: H => Hmem. exact: (Ha _ Hmem).
    Qed.

    Lemma agree_union_sets (vs1 vs2 : s) (m1 m2 : t elt) :
      agree vs1 m1 m2 -> agree vs2 m1 m2 -> agree (FS.union vs1 vs2) m1 m2.
    Proof.
      move=> Ha1 Ha2 x Hmem. rewrite Sets.F.union_b in Hmem. case/orP: Hmem=> Hmem.
      - exact: (Ha1 _ Hmem).
      - exact: (Ha2 _ Hmem).
    Qed.

    Lemma agree_add_set x (vs : s) (m1 m2 : t elt) :
      agree (FS.add x vs) m1 m2 <-> agree (FS.singleton x : s) m1 m2 /\ agree vs m1 m2.
    Proof.
      split.
      - move=> H. exact: (conj (agree_add_set_l H) (agree_add_set_r H)).
      - move=> [H1 H2]. apply: (agree_add_to_set H2). apply/agree_singleton_set.
        assumption.
    Qed.

    Lemma agree_union_set (vs1 vs2 : s) (m1 m2 : t elt) :
      agree (FS.union vs1 vs2) m1 m2 <-> agree vs1 m1 m2 /\ agree vs2 m1 m2.
    Proof.
      split.
      - move=> H. exact: (conj (agree_union_set_l H) (agree_union_set_r H)).
      - move=> [H1 H2]. exact: agree_union_sets.
    Qed.

  End AgreeLemmas.

  Ltac simpl_agree :=
    repeat
      match goal with
      | H : agree (FS.add _ _) _ _ |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          (* `move: (agree_add_set_l H)` succeeds inside this module
             but fails outside this module *)
          generalize (agree_add_set_r H);
          generalize (agree_add_set_l H);
          move=> {H} H1 H2
      | H : agree (FS.union _ _) _ _ |- _ =>
          let H1 := fresh in
          let H2 := fresh in
          generalize (agree_union_set_r H);
          generalize (agree_union_set_l H);
          move=> {H} H1 H2
      end.

  Ltac dp_agree :=
    repeat
      match goal with
      | |- agree FS.empty _ _ => exact: agree_empty_set
      | H : FS.is_empty ?vs |- agree ?vs _ _ =>
          (apply: Empty_agree); (apply: FS.is_empty_2); assumption
      | H : FS.Empty ?vs |- agree ?vs _ _ => exact: Empty_agree H
      | |- agree _ ?E ?E => exact: agree_refl
      | H : agree ?vs ?E1 ?E2 |- agree ?vs ?E2 ?E1 => exact: (agree_sym H)
      | H1 : agree ?vs ?E1 ?E2, H2 : agree ?vs ?E2 ?E3
        |- agree ?vs ?E1 ?E3 => exact: (agree_trans H1 H2)
      | H : agree (FS.singleton _) _ _ |- _ => move/agree_singleton_set: H => H
      | |- agree (FS.singleton _) _ _ => apply/agree_singleton_set
      | |- agree (FS.add _ _) _ _ => apply: agree_add_to_set
      | |- agree (FS.union _ _) _ _ => apply: agree_union_sets
      | |- agree _ (add ?x ?v _) (add ?x ?v _) => apply: agree_add_map2
      | |- agree _ (add _ _ _) _ => apply: agree_add_map_l
      | |- agree _ _ (add _ _ _) => apply: agree_add_map_r
      | H1 : is_true (FS.subset ?s1 ?s2),
          H2 : agree ?s2 ?m1 ?m2 |- agree ?s1 ?m1 ?m2 =>
          exact: (subset_set_agree H1 H2)
      | H1 : is_true (~~ FS.mem ?x ?vs),
          H2 : agree ?vs ?m1 ?m2 |- agree ?vs (add ?x ?v ?m1) ?m2 =>
          exact: (not_mem_add_map_l H1 H2)
      | H1 : is_true (~~ FS.mem ?x ?vs),
          H2 : agree ?vs ?m1 ?m2 |- agree ?vs ?m1 (add ?x ?v ?m2) =>
          exact: (not_mem_add_map_r H1 H2)
      | H : ?e |- ?e => assumption
      end.

End L.


(** ** FMapInterface.S as fmapType *)

Module Type FMap.
  Parameter key : orderedType.
  Parameter t : fmapType key.
End FMap.

Module FMapInterface_as_FM
       (E : Ordered)
       (M : FMapInterface.S
        with Definition E.t := E.t
        with Definition E.eq := E.eq
        with Definition E.lt := E.lt) <: FMap.

  Definition fmap_mixin :=
    @FMapMixin E.T M.t
               M.empty M.is_empty M.add M.find M.remove M.mem
               M.map M.mapi M.map2 M.elements M.cardinal M.fold M.equal
               M.MapsTo M.MapsTo_1 M.mem_1 M.mem_2
               M.empty_1 M.is_empty_1 M.is_empty_2 M.add_1 M.add_2 M.add_3
               M.remove_1 M.remove_2 M.remove_3 M.find_1 M.find_2
               M.elements_1 M.elements_2 M.elements_3w M.cardinal_1
               M.fold_1 M.equal_1 M.equal_2
               M.map_1 M.map_2 M.mapi_1 M.mapi_2 M.map2_1 M.map2_2
               M.elements_3.

  #[global]
   Canonical t :=
    Eval hnf in FMapType E.T M.t fmap_mixin.

  Definition key := E.T.

End FMapInterface_as_FM.


Module Type FMapWithNewKey <: FMap.
  Include FMap.
  Parameter new_key : forall (elt : Type), t elt -> key.
  Axiom new_key_is_new : forall (elt : Type) (m : t elt), ~~ FM.mem (new_key m) m.
End FMapWithNewKey.

Module FMapInterface_as_FM_WDS
       (E : OrderedWithDefaultSucc)
       (M : FMapInterface.S
        with Definition E.t := E.t
        with Definition E.eq := E.eq
        with Definition E.lt := E.lt) <: FMapWithNewKey.

  Module MM := FMapInterface_as_FM E M.
  Include MM.

  Section Gen.

    Local Notation key := E.t.
    Variable elt : Type.

    (* Generate a new key *)
    Definition new_key (m : t elt) : key :=
      match L.max_key m with
      | Some k => E.succ k
      | None => E.default
      end.

    Lemma new_key_is_new :
      forall (m : t elt), ~~ FM.mem (new_key m) m.
    Proof.
      move=> m. rewrite /new_key. case H: (L.max_key m).
      - apply/negP=> Hmem. apply: (L.max_key_not_lt H Hmem). exact: E.lt_succ.
      - move: (L.max_key_none H) => Hempty.
        exact: (L.Empty_not_mem E.default Hempty).
    Qed.

  End Gen.

End FMapInterface_as_FM_WDS.
