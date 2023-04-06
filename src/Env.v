
(** * Typing Environments *)

From Coq Require Import ZArith FSets FMapAVL.
From mathcomp Require Import ssreflect ssrbool eqtype seq.
From ssrlib Require Import Types Orders Sets Maps HList ZAriths.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(** ** Environments for variables with the same type *)

Module Type SEnv.

  Declare Module V : Ordered.

  (* The type of environments *)
  Parameter t : Type.

  (* An empty environment *)
  Parameter empty : t.

  (* Check if a variable is defined in an environment *)
  Parameter mem : V.t -> t -> bool.
  Axiom mem_empty : forall (x : V.t), mem x empty = false.

  (* Add a variable to an environment *)
  Parameter add : V.t -> t -> t.
  Axiom mem_add_eq :
    forall {E : t} {x : V.t}, mem x (add x E).
  Axiom mem_add_neq :
    forall {E : t} {x y : V.t}, (x ~= y)%OT -> mem x (add y E) = mem x E.

  (* Variables in an environment *)
  Parameter pvar : t -> Type.
  Parameter make_pvar : forall (E : t) (x : V.t), mem x E -> pvar E.
  Parameter pvar_var : forall (E : t), pvar E -> V.t.
  Axiom pvar_var_mem :
    forall (E : t) (x : pvar E), mem (pvar_var x) E.

  (* Creating new variables *)
  Parameter new_var : t -> V.t.
  Axiom new_var_is_new : forall (E : t), ~~ mem (new_var E) E.

  (* Equality of environments *)
  Parameter Equal : t -> t -> Prop.
  Axiom Equal_mem : forall (E1 E2 : t) (x : V.t), Equal E1 E2 -> mem x E1 = mem x E2.
  Axiom Equal_add : forall (E1 E2 : t) (x : V.t), Equal E1 E2 -> Equal (add x E1) (add x E2).

  Axiom mem_m : Proper (oeq ==> Equal ==> Logic.eq) mem.
  Axiom add_m : Proper (oeq ==> Equal ==> Equal) add.
End SEnv.


Module MakeSEnv (VV : OrderedWithDefaultSucc) <: SEnv with Module V := VV.

  Import FS.

  Module V := VV.

  Local Notation var := V.t.

  Module VSBase := FSetAVL.Make V.
  Module VS := FSetInterface_as_FS_WDS V VSBase.

  Definition t : Type := VS.t.

  Definition empty : t := empty.

  Definition mem (v : var) (E : t) : bool := mem v E.

  Lemma mem_empty : forall (x : V.t), mem x empty = false.
  Proof. exact: L.mem_empty. Qed.

  Definition add (v : var) (E : t) : t := add v E.

  Lemma mem_add_eq {E : t} {x : V.t} : mem x (add x E).
  Proof. apply: Sets.L.mem_add_eq. reflexivity. Qed.

  Lemma mem_add_neq {E : t} {x y : V.t} : (x ~= y)%OT -> mem x (add y E) = mem x E.
  Proof. move=> Hne. exact: (Sets.L.mem_add_neq Hne). Qed.

  Inductive pvar_t (E : t) : Type :=
  | PVar : forall x : V.t, mem x E -> pvar_t E.

  Definition pvar := pvar_t.

  Definition make_pvar := PVar.

  Definition pvar_var (E : t) (x : pvar E) : var :=
    match x with
    | PVar v _ => v
    end.

  Lemma pvar_var_mem :
    forall (E : t) (x : pvar E), mem (pvar_var x) E.
  Proof. by move=> E []. Qed.

  Definition new_var (E : t) : var := VS.new_elt E.

  Lemma new_var_is_new :
    forall (E : t), ~~ mem (new_var E) E.
  Proof. exact: VS.new_elt_is_new. Qed.

  Definition Equal (E1 E2 : t) : Prop := Equal E1 E2.

  Lemma Equal_mem (E1 E2 : t) (x : V.t) : Equal E1 E2 -> mem x E1 = mem x E2.
  Proof. move=> ->. reflexivity. Qed.

  Lemma Equal_add (E1 E2 : t) (x : V.t) : Equal E1 E2 -> Equal (add x E1) (add x E2).
  Proof. move=> ->. reflexivity. Qed.

  #[global]
   Add Morphism mem with signature oeq ==> Equal ==> Logic.eq as mem_m.
  Proof. move=> x y Hxy t1 t2 ->. rewrite Hxy. reflexivity. Qed.

  #[global]
   Add Morphism add with signature oeq ==> Equal ==> Equal as add_m.
  Proof. move=> x y Hxy t1 t2 ->. rewrite Hxy. reflexivity. Qed.

End MakeSEnv.


(** ** Environments for variables with heterogeneous types *)

Module Type TEnv.

  Declare Module V : Ordered.

  Section Env.

    (* Types *)
    Variable T : Type.

    (* Environments *)
    Parameter t : Type -> Type.

    (* An empty environment *)
    Parameter empty : t T.

    (* Check if a variable is defined in an environment *)
    Parameter mem : V.t -> t T -> bool.
    Axiom mem_empty : forall (x : V.t), mem x empty = false.

    (* Find the type of a variable in an environment *)
    Parameter find : V.t -> t T -> option T.
    Axiom find_some_mem :
      forall (E : t T) (x : V.t) (ty : T),
        find x E = Some ty -> mem x E.
    Axiom find_none_not_mem :
      forall (E : t T) (x : V.t),
        find x E = None -> mem x E = false.
    Axiom mem_find_some :
      forall (E : t T) (x : V.t),
        mem x E -> exists (ty : T), find x E = Some ty.
    Axiom not_mem_find_none :
      forall (E : t T) (x : V.t),
        mem x E = false -> find x E = None.

    (* Add a variable to an environment *)
    Parameter add : V.t -> T -> t T -> t T.
    Axiom mem_add_eq :
      forall {E : t T} {x : V.t} {ty : T}, mem x (add x ty E).
    Axiom mem_add_neq :
      forall {E : t T} {x y : V.t} {ty : T}, (x ~= y)%OT -> mem x (add y ty E) = mem x E.
    Axiom find_add_eq :
      forall {E : t T} {x : V.t} {ty : T},
        find x (add x ty E) = Some ty.
    Axiom find_add_neq :
      forall {E : t T} {x y : V.t} {ty : T},
        (x ~= y)%OT -> find x (add y ty E) = find x E.

    (* Variables in an environment *)
    Parameter pvar : t T -> Type.
    Parameter make_pvar :
      forall (E : t T) (x : V.t) (ty : T),
        find x E = Some ty -> pvar E.
    Parameter pvar_var : forall (E : t T), pvar E -> V.t.
    Parameter pvar_ty : forall (E : t T), pvar E -> T.
    Axiom pvar_var_mem :
      forall (E : t T) (x : pvar E), mem (pvar_var x) E.
    Axiom pvar_ty_find :
      forall (E : t T) (x : pvar E), find (pvar_var x) E = Some (pvar_ty x).

    (* Creating new variables *)
    Parameter new_var : t T -> V.t.
    Axiom new_var_is_new : forall (E : t T), ~~ mem (new_var E) E.

    (* Equality of environments *)
    Parameter Equal : t T -> t T -> Prop.
    Axiom Equal_mem : forall (E1 E2 : t T) (x : V.t), Equal E1 E2 -> mem x E1 = mem x E2.
    Axiom Equal_find : forall (E1 E2 : t T) (x : V.t), Equal E1 E2 -> find x E1 = find x E2.
    Axiom Equal_add :
      forall (E1 E2 : t T) (x : V.t) (v : T),
        Equal E1 E2 -> Equal (add x v E1) (add x v E2).

    Axiom mem_m : Proper (oeq ==> Equal ==> Logic.eq) mem.
    Axiom find_m : Proper (oeq ==> Equal ==> Logic.eq) find.
    Axiom add_m : Proper (oeq ==> Logic.eq ==> Equal ==> Equal) add.
  End Env.

End TEnv.


Module MakeTEnv (Import VV : OrderedWithDefaultSucc) <: TEnv with Module V := VV.

  Import FM Maps.

  Module V := VV.

  Local Notation var := V.t.

  Module VMBase := FMapAVL.Make V.
  Module VM := FMapInterface_as_FM_WDS V VMBase.

  Section Env.

    (* Variable types. *)
    Variable T : Type.

    Definition t : Type := VM.t T.

    Definition empty : t := empty T.

    (* Check if a variable is defined in an environment *)
    Definition mem (v : var) (E : t) : bool := mem v E.

    Lemma mem_empty : forall (x : var), mem x empty = false.
    Proof. exact: L.empty_a. Qed.

    (* Find the type of a variable in an environment *)
    Definition find (v : var) (E : t) : option T := find v E.

    Lemma find_some_mem :
      forall (E : t) (x : var) (ty : T),
        find x E = Some ty -> mem x E.
    Proof. exact: L.find_some_mem. Qed.

    Lemma find_none_not_mem :
      forall (E : t) (x : var),
        find x E = None -> mem x E = false.
    Proof. exact: L.find_none_not_mem. Qed.

    Lemma mem_find_some :
      forall (E : t) (x : var),
        mem x E -> exists (ty : T), find x E = Some ty.
    Proof. exact: L.mem_find_some. Qed.

    Lemma not_mem_find_none :
      forall (E : t) (x : var),
        mem x E = false -> find x E = None.
    Proof.
      move=> E x Hmem. apply: L.not_mem_find_none. apply/negPf. assumption.
    Qed.

    (* Add a variable to an environment *)
    Definition add (v : var) (ty : T) (E : t) : t := add v ty E.

    Lemma mem_add_eq {E : t} {x : var} {ty : T} : mem x (add x ty E).
    Proof. apply: L.add_eq_b. reflexivity. Qed.

    Lemma mem_add_neq {E : t} {x y : var} {ty : T} :
      (x ~= y)%OT -> mem x (add y ty E) = mem x E.
    Proof.
      move=> Hne. apply: L.add_neq_b. move=> H; apply: Hne.
      symmetry. assumption.
    Qed.

    Lemma find_add_eq {E : t} {x : var} {ty : T} : find x (add x ty E) = Some ty.
    Proof. apply: L.add_eq_o. reflexivity. Qed.

    Lemma find_add_neq {E : t} {x y : var} {ty : T} :
      (x ~= y)%OT -> find x (add y ty E) = find x E.
    Proof.
      move=> Hne. apply: L.add_neq_o. move=> H; apply: Hne.
      symmetry. assumption.
    Qed.

    (* Variables in an environment *)
    Inductive pvar_t (E : t) : Type :=
    | PVar : forall (x : var) (ty : T), find x E = Some ty -> pvar_t E.

    Definition pvar := pvar_t.

    Definition make_pvar := PVar.

    Definition pvar_var (E : t) (x : pvar E) : var :=
      match x with
      | PVar v _ _ => v
      end.

    Definition pvar_ty (E : t) (x : pvar E) : T :=
      match x with
      | PVar _ ty _ => ty
      end.

    Lemma pvar_var_mem :
      forall (E : t) (x : pvar E), mem (pvar_var x) E.
    Proof. move=> E [] x t H /=. exact: (find_some_mem H). Qed.

    Lemma pvar_ty_find :
      forall (E : t) (x : pvar E), find (pvar_var x) E = Some (pvar_ty x).
    Proof. by move=> E [] x t H /=. Qed.

    (* Creating new variables *)
    Definition new_var (E : t) : var := VM.new_key E.

    Lemma new_var_is_new :
      forall (E : t), ~~ mem (new_var E) E.
    Proof. exact: VM.new_key_is_new. Qed.

    Definition Equal (t1 t2 : t) : Prop := Equal t1 t2.

    Lemma Equal_mem (E1 E2 : t) (x : V.t) : Equal E1 E2 -> mem x E1 = mem x E2.
    Proof. rewrite /mem. move=> ->. reflexivity. Qed.

    Lemma Equal_find (E1 E2 : t) (x : V.t) : Equal E1 E2 -> find x E1 = find x E2.
    Proof. rewrite /find. move=> ->. reflexivity. Qed.

    Lemma Equal_add (E1 E2 : t) (x : V.t) (v : T) :
      Equal E1 E2 -> Equal (add x v E1) (add x v E2).
    Proof. rewrite /add => ->. reflexivity. Qed.

    #[global]
     Add Morphism mem with signature oeq ==> Equal ==> Logic.eq as mem_m.
    Proof. move=> x y Hxy t1 t2 Ht. rewrite Ht Hxy. reflexivity. Qed.

    #[global]
     Add Morphism find with signature oeq ==> Equal ==> Logic.eq as find_m.
    Proof. move=> x y Hxy t1 t2 Ht. rewrite Ht Hxy. reflexivity. Qed.

    #[global]
     Add Morphism add with signature oeq ==> Logic.eq ==> Equal ==> Equal as add_m.
    Proof. move=> x y Hxy v t1 t2 Ht. rewrite Ht Hxy. reflexivity. Qed.

  End Env.

End MakeTEnv.


(** ** Environments for variables with heterogeneous types. *)

(**
 * Indices for the access of values in a heterogeneous list (HList) are
 * defined in the environments. Need Leibniz equality to rewrite a term
 * `find x (add y ty E)` using `x = y`.
*)

From Coq Require Import Program Program.Tactics.

Module Type HEnv.

  Declare Module V : EqOrdered.

  Section Env.

    Local Open Scope hlist_scope.

    (* Types *)
    Variable T : Type.

    (* Entry *)
    Parameter entry : list T -> Type.
    Parameter vty : forall types : list T, entry types -> T.
    Parameter vidx : forall (types : list T) (e : entry types), lidx (vty e) types.

    (* Environments *)
    Parameter t : Type -> Type.
    Parameter vtypes : t T -> list T.

    (* An empty environment *)
    Parameter empty : t T.
    Axiom vtypes_empty : vtypes empty = [::].

    (* Check if a variable is defined in an environment *)
    Parameter mem : V.t -> t T -> bool.
    Axiom mem_empty : forall x, mem x empty = false.

    (* Find the type of a variable in an environment *)
    Parameter find : V.t -> forall (E : t T), option (entry (vtypes E)).
    Parameter find_ty : V.t -> t T -> option T.
    Parameter find_idx :
      (forall (x y : T), {x = y} + {x <> y}) ->
      forall (v : V.t) (ty : T) (E : t T), option (lidx ty (vtypes E)).

    Axiom find_none_find_ty_none :
      forall (E : t T) (x : V.t), find x E = None -> find_ty x E = None.
    Axiom find_some_find_ty_some :
      forall (E : t T) (x : V.t) e,
        find x E = Some e -> find_ty x E = Some (vty e).

    (* Failed to prove *)
    (*
    Axiom find_some_find_idx_some :
      forall (E : t T) (x : V.t) (ty : T) e,
        find x E = Some e /\ vty e = ty -> find_idx x ty E ~= Some (vty e).
    *)
    Axiom find_none_find_idx_none :
      forall (ty_dec : forall (x y : T), {x = y} + {x <> y}),
      forall (E : t T) (x : V.t) (ty : T), find x E = None -> find_idx ty_dec x ty E = None.

    Axiom find_some_mem :
      forall (E : t T) (x : V.t) e,
        find x E = Some e -> mem x E.
    Axiom find_none_not_mem :
      forall (E : t T) (x : V.t),
        find x E = None -> mem x E = false.

    Axiom mem_find_some :
      forall (E : t T) (x : V.t),
        mem x E -> exists e, find x E = Some e.
    Axiom not_mem_find_none :
      forall (E : t T) (x : V.t),
        mem x E = false -> find x E = None.

    (* Prepend a vtype to an entry *)
    Parameter prepend_vtype :
      forall (ty : T) (types : list T), entry types -> entry (ty::types).
    Axiom prepend_vtype_vty :
      forall (ty : T) (types : list T) (e : entry types),
        vty (prepend_vtype ty e) = vty e.
    Axiom prepend_vtype_vidx :
      forall (ty : T) (types : list T) (e : entry types),
        vidx (prepend_vtype ty e) ~= HIS ty (vidx e).

    (* Add a variable to an environment *)
    Parameter add : V.t -> T -> t T -> t T.
    Axiom mem_add_eq :
      forall {E : t T} {x : V.t} {ty : T}, mem x (add x ty E).
    Axiom mem_add_neq :
      forall {E : t T} {x y : V.t} {ty : T}, (x ~= y)%OT -> mem x (add y ty E) = mem x E.
    Axiom find_add_heq :
      forall (E : t T) (x : V.t) (ty : T),
        (exists e : entry (ty::(vtypes E)),
            find x (add x ty E) ~= Some e /\
            vty e = ty /\
            lidx_eq (vidx e) (HI0 ty (vtypes E))).
    Axiom find_add_eq :
      forall (E : t T) (x : V.t) (ty : T),
        (exists e : entry (vtypes (add x ty E)),
            find x (add x ty E) = Some e /\
            vty e = ty /\
            (vidx e) ~= (HI0 ty (vtypes E))).
    Axiom find_ty_add_eq :
      forall {E : t T} {x : V.t} {ty : T},
        find_ty x (add x ty E) = Some ty.
    Axiom find_ty_add_neq :
      forall {E : t T} {x y : V.t} {ty : T},
        (x ~= y)%OT -> find_ty x (add y ty E) = find_ty x E.
    Axiom find_add_neq :
      forall {E : t T} {x y : V.t} {ty : T},
        (x ~= y)%OT ->
        find x (add y ty E) ~= match find x E with
                              | None => None
                              | Some e => Some (prepend_vtype ty e)
                              end.
    Axiom vtypes_add :
      forall (E : t T) (x : V.t) (ty : T),
        vtypes (add x ty E) = ty::(vtypes E).

    (* Variables in an environment *)
    Parameter pvar : t T -> T -> Type.
    Parameter make_pvar :
      forall (E : t T) (ty : T) (v : V.t) (e : entry (vtypes E)),
        find v E = Some e -> vty e = ty -> pvar E ty.
    Parameter pvar_var : forall (E : t T) (ty : T), pvar E ty -> V.t.
    Parameter pvar_lidx : forall (E : t T) (ty : T), pvar E ty -> lidx ty (vtypes E).
    Axiom pvar_var_mem :
      forall (E : t T) (ty : T) (x : pvar E ty), mem (pvar_var x) E.
    Axiom pvar_vtype_eq :
      forall (E : t T) (ty1 ty2 : T) (x : pvar E ty1) (y : pvar E ty2),
        (pvar_var x == pvar_var y)%OT -> ty1 = ty2.
    Axiom pvar_lidx_heq :
      forall (E : t T) (ty1 ty2 : T) (x : pvar E ty1) (y : pvar E ty2),
        (pvar_var x == pvar_var y)%OT -> (pvar_lidx x =i pvar_lidx y)%hlist.
    Axiom pvar_lidx_eq :
      forall (E : t T) (ty : T) (x y : pvar E ty),
        (pvar_var x == pvar_var y)%OT -> pvar_lidx x = pvar_lidx y.
    Axiom pvar_lidx_hneq :
      forall (E : t T) (ty1 ty2 : T) (x : pvar E ty1) (y : pvar E ty2),
        (pvar_var x ~= pvar_var y)%OT -> pvar_lidx x <>i pvar_lidx y.

    (* Creating new variables *)
    Parameter new_var : t T -> V.t.
    Axiom new_var_is_new : forall (E : t T), ~~ mem (new_var E) E.
  End Env.

End HEnv.


Module MakeHEnv (VV : EqOrderedWithDefaultSucc) <: HEnv with Module V := VV.

  Import FM Maps.

  Module V := VV.

  Module VMBase := FMapAVL.Make V.
  Module VM := Maps.FMapInterface_as_FM_WDS V VMBase.

  Local Notation var := V.t.

  Section Env.

    Local Open Scope hlist_scope.

    (* Types *)
    Variable T : Type.

    Variable ty_dec : forall (x y : T), {x = y} + {x <> y}.

    Record entry_t (types : list T) := mkEntry { vty : T;
                                                 vidx : lidx vty types }.

    Definition entry := entry_t.

    (* Environments *)
    Record t_t := mkEnv { vtypes : list T;
                          vmap : VM.t (entry vtypes);
                          lidx_disjoint :
                            forall (x y : var) (ex ey : entry vtypes),
                              find x vmap = Some ex ->
                              find y vmap = Some ey ->
                              (x ~= y)%OT ->
                              vidx ex <>i vidx ey }.

    Definition t := t_t.
    Definition make_env := mkEnv.

    (* An empty environment *)
    Program Definition empty : t := {| vtypes := nil;
                                       vmap := empty (entry nil) |}.
    Lemma vtypes_empty : vtypes empty = [::].
    Proof. reflexivity. Qed.

    (* Check if a variable is defined in an environment *)
    Definition mem (v : var) (E : t) : bool := mem v (vmap E).

    Lemma mem_empty : forall x, mem x empty = false.
    Proof. exact: L.empty_a. Qed.

    (* Find the entry of a variable in an environment *)
    Definition find (v : var) (E : t) : option (entry (vtypes E)) :=
      find v (vmap E).

    (* Find_idx cannot be defined in the following way. *)
    (*
    Program Definition find_idx (v : var) (E : t) :=
      match find v E with
      | None => None
      | Some e => Some e
      end.
    *)

    Program Definition find_idx (v : var) (ty : T) (E : t) : option (lidx ty (vtypes E)) :=
      match find v E with
      | None => None
      | Some e => match ty_dec ty (vty e) with
                  | left _ => Some (vidx e)
                  | right _ => None
                  end
      end.

    (* Find the type of a variable in an environment. *)
    Definition find_ty (v : var) (E : t) : option T :=
      match find v E with
      | None => None
      | Some e => Some (vty e)
      end.

    Lemma find_none_find_ty_none :
      forall (E : t) (x : var), find x E = None -> find_ty x E = None.
    Proof.
      rewrite /find_ty => E x ->. reflexivity.
    Qed.

    Lemma find_some_find_ty_some :
      forall (E : t) (x : var) e,
        find x E = Some e -> find_ty x E = Some (vty e).
    Proof.
      rewrite /find_ty => E x e ->. reflexivity.
    Qed.

    Lemma find_none_find_idx_none :
      forall (E : t) (x : var) (ty : T), find x E = None -> find_idx x ty E = None.
    Proof.
      move=> E x ty H. rewrite /find_idx. rewrite H. reflexivity.
    Qed.

    Lemma find_some_find_idx_some :
      forall (E : t) (x : var) (ty : T) (e : entry (vtypes E)),
        find x E = Some e /\ vty e = ty -> find_idx x ty E ~= Some (vty e).
    Proof.
      move=> E x ty e [Hfind Hty]. rewrite /find_idx Hfind /=.
      (* Does not know how to proceed *)
    Abort.

    Lemma find_some_mem :
      forall (E : t) (x : var) e,
        find x E = Some e -> mem x E.
    Proof. move=> E x e H. exact: (L.find_some_mem H). Qed.

    Lemma find_none_not_mem :
      forall (E : t) (x : var),
        find x E = None -> mem x E = false.
    Proof. move=> E x H. exact: (L.find_none_not_mem H). Qed.

    Lemma mem_find_some :
      forall (E : t) (x : var),
        mem x E -> exists e, find x E = Some e.
    Proof. move=> E x H. exact: (L.mem_find_some). Qed.

    Lemma not_mem_find_none :
      forall (E : t) (x : var),
        mem x E = false -> find x E = None.
    Proof.
      move=> E x Hmem. apply: L.not_mem_find_none.
      apply/negPf. assumption.
    Qed.

    (* Prepend a vtype to an entry *)
    Definition prepend_vtype (ty : T) {types : list T} (e : entry types) : entry (ty::types) :=
      {| vty := vty e;
         vidx := HIS ty (vidx e) |}.

    Lemma prepend_vtype_vty :
      forall (ty : T) (types : list T) (e : entry types),
        vty (prepend_vtype ty e) = vty e.
    Proof. reflexivity. Qed.

    Lemma prepend_vtype_vidx :
      forall (ty : T) (types : list T) (e : entry types),
        vidx (prepend_vtype ty e) ~= HIS ty (vidx e).
    Proof. reflexivity. Qed.

    (* Prepend a vtype to the list of variable types of an environment. *)
    Definition map_prepend_vtype (ty : T) (types : list T)
               (m : VM.t (entry types)) : VM.t (entry (ty::types)) :=
      map (prepend_vtype ty (types:=types)) m.

    (* Declare a variable in an environment. *)
    Program Definition add (v : var) (ty : T) (E : t) : t :=
      {| vtypes := ty::(vtypes E);
        vmap := add v {| vty := ty; vidx := HI0 ty (vtypes E) |}
                    (map_prepend_vtype ty (vmap E)) |}.
    Next Obligation.
      case: (O.eq_dec x v) => Hxv.
      - (* x == v *)
        case: (O.eq_dec y v) => Hyv.
        + (* y == v *)
          rewrite Hxv Hyv in H1. apply: False_ind. apply: H1. reflexivity.
        + (* y ~= v *)
          rewrite (L.find_add_eq Hxv) in H;
            rewrite (L.find_add_neq Hyv) /prepend_vtype in H0 => {H1 Hxv Hyv}.
          case: H => H; rewrite -H /= => {H}.
          move: (L.find_map_some H0) => {H0} [ey' [He_ey _]].
          rewrite He_ey /prepend_vtype /=.
          move=> Heq; by inversion Heq.
      - (* x ~= v *)
        rewrite (L.find_add_neq Hxv) /prepend_vtype in H => {Hxv}.
        move: (L.find_map_some H) => {H} [ex' [He_ex He_x]].
        rewrite He_ex /prepend_vtype /= => {He_ex}.
        case: (O.eq_dec y v) => Hyv.
        + (* y == v *)
          rewrite (L.find_add_eq Hyv) in H0 => {Hyv}.
          case: H0 => H0; rewrite -H0 /= => {H0}.
          move=> Heq; by inversion Heq.
        + (* y ~= v *)
          rewrite (L.find_add_neq Hyv) /prepend_vtype in H0 => {Hyv}.
          move: (L.find_map_some H0) => {H0} [ey' [He_ey He_y]].
          rewrite He_ey /prepend_vtype /= => {He_ey}.
          move: (lidx_disjoint He_x He_y H1) => Hne Heq; apply: Hne.
          exact: (his_eq_lidx_eq Heq).
    Qed.

    Lemma mem_add_eq {E : t} {x : var} {ty : T} : mem x (add x ty E).
    Proof. apply: L.add_eq_b. reflexivity. Qed.

    Lemma mem_prepend_vtype E x t :
      FM.mem x (map_prepend_vtype t (vmap E)) = FM.mem x (vmap E).
    Proof. rewrite /map_prepend_vtype. exact: L.mem_map. Qed.

    Lemma mem_add_neq {E : t} {x y : var} {ty : T} :
      (x ~= y)%OT -> mem x (add y ty E) = mem x E.
    Proof.
      move=> Hne. rewrite /mem /add /=.
      rewrite (L.mem_add_neq Hne). exact: mem_prepend_vtype.
    Qed.

    Lemma find_add_eq' {E : t} {x : var} {ty : T} :
      find x (add x ty E) = Some {| vty := ty; vidx := HI0 ty (vtypes E) |}.
    Proof.
      rewrite /find /add /=. rewrite (L.find_add_eq (O.eq_refl x)).
      reflexivity.
    Qed.

    Lemma find_add_heq :
      forall (E : t) (x : var) (ty : T),
        (exists e : entry (ty::(vtypes E)),
            find x (add x ty E) ~= Some e /\
            vty e = ty /\
            lidx_eq (vidx e) (HI0 ty (vtypes E))).
    Proof.
      move=> E x ty. exists ({| vty := ty; vidx := HI0 ty (vtypes E) |}) => /=.
      rewrite find_add_eq'. repeat split; reflexivity.
    Qed.

    Lemma find_add_eq :
      forall (E : t) (x : var) (ty : T),
        (exists e : entry (vtypes (add x ty E)),
            find x (add x ty E) = Some e /\
            vty e = ty /\
            (vidx e) ~= (HI0 ty (vtypes E))).
    Proof.
      move=> E x ty. exists ({| vty := ty; vidx := HI0 ty (vtypes E) |}) => /=.
      rewrite find_add_eq'. repeat split; reflexivity.
    Qed.

    Lemma find_add_neq' {E : t} {x y : var} {ty : T} :
      (x ~= y)%OT ->
      find x (add y ty E) = match find x E with
                            | None => None
                            | Some e => Some (prepend_vtype ty e)
                            end.
    Proof.
      move=> Hne. rewrite /find /add /=. rewrite (L.find_add_neq Hne).
      rewrite /map_prepend_vtype. case H: (FM.find x (vmap E)).
      - exact: (L.find_some_map H).
      - exact: (L.find_none_map H).
    Qed.

    Lemma find_add_neq {E : t} {x y : var} {ty : T} :
      (x ~= y)%OT ->
      find x (add y ty E) ~= match find x E with
                             | None => None
                             | Some e => Some (prepend_vtype ty e)
                             end.
    Proof. move=> Hne. rewrite -(find_add_neq' Hne). reflexivity. Qed.

    Lemma find_ty_add_eq {E : t} {x : var} {ty : T} :
      find_ty x (add x ty E) = Some ty.
    Proof.
      rewrite /find_ty /find /add /=. rewrite (L.find_add_eq (O.eq_refl x)) /=.
      reflexivity.
    Qed.

    Lemma find_ty_add_neq {E : t} {x y : var} {ty : T} :
      (x ~= y)%OT -> find_ty x (add y ty E) = find_ty x E.
    Proof.
      rewrite /find_ty /find /add /= => Hne. rewrite (L.find_add_neq Hne) /=.
      rewrite /map_prepend_vtype. case H: (FM.find x (FM.map (prepend_vtype ty) (vmap E))).
      - move: (L.find_map_some H) => [e [He Hfind]].
        rewrite Hfind. rewrite He prepend_vtype_vty. reflexivity.
      - rewrite (L.find_map_none H). reflexivity.
    Qed.

    Lemma vtypes_add :
      forall (E : t) (x : V.t) (ty : T),
        vtypes (add x ty E) = ty::(vtypes E).
    Proof. reflexivity. Qed.

    (* A pvar is a variable of a specified type defined in an environment. *)
    (* Note: The equality of vtypes used here is =, not ==. If == is used, then
     * we will fail to do dependent destruction.
     *)
    Inductive pvar_t (E : t) (ty : T) : Type :=
    | PVar : forall v e, find v E = Some e -> vty e = ty -> pvar_t E ty.

    Definition pvar := pvar_t.
    Definition make_pvar := PVar.

    (* Return the variable ID of a pvar. *)
    Definition pvar_var (E : t) (ty : T) (x : pvar E ty) : var :=
      match x with
      | PVar v _ _ _ => v
      end.

    (* Return the lidx of a pvar in an environment. *)
    Program Definition pvar_lidx (E : t) (ty : T) (x : pvar E ty) : lidx ty (vtypes E) :=
      match x with
      | PVar _ e _ _ => vidx e
      end.

    (* Lemmas about pvar. *)

    Lemma pvar_vtype_eq (E : t) (ty1 ty2 : T) (x : pvar E ty1) (y : pvar E ty2) :
      (pvar_var x == pvar_var y)%OT -> ty1 = ty2.
    Proof.
      elim: x => x ex Hex Htx /=. elim: y => y ey Hey Hty /=.
      move=> Hxy. rewrite /find in Hex Hey. rewrite -Hxy Hex in Hey.
      case: Hey => Hexey; rewrite -Hexey Htx in Hty. exact: Hty.
    Qed.

    Lemma pvar_lidx_heq (E : t) (tyx tyy : T) (x : pvar E tyx) (y : pvar E tyy) :
      (pvar_var x == pvar_var y)%OT -> (pvar_lidx x =i pvar_lidx y)%hlist.
    Proof.
      elim: x => x ex Hex Htx /=. elim: y => y ey Hey Hty /=.
      dependent destruction Htx. dependent destruction Hty. rewrite /=.
      move=> Hxy. rewrite /find in Hex Hey. rewrite -Hxy Hex in Hey.
      case: Hey => Hey; rewrite Hey. reflexivity.
    Qed.

    Lemma pvar_lidx_eq (E : t) ty (x y : pvar E ty) :
      (pvar_var x == pvar_var y)%OT -> pvar_lidx x = pvar_lidx y.
    Proof.
      move=> Hxy. apply: lidx_eq_eq. apply: pvar_lidx_heq. assumption.
    Qed.

    Lemma pvar_lidx_hneq (E : t) (tyx tyy : T) (x : pvar E tyx) (y : pvar E tyy) :
      (pvar_var x ~= pvar_var y)%OT -> pvar_lidx x <>i pvar_lidx y.
    Proof.
      elim: x => x ex Hex Htx. elim: y => y ey Hey Hty. move=> /= Hne.
      dependent destruction Htx. dependent destruction Hty. rewrite /=.
      exact: (lidx_disjoint Hex Hey Hne).
    Qed.

    Lemma pvar_var_mem :
      forall (E : t) (ty : T) (x : pvar E ty), mem (pvar_var x) E.
    Proof.
      move=> E ty [] v e Hfind Hvty /=. exact: (find_some_mem Hfind).
    Qed.

    (* Create a new variable. *)

    Definition new_var (E : t) : var := VM.new_key (vmap E).

    Lemma new_var_is_new :
      forall (E : t), ~~ mem (new_var E) E.
    Proof. move=> E. exact: (VM.new_key_is_new (vmap E)). Qed.

  End Env.

End MakeHEnv.
