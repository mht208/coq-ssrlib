
(** Lemmas for compatibility. *)

From mathcomp Require Import ssreflect eqtype ssrbool seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section FoldRightComp.

  Variables (T1 T2 : Type) (h : T1 -> T2).
  Variables (R : Type) (f : T2 -> R -> R) (z0 : R).

  (* Available since coq-mathcomp-ssreflect 1.11.0 *)
  Lemma foldr_rcons s x : foldr f z0 (rcons s x) = foldr f (f x z0) s.
  Proof. by rewrite -cats1 foldr_cat. Qed.

End FoldRightComp.

Section FoldLeft.

  Variables (T R : Type) (f : R -> T -> R).

  (* Available since coq-mathcomp-ssreflect 1.11.0 *)
  Lemma foldl_rcons z s x : foldl f z (rcons s x) = f (foldl f z s) x.
  Proof. by rewrite -cats1 foldl_cat. Qed.

End FoldLeft.

Section Zip.

  Variables (S T : Type).

  (* Available since coq-mathcomp-ssreflect 1.13.0 *)
  Lemma zip_map {I : Type} (f : I -> S) (g : I -> T) (s : seq I) :
    zip (map f s) (map g s) = [seq (f i, g i) | i <- s].
  Proof. by elim: s => //= i s ->. Qed.

End Zip.
