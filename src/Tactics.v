
From mathcomp Require Import ssreflect ssrbool.

(** General tactics *)

(* Split goal of the form (_ && _). *)
Ltac splitb := apply/andP; split.

(* Split all hypotheses of the form (_ && _). *)
Ltac hyps_splitb :=
  repeat (match goal with
          | H: is_true (_ && _) |- _ =>
            let H1 := fresh in
            let H2 := fresh in
            move/andP: H => [H1 H2]
          end).

Ltac leftb := apply/orP; left.

Ltac rightb := apply/orP; right.

Ltac caseb H :=
  match type of H with
  | is_true ([&& _, _ & _ ]) =>
    let H0 := fresh in
    let H1 := fresh in
    move/andP: H => [H0 H1]; caseb H1; first [caseb H0 | move: H0]
  | is_true ([&& _ & _ ]) =>
    let H0 := fresh in
    let H1 := fresh in
    move/andP: H => [H0 H1]; first [caseb H1 | move: H1]; first [caseb H0 | move: H0]
  | is_true (_ && _) =>
    let H0 := fresh in
    let H1 := fresh in
    move/andP: H => [H0 H1]; first [caseb H1 | move: H1]; first [caseb H0 | move: H0]
  | [/\ _, _, _, _ & _ ] =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseb H1 | move: H1]; first [caseb H0 | move: H0]
  | [/\ _, _, _ & _ ] =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseb H1 | move: H1]; first [caseb H0 | move: H0]
  | [/\ _, _ & _ ] =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseb H1 | move: H1]; first [caseb H0 | move: H0]
  | [/\ _ & _ ] =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseb H1 | move: H1]; first [caseb H0 | move: H0]
  | _ /\ _ =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseb H1 | move: H1]; first [caseb H0 | move: H0]
  | is_true ([|| _, _ | _ ]) =>
    let H0 := fresh in
    move/orP: H; case; [idtac | move=> H0; caseb H0]
  | is_true ([|| _ | _ ]) => move/orP: H; case
  | is_true (_ || _) => move/orP: H; case
  | [\/ _, _, _ | _ ] => elim: H
  | [\/ _, _ | _ ] => elim: H
  | [\/ _ | _ ] => elim: H
  | _ \/ _ => elim: H
  end.

Ltac applyb H :=
  match goal with
  | H: is_true (negb _) |- False => apply: (negP H) => H
  | H: is_true (negb _) |- is_true (negb _) =>
    let H0 := fresh in
    apply/negP => H0; apply: (negP H); move: H0
  end.

Ltac sethave e1 e2 := set e1 := e2; have: e1 = e2 by reflexivity.

Ltac caseb_hyps :=
  repeat (match goal with
          | H : is_true [&& _ & _] |- _ => case/andP: H; intros
          | H : is_true [|| _ | _] |- _ => case/orP: H; intros
          end).

Ltac dcase t := move: (refl_equal t); generalize t at -1.
