
(** * Extra functions from decimal numbers to strings *)

From Coq Require Import ZArith Decimal String DecimalString.

Section DecimalStringConversions.

  (*
    Decimal.int is renamed to Decimal.signed_int to avoid name clashes since 8.16.0.
    Do not use Decimal.int or any function involving Decimal.int to avoid name clashes.
    See https://github.com/coq/coq/issues/7017.
   *)

  Local Open Scope string_scope.

  Definition newline := String (Ascii.ascii_of_N 10) EmptyString.

  Variant signed_int := Pos (d : uint) | Neg (d : uint).

  Definition nat_to_signed_int (n : nat) : signed_int := Pos (Nat.to_uint n).

  Definition positive_to_signed_int (n : positive) : signed_int := Pos (Pos.to_uint n).

  Definition N_to_signed_int (n : N) : signed_int := Pos (N.to_uint n).

  Definition Z_to_signed_int (n : Z) : signed_int :=
    match n with
    | Z0 => Pos (Nat.to_uint O)
    | Zpos m => Pos (Pos.to_uint m)
    | Zneg m => Neg (Pos.to_uint m)
    end.

  Definition string_of_signed_int (d : signed_int) :=
    match d with
    | Pos d => NilEmpty.string_of_uint d
    | Neg d => "-" ++ (NilEmpty.string_of_uint d)
    end.

  Definition string_of_nat (n : nat) : string :=
    string_of_signed_int (nat_to_signed_int n).

  Definition string_of_positive (n : positive) : string :=
    string_of_signed_int (positive_to_signed_int n).

  Definition string_of_N (n : N) : string :=
    string_of_signed_int (N_to_signed_int n).

  Definition string_of_Z (n : Z) : string :=
    string_of_signed_int (Z_to_signed_int n).

End DecimalStringConversions.

Module Type Printer.
  Parameter t : Type.
  Parameter to_string : t -> string.
End Printer.
