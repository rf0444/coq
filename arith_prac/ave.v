Require Import QArith.
Require Import List.
Open Scope Q_scope.

Fixpoint sum (xs : list Q) : Q :=
  match xs with
    | nil => 0
    | x :: xs => x + sum xs
  end.

Theorem sum_1_2__10_returns_55 :
  sum (1#1::2#1::3#1::4#1::5#1::6#1::7#1::8#1::9#1::10#1::nil) = 55#1.
Proof.
  compute.
  reflexivity.
Qed.

Theorem sum_head : forall (xs : list Q),
  sum xs = (hd (0#1) xs) + sum (tail xs).
Proof.
  intros.
  induction xs.
    simpl.
    unfold Qplus.
    simpl.
    reflexivity.
    
    simpl.
    reflexivity.
Qed.
(*
Definition average (xs : list Q) : Q :=
   (sum xs) / (Z_of_nat (length xs) # 1).

Theorem ave_1_2__10_returns_5_5 : 
  average (1#1::2#1::3#1::4#1::5#1::6#1::7#1::8#1::9#1::10#1::nil) = 11#2.
Proof.
  compute.
  (*´・ω・｀*)
Qed.
*)
(*
Theorem ave_sum : forall (xs : list Q),
  ~ (Z_of_nat (length xs) # 1 == 0) -> average xs * (Z_of_nat (length xs) # 1) = sum xs.
Proof.
  intros.
  unfold average.
  (*´・ω・｀*)
Qed.
*)
