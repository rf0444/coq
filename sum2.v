Require Import Arith.

Fixpoint sum (n:nat) : nat :=
 match n with
  | 0 => 0
  | S n => S n + sum n
 end.

Theorem sum_of_nat : forall n:nat, 2 * sum n = n * (n + 1).
Proof.
  intro n.
  induction n.
    simpl.
    reflexivity.
    
    unfold sum; fold sum.
    rewrite mult_plus_distr_l.
    rewrite IHn.
    ring.
Qed.

