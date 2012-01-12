Require Import Arith.

Fixpoint fact n:nat :=
 match n with
  | O => 0
  | S m => n * fact m
 end.

Theorem fact_n_plus_1:
 forall n : nat, fact (n + 1) = (n + 1) * fact n.
Proof.
intro n.
induction n.
 reflexivity.
 
 replace (S n + 1) with (S (n + 1)).
  unfold fact; fold fact.
  rewrite IHn.
  ring.
  
  rewrite <- plus_Sn_m.
  reflexivity.
Qed.

(* 使わなかったけど *)
Lemma plus_1_Sn:
 forall n:nat, n + 1 = S n.
Proof.
intro n.
rewrite plus_n_O.
rewrite plus_Snm_nSm.
reflexivity.
Qed.

