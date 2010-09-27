Require Import Arith.

Fixpoint fib1 n:nat :=
 match n with
  | 0 => 0
  | 1 => 1
  | S (S m as p) => fib1 p + fib1 m
 end.

Fixpoint fib2 n a b:nat :=
 match n with
  | 0 => a
  | S n => fib2 n b (a + b)
 end.

Lemma plus_1_Sn :
 forall n:nat, n + 1 = S n.
Proof.
 intro n.
 rewrite plus_n_O.
 rewrite plus_Snm_nSm.
 reflexivity.
Qed.

Lemma plus_2_SSn :
 forall n:nat, n + 2 = S (S n).
Proof.
 intro n.
 rewrite plus_n_O.
 rewrite plus_Snm_nSm.
 rewrite plus_Snm_nSm.
 reflexivity.
Qed.

Theorem fib1_fib :
 forall n:nat,
 fib1 n + fib1 (n + 1) = fib1 (n + 2).
Proof.
 intro n.
 rewrite plus_1_Sn.
 rewrite plus_2_SSn.
 simpl fib1.
 destruct n.
  reflexivity.
  
  ring.
Qed.

Theorem fib2_fib :
 forall n a b:nat,
 fib2 n a b + fib2 (n + 1) a b = fib2 (n + 2) a b.
Proof.
 induction n.
  intros a b.
  reflexivity.
  
  intros a b.
  rewrite plus_Sn_m.
  rewrite plus_Sn_m.
  simpl.
  rewrite (IHn b (a + b)).
  reflexivity.
Qed.

(* 未使用 *)
Lemma fib2_eq_aux :
 forall n a b c d:nat,
 fib2 n (a + b) (c + d) = fib2 n a c + fib2 n b d.
Proof.
 induction n.
  intros a b c d.
  reflexivity.
  
  intros a b c d.
  simpl.
  rewrite <- IHn.
  replace (a + c + (b + d)) with (a + b + (c + d)) by ring.
  reflexivity.
Qed.

(* 未使用 *)
Lemma fib2_0_1_eq :
 forall n:nat, fib2 n 0 1 = fib2 (S n) 1 0.
Proof.
 intro n.
 simpl.
 reflexivity.
Qed.

Lemma fib1_eq_fib2_aux :
 forall n:nat,
 fib1 n = fib2 n 0 1 /\ fib1 (S n) = fib2 (S n) 0 1.
Proof.
 induction n.
  split.
   reflexivity.
   
   reflexivity.
  destruct IHn.
  split.
   exact H0.
   
   rewrite <- plus_2_SSn.
   rewrite <- fib1_fib.
   rewrite <- fib2_fib.
   rewrite plus_1_Sn.
   rewrite <- H.
   rewrite <- H0.
   reflexivity.
Qed.

Theorem fib1_eq_fib2 :
 forall n:nat, fib1 n = fib2 n 0 1.
Proof.
 intro n.
 destruct (fib1_eq_fib2_aux n).
 exact H.
Qed.

