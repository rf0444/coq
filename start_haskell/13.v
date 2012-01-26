
Inductive Nat :=
 | Zero: Nat
 | Succ: Nat-> Nat.

Fixpoint add (n m: Nat) :=
  match n with
  | Zero => m
  | Succ n => Succ (add n m)
  end.


Theorem Ex_13_2 : forall (n m: Nat), add n (Succ m) = Succ (add n m).
Proof.
  intros n m.
  induction n.
    simpl.
    reflexivity.
    
    simpl.
    rewrite IHn.
    reflexivity.
Qed.


Lemma add_n_z_eq_n : forall n: Nat, add n Zero = n.
Proof.
  induction n.
    simpl.
    reflexivity.
    
    simpl.
    rewrite IHn.
    reflexivity.
Qed.
Theorem Ex_13_3 : forall (n m: Nat), add n m = add m n.
Proof.
  intros n m.
  induction n.
    simpl.
    rewrite add_n_z_eq_n.
    reflexivity.
    
    simpl.
    rewrite Ex_13_2.
    rewrite IHn.
    reflexivity.
Qed.


Inductive List (A: Type) :=
 | Nil: List A
 | Cons: A -> List A -> List A.
Implicit Arguments Nil [A].
Implicit Arguments Cons [A].

Fixpoint all {A} (p: A -> Prop) (list: List A): Prop :=
  match list with
  | Nil => True
  | Cons x xs => (p x) /\ (all p xs)
  end.

Fixpoint replicate {A} (n: nat) (x: A): List A :=
  match n with
  | O => Nil
  | S n => Cons x (replicate n x)
  end.

Theorem Ex_13_4 : forall (A: Type) (n: nat) (x: A),
  all (fun a => a = x) (replicate n x).
Proof.
  intros A n x.
  induction n.
    unfold replicate.
    unfold all.
    exact I.
    
    simpl.
    split.
      reflexivity.
      
      exact IHn.
Qed.


Fixpoint append {A} (xs ys: List A): List A :=
  match xs with
  | Nil => ys
  | Cons x xs => Cons x (append xs ys)
  end.

Theorem Ex_13_5_1 : forall (A: Type) (xs: List A), append xs Nil = xs.
Proof.
  intros A xs.
  induction xs.
    simpl.
    reflexivity.
    
    simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Theorem Ex_13_5_2 : forall (A: Type) (xs ys zs: List A),
  append xs (append ys zs) = append (append xs ys) zs.
Proof.
  intros A xs ys zs.
  induction xs.
    simpl.
    reflexivity.
    
    simpl.
    rewrite IHxs.
    reflexivity.
Qed.


Fixpoint reverse {A} (xs: List A): List A :=
  match xs with
  | Nil => Nil
  | Cons x xs => append (reverse xs) (Cons x Nil)
  end.

(* proof of section 13.5 *)
Lemma reverse_assoc : forall (A: Type) (xs ys: List A),
  reverse (append xs ys) = append (reverse ys) (reverse xs).
Proof.
  intros A xs ys.
  induction xs.
    simpl.
    rewrite (Ex_13_5_1 A (reverse ys)).
    reflexivity.
    
    simpl.
    rewrite IHxs.
    rewrite <- (Ex_13_5_2 A (reverse ys) (reverse xs) (Cons a Nil)).
    reflexivity.
Qed.
Theorem r_r_xs_eq_xs : forall (A: Type) (xs: List A),
  reverse (reverse xs) = xs.
Proof.
  intros A xs.
  induction xs.
    simpl.
    reflexivity.
    
    simpl.
    rewrite (reverse_assoc A (reverse xs) (Cons a Nil)).
    simpl.
    rewrite IHxs.
    reflexivity.
Qed.

(* proof of exercise 13.6 *)
Lemma reverse_xs_x_eq_x_reverse_xs : forall (A: Type) (x: A) (xs: List A),
  reverse (append xs (Cons x Nil)) = Cons x (reverse xs).
Proof.
  intros A x xs.
  induction xs.
    simpl.
    reflexivity.
    
    simpl.
    rewrite IHxs.
    simpl.
    reflexivity.
Qed.
Theorem Ex_13_6 : forall (A: Type) (xs: List A),
  reverse (reverse xs) = xs.
Proof.
  intros A xs.
  induction xs.
    simpl.
    reflexivity.
    
    simpl.
    rewrite (reverse_xs_x_eq_x_reverse_xs A a (reverse xs)).
    rewrite IHxs.
    reflexivity.
Qed.


Fixpoint map {A B} (f: A -> B) (xs: List A): List B :=
  match xs with
  | Nil => Nil
  | Cons x xs => Cons (f x) (map f xs)
  end.

Definition compose {A B C} (f: B -> C) (g: A -> B) (x: A): C := f (g x).

Theorem Ex_13_7 : forall (A B C: Type) (f: B -> C) (g: A -> B) (xs: List A),
  map f (map g xs) = map (compose f g) xs.
Proof.
  intros A B C f g xs.
  induction xs.
    simpl.
    reflexivity.
    
    simpl.
    rewrite IHxs.
    unfold compose.
    reflexivity.
Qed.


Fixpoint take {A} (n: nat) (xs: List A): List A :=
  match n, xs with
  | 0, _ => Nil
  | _, Nil => Nil
  | S n, Cons x xs => Cons x (take n xs)
  end.
Fixpoint drop{A} (n: nat) (xs: List A): List A :=
  match n, xs with
  | 0, _ => xs
  | _, Nil => Nil
  | S n, Cons _ xs => drop n xs
  end.

Theorem Ex_13_8 : forall (A: Type) (n: nat) (xs: List A),
  append (take n xs) (drop n xs) = xs.
Proof.
  intros A n.
  induction n.
    intro xs.
    simpl.
    reflexivity.
    
    destruct xs.
      simpl.
      reflexivity.
      
      simpl.
      rewrite (IHn xs).
      reflexivity.
Qed.


Inductive Tree (A: Type) :=
 | Leaf: A -> Tree A
 | Node: Tree A -> Tree A -> Tree A.

Fixpoint leafs {A} (xs: Tree A): nat :=
  match xs with
  | Leaf _ => 1
  | Node l r => leafs l + leafs r
  end.
Fixpoint nodes {A} (xs: Tree A): nat :=
  match xs with
  | Leaf _ => 0
  | Node l r => S (nodes l + nodes r)
  end.

Require Import Arith.

Theorem Ex_13_9 : forall (A: Type) (xs: Tree A),
  leafs xs = S (nodes xs).
Proof.
  intro A.
  induction xs.
    simpl.
    reflexivity.
    
    simpl.
    rewrite IHxs1; rewrite IHxs2.
    rewrite <- (plus_Snm_nSm (S (nodes xs1)) (nodes xs2)).
    simpl.
    reflexivity.
Qed.
