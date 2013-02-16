Require Import Arith.

Inductive List A :=
 | Nil : List A
 | Cons : A -> List A -> List A.

Implicit Arguments Nil [A].
Implicit Arguments Cons [A].


Fixpoint append {A} (xs ys: List A): List A :=
  match xs with
   | Nil => ys
   | Cons x xs => Cons x (append xs ys)
  end. 

Fixpoint reverse {A} (xs: List A): List A :=
  match xs with
   | Nil => Nil
   | Cons x xs => append (reverse xs) (Cons x Nil)
  end.

Theorem append_nil : forall (A: Type) (xs: List A),
  append xs Nil = xs.
Proof.
  intros A xs.
  induction xs.
    reflexivity.
    
    simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Theorem append_assoc : forall (A: Type) (xs ys zs: List A),
  append xs (append ys zs) = append (append xs ys) zs.
Proof.
  intros A xs ys zs.
  induction xs.
    reflexivity.
    
    simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Theorem rev_assoc : forall (A: Type) (xs ys: List A),
  reverse (append xs ys) = append (reverse ys) (reverse xs).
Proof.
  intros A xs ys.
  induction xs.
    simpl.
    rewrite append_nil.
    reflexivity.
    
    simpl.
    rewrite append_assoc.
    rewrite IHxs.
    reflexivity.
Qed.

Theorem rev_rev : forall (A: Type) (xs: List A),
  reverse (reverse xs) = xs.
Proof.
  intros A xs.
  induction xs.
    reflexivity.
    
    simpl.
    rewrite rev_assoc.
    rewrite IHxs.
    reflexivity.
Qed.


Fixpoint get {A: Type} (xs: List A) (n: nat) (def: A): A :=
  match xs, n with
   | Cons x _, O => x
   | Cons _ xs, S n => get xs n def
   | _, _ => def
  end.

Fixpoint length {A: Type} (xs: List A): nat :=
  match xs with
   | Nil => O
   | Cons _ xs => S (length xs)
  end.

Theorem IFPH_4_2_12: forall (A: Type) (xs ys: List A) (k: nat) (def: A),
  let n := length xs in
  get (append xs ys) k def = match nat_compare k n with
   | Lt => get xs k def 
   | _ => get ys (k - n) def
  end.
Proof.
  intros A xs ys k def.
  simpl.
  generalize k.
  clear k.
  induction xs.
    intro k.
    simpl.
    destruct k.
      simpl. reflexivity.
      simpl. reflexivity.
    
    intro k.
    destruct k.
      simpl. reflexivity.
      simpl. rewrite (IHxs k). reflexivity.
Qed.