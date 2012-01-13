
Inductive susp (A: Type): Type :=
| F : A -> susp A.

Implicit Arguments F [A].

Definition force {A} (x: susp A): A :=
  match x with
  | F a => a
  end.

Inductive StreamCell (A: Type): Type :=
| Nil : StreamCell A
| Cons : A -> susp (StreamCell A) -> StreamCell A.

Implicit Arguments Nil [A].
Implicit Arguments Cons [A].

Definition Stream (A: Type): Type := susp (StreamCell A).

Definition FNil {A}: Stream A := F Nil.
Definition FCons {A} (x: A) (s: Stream A): Stream A := F (Cons x s).
Infix "::" := FCons (at level 60, right associativity).

Definition length {A} (s: Stream A): nat :=
  (fix length' (c: StreamCell A): nat :=
    match c with
    | Nil => 0
    | Cons _ xs => S (length' (force xs))
    end
  ) (force s).

Fixpoint take {A} (n: nat) (s: Stream A): Stream A :=
  match n, s with
  | _, F Nil => FNil
  | 0, _ => FNil
  | S m, F (Cons x xs) => x :: take m xs
  end.

Definition insertBy {A} (cmp: A -> A -> comparison) (a: A) (s: Stream A): Stream A :=
  (fix insertBy' (c: StreamCell A): Stream A :=
    match c with
    | Nil => a :: FNil
    | Cons x xs => match cmp a x with
      | Eq | Lt => a :: F c
      | Gt => x :: insertBy' (force xs)
      end
    end
  ) (force s).

Definition foldr {A B} (f: A -> B -> B) (b: B) (s: Stream A): B :=
  (fix foldr' (c: StreamCell A): B :=
    match c with
    | Nil => b
    | Cons x xs => f x (foldr' (force xs))
    end
  ) (force s).

Definition isort {A} (cmp: A -> A -> comparison) (s: Stream A): Stream A :=
  foldr (insertBy cmp) FNil s.

(* TODO: order をちゃんと定義 *)
Definition order {A} (a: A): nat := 1.

Require Import Arith.
Require Import Omega.

Theorem isort_o_nk:
  forall (A: Type) (n k: nat) (cmp: A -> A -> comparison) (s: Stream A),
  length s = n ->
  exists c1: nat, exists c2: nat, exists c3: nat,
  c1 < n -> c2 < k ->
  order(take k (isort cmp s)) < c3 * n * k.
Proof.
  intros A n k cmp s HL.
  evar (minl: nat); exists minl.
  evar (mink: nat); exists mink.
  evar (c: nat); exists c.
  intros LC LK.
  
  (* TODO: order対応 *)
  unfold order.
  apply lt_le_trans with (m := c * minl * mink).
    instantiate (1 := 2) in (Value of c).
    instantiate (1 := 2) in (Value of minl).
    instantiate (1 := 2) in (Value of mink).
    replace c with 2; [|auto].
    replace minl with 2; [|auto].
    replace mink with 2; [|auto].
    omega.
    
    repeat rewrite <- mult_assoc.
    apply mult_le_compat_l.
    apply mult_le_compat; apply lt_le_weak; auto.
Qed.


