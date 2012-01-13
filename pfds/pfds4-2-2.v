
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

Fixpoint take_cps {A B} (n: nat) (s: Stream A) (cont: Stream A -> B): B :=
  match n, s with
  | _, F Nil => cont FNil
  | 0, _ => cont FNil
  | S m, F (Cons x xs) => take_cps m xs (fun s' => cont (x :: s'))
  end.

Definition insertBy_cps {A B} (cmp: A -> A -> comparison) (a: A) (s: Stream A) (cont: Stream A -> B): B :=
  (fix insertBy' (c: StreamCell A) (cont': Stream A -> B): B :=
    match c with
    | Nil => cont' (a :: FNil)
    | Cons x xs => match cmp a x with
      | Eq | Lt => cont' (a :: F c)
      | Gt => insertBy' (force xs) (fun s' => cont' (x :: s'))
      end
    end
  ) (force s) cont.

Definition foldr_cps {A B C} (f: A -> B -> B) (b: B) (s: Stream A) (cont: B -> C): C :=
  (fix foldr' (c: StreamCell A) (cont': B -> C): C :=
    match c with
    | Nil => cont' b
    | Cons x xs => foldr' (force xs) (fun b' => cont' (f x b'))
    end
  ) (force s) cont.


(* つかってみる *)

Definition I {A} (a: A) := a.

Definition isort {A} (cmp: A -> A -> comparison) (s: Stream A): Stream A :=
  foldr_cps (fun a s => insertBy_cps cmp a s I) FNil s I.

Require Import Arith.

(* TODO: 計算コスト関数を定義する *)

Definition d_take_cost {A} (n m: nat) (s: Stream A): nat :=
  let take_cont := length in
  take_cps m s (fun s' => take_cps n s take_cont).

Definition isort_ord {A} (cmp: A -> A -> comparison) (s: Stream A): nat :=
  let ins_cont := I in
  let fold_cont := length in
  foldr_cps (fun a s' => insertBy_cps cmp a s' ins_cont) FNil s fold_cont.



