
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

(* normal impl *)

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

(* lazy with cost *)

Definition filter {A} (f: A -> bool) (s: Stream A): Stream A :=
  (fix filter' (c: StreamCell A) :=
    match c with
    | Nil => FNil
    | Cons x xs => if (f x) then x :: filter' (force xs) else filter' (force xs) end
  ) (force s).

Definition map {A B} (f: A -> B) (s: Stream A): Stream B :=
  (fix map' (c: StreamCell A) :=
    match c with
    | Nil => FNil
    | Cons x xs => f x :: map' (force xs)
    end
  ) (force s).


Inductive LazyCostStream (A: Type) :=
| None : nat -> LazyCostStream A
| Some : Stream (A * nat) -> LazyCostStream A.

Implicit Arguments None [A].
Implicit Arguments Some [A].

Definition StoL {A} (s: Stream A): LazyCostStream A :=
  match (force s) with
  | Nil => None 0
  | _ => Some (map (fun x => (x, 0)) s)
  end.

Require Import Arith.

(*
Fixpoint take' {A} (n: nat) (s: Stream A): LazyCostStream A :=
  match n, s with
  | _, F Nil => (FNil, 1) :: FNil
  | 0, _ => (FNil, 1) :: FNil
  | S m, F (Cons x xs) =>
    let f := fun ele => match ele with (xs', cost) => (x::xs', S cost) end
    in map f ((FNil, 1) :: take' m xs)
  end.
*)

Definition take' {A} (n: nat) (lcs: LazyCostStream A): LazyCostStream A :=
  match lcs with
  | None cost => None (S cost)
  | Some s =>
    let take'' := (fix take'' (n: nat) (s: Stream (A * nat)) (cost: nat) :=
      match n, s with
      | _, F Nil => None cost
      | O, _ => None cost
      | S m, F (Cons (x, c) xs) => match take'' m xs (S cost) with
        | None _ => Some ((x, c + cost) :: FNil)
        | Some ss => Some ((x, c + cost) :: ss)
        end
      end
    ) in take'' n s 1
  end.

Definition insertBy' {A} (cmp: A -> A -> comparison) (a: A) (lcs: LazyCostStream A): LazyCostStream A :=
  match lcs with
  | None cost => Some ((a, S cost) :: FNil)
  | Some s =>
    let insertBy'' := (fix insertBy'' (sc: StreamCell (A * nat)) (cost: nat) :=
      match sc with
      | Nil => Some ((a, S cost) :: FNil)
      | Cons (x, c) xs => match cmp a x with
        | Eq | Lt => Some ((a, c + cost) :: map (fun e => match e with (x, c) => (x, c + cost) end) (F sc))
        | Gt => match insertBy'' (force xs) (S cost) with
          | None _ => Some ((x, c + cost) :: FNil)
          | Some ss => Some ((x, c + cost) :: ss)
          end
        end
      end
    ) in insertBy'' (force s) 1
  end.

Definition foldr' {A B} (f: A -> LazyCostStream B -> LazyCostStream B) (b: LazyCostStream B) (lcs: LazyCostStream A): LazyCostStream B :=
  match lcs with
  | None cost => match b with
    | None cost' => None (cost + cost')
    | Some bs => Some (map (fun e => match e with (x, c) => (x, S c) end) bs)
    end
  | Some s =>
    let foldr'' := (fix foldr'' (sc: StreamCell (A * nat)) (cost: nat) :=
      match sc with
      | Nil => match b with
        | None cost' => None (cost' + cost)
        | Some s => Some (map (fun e => match e with (x, c) => (x, c + cost) end) s)
        end
      | Cons (x, c) xs => match f x (foldr'' (force xs) (S cost)) with
        | None c => None (S c)
        | Some s => Some (map (fun e => match e with (x, c) => (x, c + cost) end) s)
        end
      end
    ) in foldr'' (force s) 1
  end.

Definition isort' {A} (cmp: A -> A -> comparison) (s: LazyCostStream A): LazyCostStream A :=
  foldr' (insertBy' cmp) (StoL FNil) s.

(* for test *)
(* todo: i < j -> cost_i < cost_j *)

Goal isort' nat_compare (StoL (5::2::7::4::3::FNil)) = None 0.
  compute.


