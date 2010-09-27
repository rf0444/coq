(* 整数モジュールをインポート *)
Require Import ZArith.
(* デフォルトの演算子を整数のものとする *)
Open Scope Z_scope.

(* max関数の定義 *)
Definition max (a b : Z) : Z :=
  match a ?= b with
    | Eq | Gt => a
    | Lt => b
  end.

(* max関数のテスト *)
(* max 1 3 は 3 を返す *)
Theorem max_1_3_returns_3 : max 1 3 = 3.
Proof.
  unfold max. (* max関数を展開 *)
  simpl. (* 計算可能な部分を計算 *)
  reflexivity. (* 左辺 = 右辺 *)
Qed.

(* max 19 5 は 19 を返す *)
Theorem max_19_5_returns_19 : max 19 5 = 19.
Proof.
  (* 先のテストケースと同様 *)
  unfold max.
  simpl.
  reflexivity.
Qed.

(* max関数の性質 *) (* 証明学習中 *)
(* a >= b なら max a b は a と等しい *)
Theorem max_ret_a : forall (a b : Z),
  (a >= b) -> max a b = a.
Proof.
  intros a b;
  unfold max, Zge;
  destruct (a ?= b);
  auto.
  intro H;
  elim H;
  auto.
Qed.

(* a <= b なら max a b は b と等しい *)
Theorem max_ret_b : forall (a b : Z),
  (a <= b) -> max a b = b.
Proof.
  intros a b;
  unfold max, Zle.
  generalize (Zcompare_Eq_eq a b).
  destruct (a ?= b);
  auto.
  intros _ H;
  elim H;
  auto.
Qed.

(* 証明用小定理 *)
Lemma max_case_strong : forall (n m : Z) (P : Z -> Type), 
  (m <= n -> P n) -> (n <= m -> P m) -> P (max n m).
Proof.
  intros n m P H1 H2;
  unfold max, Zle, Zge in *.
  rewrite <- (Zcompare_antisym n m) in H1.
  destruct (n ?= m);
  (apply H1|| apply H2);
  discriminate.
Qed.

(* max a b の結果は a 以上 *)
Theorem max_bigger_a : forall (a b : Z),
  max a b >= a.
Proof.
  intros;
  apply max_case_strong;
  auto with zarith.
Qed.

(* max a b の結果は b 以上 *)
Theorem max_bigger_b : forall (a b :Z),
  max a b >= b.
Proof.
  intros;
  apply max_case_strong;
  auto with zarith.
Qed.

(* 証明用小定理 *)
Lemma max_case : forall (n m : Z) (P : Z -> Type), P n -> P m -> P (max n m).
Proof.
  intros n m P H1 H2;
  unfold max in |- *;
  case (n ?= m);
  auto with arith.
Qed.

(* max a b は a と b の上限となる *)
Theorem max_upper : forall (a b c : Z),
  (a <= c) -> (b <= c) -> max a b <= c.
Proof.
  intros;
  apply max_case;
  assumption.
Qed.

(* max関数は結合律を満たす *)
Theorem max_associative : forall (a b c : Z),
  max (max a b) c = max a (max b c).
Proof.
  intros a b c;
  repeat apply max_case_strong;
  intros;
  reflexivity || (try apply Zle_antisym);
  eauto with zarith.
Qed.

(* max関数は可換律を満たす *)
Theorem max_commutative : forall (a b : Z),
  max a b = max b a.
Proof.
  intros;
  do 2 apply max_case_strong;
  intros;
  reflexivity || (try apply Zle_antisym);
  eauto with zarith.
Qed.

