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

(* max関数の性質 *)
(* a >= b なら max a b は a と等しい *)
Theorem max_ret_a : forall (a b : Z),
  (a >= b) -> max a b = a.
Proof.
  intros a b. (* a, b を前提に置き、ゴールのforallを展開 *)
  unfold max. (* max関数を展開 *)
  unfold Zge. (* >= を展開 *)
    (* a >= b は (a ?= b) <> Lt に展開される *)
  destruct (a ?= b). (* a ?= b の値によって場合分け *)
    (* a ?= b が Eq の場合 *)
    (* Eq <> Lt -> a = a *)
    intro H. (* Eq <> Lt を H として前提へ*)
    (* a = a *)
    reflexivity. (* 反射律により、正しい *)
    (* a ?= b が Lt の場合 *)
    (* Lt <> Lt -> b = a *)
    intro H. (* Lt <> Lt を H として前提へ*)
    elim H. (* 前提HがFalseとなることを示す *)
      (* 前提がFalseであれば、あらゆる規則を導ける *)
      (* Lt <> Lt は ~ (Lt = Lt)、よって Lt = Lt を示す *)
    (* Lt = Lt *)
    reflexivity. (* 反射律により、正しい *)
    (* a ?= b が Gt の場合 *)
    (* Gt <> Lt -> b = a *)
    intro H. (* Gt <> Lt を H として前提へ*)
    (* a = a *)
    reflexivity. (* 反射律により、正しい *)
Qed.

(* a <= b なら max a b は b と等しい *)
Theorem max_ret_b : forall (a b : Z),
  (a <= b) -> max a b = b.
Proof.
  intros a b. (* a, b を前提に置き、ゴールのforallを展開 *)
  unfold max, Zle. (* max関数, <= を展開 *)
    (* a <= b は (a ?= b) <> Gt に展開される *)
  generalize (Zcompare_Eq_eq a b).
    (* 定理をゴールの前提に追加 *)
    (* Zcompare_Eq_eq : forall n m:Z, (n ?= m) = Eq -> n = m. *)
  destruct (a ?= b). (* a ?= b の値によって場合分け *)
    (* a ?= b が Eq の場合 *)
    intro H1. (* Eq = Eq -> a = b を H1 として前提へ *)
    intro H2. (* Eq <> Gt を H2 として前提へ *)
    apply H1. (* H1 をゴールに適用 *)
      (* H1 の前提 (Eq = Eq) がゴールになる *)
    (* Eq = Eq *)
    reflexivity. (* 反射律により、正しい *)
    (* a ?= b が Lt の場合 *)
    intros _ _. (* ゴールの前提部分を除去 (不要) *)
    (* b = b *)
    reflexivity. (* 反射律により、正しい *)
    (* a ?= b が Gt の場合 *)
    intros _ H. (* Gt <> Gt を H として前提へ*)
      (* 前の部分は不要なので除去 *)
    elim H. (* 前提HがFalseとなることを示す *)
    (* Gt = Gt *)
    reflexivity. (* 反射律により、正しい *)
Qed.
