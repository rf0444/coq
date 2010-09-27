(* 有理数モジュールをインポート *)
Require Import QArith.
(* リストモジュールをインポート *)
Require Import List.
(* デフォルトの演算子を有理数のものとする *)
Open Scope Q_scope.

(* sum関数の定義 *)
Fixpoint sum (xs : list Q) : Q :=
  match xs with
    | nil => 0
    | x :: xs => x + sum xs
  end.

(* sum関数のテスト *)
(* 1から10までの要素を持つリストを与えると55を返す *)
Theorem sum_1_2__10_returns_55 :
  sum (1#1::2#1::3#1::4#1::5#1::6#1::7#1::8#1::9#1::10#1::nil) = 55#1.
Proof.
  compute. (* 計算する *)
  reflexivity. (* 左辺 = 右辺 *)
Qed.

(* sum関数の性質 *)
(* sum(リスト) = リストの先頭要素(nilの場合は0) + sum(リストの先頭要素を除いたリスト(nilの場合はnil)) *)
Theorem sum_head : forall (xs : list Q),
  sum xs = (hd (0#1) xs) + sum (tail xs).
Proof.
  intros. (* xsを導入 *)
  induction xs. (* xsについての帰納法を開始 *)
    (* sum nil = hd 0 nil + sum (tail nil) *)
    simpl. (* sum, hd, tail 関数を展開 *)
    (* 0 + 0 = 0 *)
    unfold Qplus. (* 加算を展開 *)
    (* (省略) *)
    simpl. (* 展開された加算を計算 *)
    (* 0 = 0 *)
    reflexivity. (* 左辺 = 右辺 *)
    
    (* sum (a::xs) = hd 0 (a::xs) + sum (tail (a::xs)) *)
    simpl. (* sum, hd, tail 関数を展開 *)
    (* a + sum xs = a + sum xs *)
    reflexivity. (* 左辺 = 右辺 *)
Qed.

