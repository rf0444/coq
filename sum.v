(* �L�������W���[�����C���|�[�g *)
Require Import QArith.
(* ���X�g���W���[�����C���|�[�g *)
Require Import List.
(* �f�t�H���g�̉��Z�q��L�����̂��̂Ƃ��� *)
Open Scope Q_scope.

(* sum�֐��̒�` *)
Fixpoint sum (xs : list Q) : Q :=
  match xs with
    | nil => 0
    | x :: xs => x + sum xs
  end.

(* sum�֐��̃e�X�g *)
(* 1����10�܂ł̗v�f�������X�g��^�����55��Ԃ� *)
Theorem sum_1_2__10_returns_55 :
  sum (1#1::2#1::3#1::4#1::5#1::6#1::7#1::8#1::9#1::10#1::nil) = 55#1.
Proof.
  compute. (* �v�Z���� *)
  reflexivity. (* ���� = �E�� *)
Qed.

(* sum�֐��̐��� *)
(* sum(���X�g) = ���X�g�̐擪�v�f(nil�̏ꍇ��0) + sum(���X�g�̐擪�v�f�����������X�g(nil�̏ꍇ��nil)) *)
Theorem sum_head : forall (xs : list Q),
  sum xs = (hd (0#1) xs) + sum (tail xs).
Proof.
  intros. (* xs�𓱓� *)
  induction xs. (* xs�ɂ��Ă̋A�[�@���J�n *)
    (* sum nil = hd 0 nil + sum (tail nil) *)
    simpl. (* sum, hd, tail �֐���W�J *)
    (* 0 + 0 = 0 *)
    unfold Qplus. (* ���Z��W�J *)
    (* (�ȗ�) *)
    simpl. (* �W�J���ꂽ���Z���v�Z *)
    (* 0 = 0 *)
    reflexivity. (* ���� = �E�� *)
    
    (* sum (a::xs) = hd 0 (a::xs) + sum (tail (a::xs)) *)
    simpl. (* sum, hd, tail �֐���W�J *)
    (* a + sum xs = a + sum xs *)
    reflexivity. (* ���� = �E�� *)
Qed.

