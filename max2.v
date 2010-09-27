(* �������W���[�����C���|�[�g *)
Require Import ZArith.
(* �f�t�H���g�̉��Z�q�𐮐��̂��̂Ƃ��� *)
Open Scope Z_scope.

(* max�֐��̒�` *)
Definition max (a b : Z) : Z :=
  match a ?= b with
    | Eq | Gt => a
    | Lt => b
  end.

(* max�֐��̃e�X�g *)
(* max 1 3 �� 3 ��Ԃ� *)
Theorem max_1_3_returns_3 : max 1 3 = 3.
Proof.
  unfold max. (* max�֐���W�J *)
  simpl. (* �v�Z�\�ȕ������v�Z *)
  reflexivity. (* ���� = �E�� *)
Qed.

(* max�֐��̐��� *)
(* a >= b �Ȃ� max a b �� a �Ɠ����� *)
Theorem max_ret_a : forall (a b : Z),
  (a >= b) -> max a b = a.
Proof.
  intros a b. (* a, b ��O��ɒu���A�S�[����forall��W�J *)
  unfold max. (* max�֐���W�J *)
  unfold Zge. (* >= ��W�J *)
    (* a >= b �� (a ?= b) <> Lt �ɓW�J����� *)
  destruct (a ?= b). (* a ?= b �̒l�ɂ���ďꍇ���� *)
    (* a ?= b �� Eq �̏ꍇ *)
    (* Eq <> Lt -> a = a *)
    intro H. (* Eq <> Lt �� H �Ƃ��đO���*)
    (* a = a *)
    reflexivity. (* ���˗��ɂ��A������ *)
    (* a ?= b �� Lt �̏ꍇ *)
    (* Lt <> Lt -> b = a *)
    intro H. (* Lt <> Lt �� H �Ƃ��đO���*)
    elim H. (* �O��H��False�ƂȂ邱�Ƃ����� *)
      (* �O��False�ł���΁A������K���𓱂��� *)
      (* Lt <> Lt �� ~ (Lt = Lt)�A����� Lt = Lt ������ *)
    (* Lt = Lt *)
    reflexivity. (* ���˗��ɂ��A������ *)
    (* a ?= b �� Gt �̏ꍇ *)
    (* Gt <> Lt -> b = a *)
    intro H. (* Gt <> Lt �� H �Ƃ��đO���*)
    (* a = a *)
    reflexivity. (* ���˗��ɂ��A������ *)
Qed.

(* a <= b �Ȃ� max a b �� b �Ɠ����� *)
Theorem max_ret_b : forall (a b : Z),
  (a <= b) -> max a b = b.
Proof.
  intros a b. (* a, b ��O��ɒu���A�S�[����forall��W�J *)
  unfold max, Zle. (* max�֐�, <= ��W�J *)
    (* a <= b �� (a ?= b) <> Gt �ɓW�J����� *)
  generalize (Zcompare_Eq_eq a b).
    (* �藝���S�[���̑O��ɒǉ� *)
    (* Zcompare_Eq_eq : forall n m:Z, (n ?= m) = Eq -> n = m. *)
  destruct (a ?= b). (* a ?= b �̒l�ɂ���ďꍇ���� *)
    (* a ?= b �� Eq �̏ꍇ *)
    intro H1. (* Eq = Eq -> a = b �� H1 �Ƃ��đO��� *)
    intro H2. (* Eq <> Gt �� H2 �Ƃ��đO��� *)
    apply H1. (* H1 ���S�[���ɓK�p *)
      (* H1 �̑O�� (Eq = Eq) ���S�[���ɂȂ� *)
    (* Eq = Eq *)
    reflexivity. (* ���˗��ɂ��A������ *)
    (* a ?= b �� Lt �̏ꍇ *)
    intros _ _. (* �S�[���̑O�񕔕������� (�s�v) *)
    (* b = b *)
    reflexivity. (* ���˗��ɂ��A������ *)
    (* a ?= b �� Gt �̏ꍇ *)
    intros _ H. (* Gt <> Gt �� H �Ƃ��đO���*)
      (* �O�̕����͕s�v�Ȃ̂ŏ��� *)
    elim H. (* �O��H��False�ƂȂ邱�Ƃ����� *)
    (* Gt = Gt *)
    reflexivity. (* ���˗��ɂ��A������ *)
Qed.
