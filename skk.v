Definition I {A:Type} x:A := x.
Definition K {A B:Type} (x:A) (y:B) := x.
Definition F {A B:Type} (x:A) (y:B) := y.
Definition S {A B C:Type} (x:A->B->C) (y:A->B) (z:A) := x z (y z).

Theorem ki_f : forall (A B:Type)(x:A)(y:B), K I x y = F x y.
Proof.
  intros A B x y.
  unfold K.
  unfold I.
  unfold F.
  reflexivity.
Qed.

Theorem skk_i : forall (A B:Type)(x:A), S K (K:A->B->A) x = I x.
Proof.
  intros A B x.
  unfold S.
  unfold K.
  unfold I.
  reflexivity.
Qed.

