Theorem and_1 : forall P Q:Prop, P -> Q -> P /\ Q.
Proof.
  intros; split; assumption.
Qed.

Theorem and_2 : forall P Q:Prop, P /\ Q -> P -> Q.
Proof.
  intros P Q H _; elim H.
  intros _ q; assumption.
Qed.

Theorem nn_1 : forall P:Prop, P -> ~~P.
Proof.
  intros P p np.
  contradiction.
Qed.

Theorem nn_2 : forall A:Prop, ~A <-> ~~~A.
Proof.
  intro P.
  split.
    intros na nna; contradiction.
    intros nnna a.
    apply nnna.
    intro na; contradiction.
Qed.

Theorem n_1 : forall A:Prop, ~ A <-> (A -> False).
Proof.
  intro A.
  split.
    intros na a; contradiction.
    intros H a; exact (H a).
Qed.

Theorem cp_1 : forall A B:Prop, (A -> B) -> (~B -> ~A).
Proof.
  intros A B H nb a.
  assert (b := H a); contradiction.
Qed.

Theorem cp_2 : forall A B:Prop, (~B -> ~A) <-> (A -> ~~B).
Proof.
  intros A B.
  split; intro H.
    intros a nb.
    assert (na := H nb); contradiction.
    intros nb a.
    assert (nbb := H a); contradiction.
Qed.

Theorem dist_1 : forall A B C:Prop, A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C).
Proof.
  intros A B C.
  split; intro H.
    elim H; intros a H1.
    elim H1; [intro b | intro c].
      left; split; assumption.
      right; split; assumption.
    elim H; intro H1.
      elim H1; intros a b.
      split; [ | left]; assumption.
      elim H1; intros a c.
      split; [ | right]; assumption.
Qed.

Theorem dist_2 : forall A B C:Prop, A \/ (B /\ C) <-> (A \/ B) /\ (A \/ C).
Proof.
  intros A B C.
  split; intro H.
    elim H; [intro a | intro H1].
      split; left; assumption.
      elim H1; intros b c.
      split; right; assumption.
    elim H; intros H1 H2.
      elim H1; [intro a | intro b].
        left; assumption.
        elim H2; [intro a | intro c].
          left; assumption.
          right; split; assumption.
Qed.

Theorem dm_1 : forall A B:Prop, (~A \/ ~B) -> ~(A /\ B).
Proof.
  intros A B H.
  intro H1.
  elim H; [intro na | intro nb].
    elim H1; intros a b; contradiction.
    elim H1; intros a b; contradiction.
Qed.

Theorem dm_2 : forall A B:Prop, (~A /\ ~B) -> ~(A \/ B).
Proof.
  intros A B H H1.
  elim H; intros na nb.
  elim H1; intros; contradiction.
Qed.

 
Theorem existn_nforall_1 :
  forall (A:Type)(P:A -> Prop),
  (exists a:A, ~ P a) -> (~ forall a:A, P a).
Proof.
  intros A P H1 H2; elim H1; auto.
Qed.

Theorem existn_nforall_2 :
  forall (A:Type)(P:A -> Prop),
  (forall a:A, P a) -> (exists a:A, ~ P a) -> False.
Proof.
  intros A P H1 H2; elim H2; auto.
Qed.


Lemma exists_forall : forall (A:Type)(P: A -> A -> Prop),
  (exists a:A, forall b:A, P a b) -> (forall b:A, exists a:A, P a b).
Proof.
  intros A P H1 a.
  elim H1.
  intros x H2.
  exists x.
  apply H2.
Qed.


Theorem 矛盾 : forall (矛 盾:Type)(突き通す:矛 -> 盾 -> Prop),
  (exists 最強の矛:矛, forall あらゆる盾:盾, 突き通す 最強の矛 あらゆる盾) ->
  (exists 最強の盾:盾, forall あらゆる矛:矛, ~ 突き通す あらゆる矛 最強の盾) ->
  False.
Proof.
  intros 矛 盾 突き通す.
  intros どんな盾でも貫く矛がある どんな矛でも防ぐ盾がある.
  elim どんな盾でも貫く矛がある.
  intros 最強の矛 最強の矛はあらゆる盾を貫く.
  elim どんな矛でも防ぐ盾がある.
  intros 最強の盾 最強の盾はあらゆる矛を防ぐ.
  apply (最強の盾はあらゆる矛を防ぐ 最強の矛).
  apply (最強の矛はあらゆる盾を貫く 最強の盾).
Qed.

