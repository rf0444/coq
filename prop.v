Theorem and_1 : forall P Q:Prop, P -> Q -> P /\ Q.
Proof.
  intros; split; assumption.
Qed.

Theorem and_2 : forall P Q:Prop, P /\ Q -> P -> Q.
  intros P Q H _; elim H.
  intros _ q; assumption.
Qed.

Theorem nn_1 : forall P:Prop, P -> ~~P.
Proof.
  intros P p np.
  contradiction.
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

