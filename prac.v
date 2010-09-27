Section Prop_Logic.
  Lemma Coq_01 : forall A B C:Prop, (A->B->C) -> (A->B) -> A -> C.
    intros A B C H1 H2 a.
    exact (H1 a (H2 a)).
  Qed.
  Lemma Coq_02 : forall A B C:Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
    intros A B C H.
    elim H; intros a H1.
    elim H1; intros b c.
    split; [split | ]; assumption.
  Qed.
  Lemma Coq_03 : forall A B C D:Prop, (A -> C) /\ (B -> D) /\ A /\ B -> C /\ D.
    intros A B C D H.
    elim H; intros H0 H1.
    elim H1; intros H2 H3.
    elim H3; intros a b.
    split; [apply (H0 a) | apply (H2 b)]; assumption.
  Qed.
  Lemma Coq_04 : forall A : Prop, ~(A /\ ~A).
    intros A H.
    elim H; intros a na.
    elim na.
    assumption.
  Qed.
  Lemma Coq_05 : forall A B C:Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
    intros A B C H.
    elim H.
     intro a; left; left; assumption.
     intro H1; elim H1.
       intro b; left; right; assumption.
       intro c; right; assumption.
  Qed.
  Lemma Coq_06 : forall A, ~~~A -> ~A.
    intros A nnna.
    intro a.
    elim nnna; intro na.
    elim na; assumption.
  Qed.
  Lemma Coq_07 : forall A B:Prop, (A->B)->~B->~A.
   intros A B H1 nb.
   intro a.
   elim nb.
   exact (H1 a).
  Qed.
  Lemma Coq_08: forall A B:Prop, ((((A->B)->A)->A)->B)->B.
    intros A B H.
    apply H; intro H1.
    apply H1; intro a.
    apply H.
    intros _; assumption.
  Qed.
  Lemma Coq_09 : forall A:Prop, ~~(A\/~A).
    intros A H.
    elim H.
    right; intro a.
    elim H; left; assumption.
  Qed.
End Prop_Logic.
