Require Import Classical.

Theorem drinker: forall A: Type, forall P: A -> Prop,
  forall a: A,
  exists x: A, (P x -> forall y: A, P y).
Proof.
  intros A P a.
  apply NNPP.
  intro H1.
  apply H1.
  exists a.
  intros Pa y.
  apply NNPP.
  intro H2.
  apply H1.
  exists y.
  intro Py.
  contradiction.
Qed.

Lemma prenex: forall A: Type, forall P: A -> Prop,
  (forall x: A, exists y: A, P x /\ ~ P y)
  <-> ~ (exists x: A, P x -> forall y: A, P y).
Proof.
  intros A P.
  split.
    intro H1.
    apply all_not_not_ex.
    intro a.
    elim (H1 a).
    intros b H2.
    elim H2.
    intros Pa nPb H3.
    apply nPb.
    apply H3.
    exact Pa.
    
    intros H1 a.
    apply not_all_not_ex.
    intro H2.
    apply (H2 a).
    split.
      apply NNPP.
      intro H3.
      apply H1.
      exists a.
      intro H4.
      contradiction.
      
      intro H3.
      apply H1.
      exists a.
      intros _ y.
      assert (H4 := not_and_or (P a) (~ P y) (H2 y)).
      elim H4.
        intro nPa.
        contradiction.
        
        intro nnPy.
        apply NNPP.
        exact nnPy.
Qed.

Theorem drinker_with_prenex: forall A: Type, forall P: A -> Prop,
  forall a: A,
  exists x: A, (P x -> forall y: A, P y).
Proof.
  intros A P a.
  apply NNPP.
  intro H1.
  apply H1.
  exists a.
  intros Pa y.
  assert (H2 := proj2 (prenex A P) H1).
  assert (H3 := H2 y).
  elim H3.
  intros x H4.
  exact (proj1 H4).
Qed.

(*
Lemma all_conj: forall A: Type, forall P Q: A -> Prop,
  (forall x: A, P x) /\ (forall x: A, Q x)
  <-> (forall x: A, P x /\ Q x).
Proof.
intros A P Q.
split.
  intros H1 x.
  elim H1.
  intros H2 H3.
  split.
    exact (H2 x).
    
    exact (H3 x).
  
  intro H1.
  split.
    intro x.
    exact (proj1 (H1 x)).
    
    intro x.
    exact (proj2 (H1 x)).
Qed.
*)

(*
Lemma drinker1: forall A: Type, forall P: A -> Prop,
  (forall x : A, exists y : A, P x /\ ~ P y)
  -> (forall x : A, exists y : A, ~ P x \/ P y).
Proof.
intros A P H1 x.
exists x.
assert (H2 := classic (P x)).
elim H2.
  intro Px.
  right.
  exact Px.
  
  intro nPx.
  left.
  exact nPx.
Qed.
*)

