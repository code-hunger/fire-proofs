Require Import Unicode.Utf8.

Section Task_4_17_weak_is_strong.
  Variables A B C : Prop.
  Definition DN := forall p : Prop, ¬¬p → p.

  Lemma disj_forward: DN → (¬A → ¬B → False) → A ∨ B.
  Proof.
    intros DN weak_disj.
    apply DN.
    intro not_disj.
    apply weak_disj.
    intro proof_A.
    apply not_disj ; left ; assumption.
    intro proof_B.
    apply not_disj; right ; assumption.
  Qed.

  Lemma disj_backward: (A ∨ B) → ( ¬A → ¬B → False).
  Proof.
    intros disj_A_B not_A not_B.
    apply not_A.
    case disj_A_B.
    intro ; assumption.
    intro proof_B.
    elim not_B.
    assumption.
  Qed.

  Lemma conj_forward: DN → (¬(A → B → False)) → A ∧ B.
  Proof.
    intros DN weak_conj.
    apply DN.
    intro not_conj.
    apply weak_conj.
    intros proof_A proof_B.
    apply not_conj.
    apply conj ; assumption.
  Qed.

  Lemma conj_backward: A ∧ B → (¬(A → B → False)).
  Proof.
    intros conj_A_B weak_conj.
    elim conj_A_B ; intros.
    apply weak_conj ; assumption.
  Qed.

  Variable P : Set -> Prop.
  Lemma exists_forward: DN → (¬ forall x, ¬P x) → exists x, P x.
  Proof.
    intros DN weak_ex.
    apply DN.
    intro not_ex.
    apply weak_ex.
    intros x proof_P.
    apply not_ex.
    exists x.
    assumption.
  Qed.

  Lemma exists_backward : (exists x, P x) → ¬ forall x, ¬P x.
  Proof.
    intros exists_P forall_not.
    elim exists_P.
    intros x proof_P.
    elim forall_not with x.
    assumption.
  Qed.

End Task_4_17_weak_is_strong.
