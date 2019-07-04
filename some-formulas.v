Require Import Unicode.Utf8.

Section Task_4_8.
  Variables A B C : Prop.
  Variable P : nat → Prop.

  Hypothesis EM: forall p : Prop, p ∨ ¬p.
  Hypothesis DN: forall p : Prop, ¬¬p → p.

  Lemma task1: (A → exists x, P x) → exists x, (A → P x).
  Proof.
    intros exists_P.
    apply DN.
    intro not_exists.

    (* To reach false, let's prove a hypothesis - exists_P - is wrong: *)
    elim exists_P.

    intros x Px.
    (* Again - for false, let's prove a hypothesis is wrong: *)
    elim not_exists.

    (* The 'x' and 'P x' we need are in the hypothesis: *)
    exists x ; intro ; assumption.

    (* Having proved that the consequent of the exists_P implication is wrong,
       we've got to prove its antecedent is true.
       Let's assume the opposite: *)
    apply DN ; intro not_A.

    (* For a contradiction, let's prove the opposite of a hypothesis: *)
    elim not_exists.

    (* Really, now's the hardest part of the proof.
       Took me probably 20 minutes.
       I initially proved the goal with 'forall' instead of 'exists',
       which is a stronger claim, but couldn't integrate it here.

       As the inner term (A → P x) is true for all x given our assumption (¬A),
       we really need to give it just a single x: *)
    exists 42 ; intro ; contradiction.
  Qed.

  Lemma task2: ((A → B) → C) → (A → C) → C.
    intros A_B_impl_C A_impl_C.

    apply DN ; intro not_C.

    (* Now we have (¬C) and (A → C) as hypotheses.
       Obviously, A can't be true.
       Otherwise the implication would be false, because C is false. *)

    (* As I need to reach a contradiction, it would be very useful to 
       have another hypothesis.

       As 'A' is false by the above argument, I shall try to add
       (¬A) to my hypotheses. *)

    (* A very easy way to do so is to look at the 2 possibilities for A.
       It might be possible to go without EM, but solving for 'A'
       is straightforward and we can quickly move to ¬A: *)
    elim EM with (p := A).

    intro proof_A.
    (* Having A and ¬C and (A → C), contradiction is easy: *)
    apply not_C in A_impl_C ; assumption.

    (* Now we're just as before the 'EM', but with '¬A' as hypothesis: *)
    intro not_A.

    (* ¬C forces ¬(A → B) because of '(A → B) → C': *)
    apply not_C in A_B_impl_C .

    (* A false goal and a false hypothesis? 
       Don't know where it came from, but it's easy: *)
    assumption.

    (* Need A → B while ¬A is available. Trivial: *)
    intro proof_A ; contradiction.
  Qed.

  Lemma task3: (A → B) ∨ (B → A).
  Proof.
    (* Looking at both cases for 'A' makes this extremely easy: *)
    elim EM with (p := A).

    intro proof_A.
    (* First, we have A. But there's a B → A on the right of the disjunction: *)
    right; intro; assumption.

    intro not_A.
    (* Next, we have ¬A. But there's A → B on the left of the disjunction: *)
    left; intro ; contradiction.
  Qed.

  Lemma task4: ((A → B) → A) → A.
  Proof.
    intro.
    (* Obviously, A can't be false in (A → B) → A. *)
    elim EM with (p := A).
    (* The first case - A → A - is trivial *)
    intros ; assumption.

    intro not_A.
    (* In the second case, we have '(A → B) → A' and a goal 'A'.
       Let's prove (A → B) instead: *)
    apply H.

    (* But that's easy, because we assumed ¬A: *)
    intro ; contradiction.
  Qed.

End Task_4_8.

