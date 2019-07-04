Require Import Unicode.Utf8.

(* In the first section I prove 6 of the laws in constructive logic.
   The two requiring classical logic are proved in the next section. *)
Section Morgan_Constructive.

  Lemma Morgan1 : forall a b: Prop, (~a /\ ~b) -> ~(a \/ b).
  Proof.
    intros a b conj_of_neg.

    (* Split conj_of_neg in the hypothesis to its both parts by
       moving it in front of the goal as an antecedent of an implication: *)
    elim conj_of_neg ; intros not_a not_b.

    (* To prove the negation of a disjunction, let's assume the opposite
       and derive a contradiction in both of its cases: *)
    intro neg_of_disj.

    (* Now, deriving a contradiction is done directly from
       the hypothesis for both parts of the disjunction: *)
    elim neg_of_disj ;  assumption.
  Qed.

  Lemma Morgan2 : forall a b: Prop, ~(a \/ b) -> (~a /\ ~b).
  Proof.
    intros a b negated_disj.

    (* I'll prove the conjunction by proving both its parts: *)
    split.

    (* Need to prove ¬a. Assume the opposite: *)
    intro.

    (* Reaching a contradiction is the same as
       proving the opposite of a hypothesis: *)
    elim negated_disj.

    (* We have "a" and need "a \/ b". Done! *)
    left . assumption.

    (* The proof of ¬b is exactly the same: *)
    intro ; elim negated_disj ; right ; assumption.
  Qed.

  (* NOTE: The third law requires classical logic,
     its proof is in the next section. *)

  Lemma Morgan4: forall a b: Prop, (~a \/ ~b) -> ~(a /\ b).
  Proof.
    (* Let's attack the proof by assuming the antecedent. *)
    intros a b conj_of_neg.

    (* I'll prove the consequent for both cases of the disjunction. *)
    elim conj_of_neg.

    (* Now we have 2 analoguous goals - once we'll assume '¬a', and once '¬b'.
       In both cases I assume the opposite of the goal
       and triumphally reach a contradiction. *)

    intro not_a.
    intro conj_of_positive. (* This works because ¬ is "-> false" in disguise *)

    (*  Now we have ¬a and a /\ b in the hypothesis,
        which is already a contradiction.
        Let's prove it: *)

    (* First, assume 'a' and 'b' from "a /\ b" as an implication argument: *)
    elim conj_of_positive .

    (* Next fire the contradiction with the '¬a' from the hypothesis. *)
    intro ; contradiction.

    (* The next goal is exactly the same as the previous,
       no explanation needed here *)
    intros not_b conj_positive ; elim conj_positive ; intro ; contradiction.
  Qed.

  Variable A : nat → Prop.
  Lemma Morgan5: (exists x, ¬A x) → ¬(forall y, A y).
  Proof.
    intro exists_not.
    elim exists_not.
    intros x not_ax forall_yes.
    elim not_ax.
    apply forall_yes.
  Qed.

  Lemma Morgan7: ¬(exists x, A x) → (forall x, ¬A x).
  Proof.
    (* Assume that no `x` suits `A x` and then choose a random `x` *)
    intros not_exists x.

    (* Assume the opposite of the goal - `A x`.
       After that we'll need to reach a contradiction *)
    intro ax.

    (* To reach a contradiction,
       we need to prove the opposite of a hypothesis.
       Let's choose `not_exists` for the task: *)
    elim not_exists.

    (* Now we need to show `∃x: A x`.
       But on step 2 we assumed `A x` for the `x` chosen earlier.
       This means we can solve the goal directly from the assumptions: *)
    exists x; assumption.
  Qed.

  Lemma Morgan8: (forall x, ¬A x) → ¬(exists x, A x).
  Proof.
    (* Before we start, let me undress that sneaky '¬'.
       It'll make the proof 2 steps shorter at the end.
       The logic is simpler this way, too. *)
    unfold not.

    (* Assume that no `x` suits A x *)
    intro forall_not.

    (* And assume the opposite of the goal. *)
    intro exists_yes.

    (* Now we need to show our 2 hypotheses contradict.
       We can do this by proving the opposite of the second: *)
    elim exists_yes.

    (* ...which is exactly the first one! *)
    assumption.

    (* NOTE: If we do not unfold the ¬ in the beginning, 2 more steps are needed before `assumption`: (comment out the `unfold not` to check)

    intro x. (* Choose any X for the goal. *)
    intro Ax. (* Assume the antecedent of the implication *)

    (* We assumed forall_not, yet we found a `x` s.t. `A x`: *)
    elim forall_not with x.
    assumption.
     *)
  Qed.
End Morgan_Constructive.

Section ClassicMorgan.
  Definition excluded_middle := forall t : Prop, t ∨ ¬t.
  Definition double_negative := forall t : Prop, (¬¬ t) → t.

  Lemma Morgan6: excluded_middle → double_negative →
    forall A : nat → Prop,
    ¬(forall y, A y) → (exists x, ¬(A x)).
  Proof.
    intros EM DN.
    intros A not_forall_true.

    (* After we assumed everything we could, it's time fro the hard part! *)

    (* Now there are both cases for '¬A x'.
       Either there's a 'x' that makes it true, or there is not.
       In other words, either there is a 'x' that fits our goal, or there is not.
       Let's look at both cases by using the rule of the excluded middle: *)
    elim EM with (t := exists x, ¬A x). (* Choose ¬A x first as it's easier *)

    (* In the first case we just assumed the goal, the proof is trivial:  *)
    intro H ; exact H.

    (* In the second case, there is no 'x' fitting our goal.
       This means, we have a goal in the form (¬P → P).
       Clearly, we have to reach a contradiction.
       For this reason, let's assume the antecedent: *)
    intro not_exists_not.

    (* Now we have to show that our 2 hypotheses contradict,
       just like in Morgan6. To achieve this we'll try to
       prove the opposite of the first hypothesis, namely not_forall_true: *)
    elim not_forall_true.

    (* Choose any 'y': *)
    intro y.

    (* Honestly, I don't know how this happened,
       but here I saw I could use a law I previously proved for not_exists_not.
       A quick overview of the current situation:
       - We have a random y.
       - We have to prove that for this 'y', 'A y' is true.
       - We also have that no 'x' exists s.t. ¬A x is true. (by not_exists_not)
       The last one means that for no 'x', 'A x' is false. (1)
       That is, for any 'x', 'A x' is true. (2)
       This means it will be true for our chosen 'y' as well.

       And what gives us (2) from (1) is exactly the 7th law of de Morgan
       I proved earlier - it moves the negation inside and flips the quantifier.
     *)
    apply Morgan7 with (x := y) in not_exists_not.

    (* The rest is trivial with a double-negative elimination.
       The goal is 'A y' and the hypothesis has '¬¬A y': *)
    apply DN ; exact not_exists_not.
  Qed.

  Lemma Morgan3_converse: double_negative → excluded_middle →
    forall a b : Prop,
     ¬(a /\ b) -> ¬a \/ ¬b.
  Proof.
    (* Begin fire *)
    intros DN EM a b negated_conj.

    (* Gotta prove ¬a∨¬b from ¬(a∧b). Let's look at all cases for 'a': *)
    elim EM with (t := ¬a). (* Choose ¬a first, because it's easier *)

    (* 2 cases now. Either '¬a' or 'a' *)

    (* First, "¬a → (¬a ∨ ¬b)" is trivial: *)
    intros ; left ; assumption.

    (* In the second case, we have '¬¬a'. Let's clean it first: *)
    intro not_not_a ; apply DN in not_not_a.

    (* Got to prove (¬a ∨ ¬b), but the left part is not true.
       Therefore, our only hope is to prove the right part - '¬b':  *)
    right.

    (* If we assume 'b', reaching a contradiction is trivial: *)
    intro proof_of_b.

  
    (* For a contradiction, let's try to prove the opposite
       of a hypothesis - negated_conj: *)
    elim negated_conj.

    (* The rest of the proof is trivial as we have
       both 'a' and 'b' in the hypothesis: *)
    split ; assumption.
  Qed.

End ClassicMorgan.
