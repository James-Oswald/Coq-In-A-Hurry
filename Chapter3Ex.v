
Lemma ex1: forall A B C:Prop, A/\(B/\C)->(A/\B)/\C.
Proof.
    intros A B C H.
    destruct H as [H1 Ht].
    destruct Ht as [H2 H3].
    split.
    split.
    assumption.
    assumption.
    assumption.
Qed.

Lemma ex2: forall A B C D: Prop,(A->B)/\(C->D)/\A/\C -> B/\D.
Proof.
    intros A B C D H.
    destruct H as [ab [cd [a c]]].
    split.
    apply ab.
    assumption.
    apply cd.
    assumption.
Qed.

Lemma ex3: forall A: Prop, ~(A/\~A).
Proof.
    intros a P.
    destruct P as [A NA].
    elim NA.
    assumption.
Qed.

Lemma ex4: forall A B C: Prop, A\/(B\/C)->(A\/B)\/C.
Proof.
    intros A B C H.
    destruct H as [H1 | [H2 | H3]].
    left; left.
    assumption.
    left; right.
    assumption.
    right.
    assumption.
Qed.

Lemma ex5: forall A B: Prop, (A\/B)/\~A -> B.
Proof.
    intros A B H.
    destruct H as [[H1 | H2] H3].
    elim H3.
    assumption.
    assumption.
Qed.

Lemma ex6: forall A:Type, forall P Q: A->Prop, 
(forall x, P x)\/(forall y, Q y)->forall x, P x\/Q x.
Proof.
    intros A P Q H.
    destruct H as [H1 | H2].
    intros X.
    left.
    apply H1 with (x:=X).
    intros X.
    right.
    apply H2 with (y:=X).
Qed.



