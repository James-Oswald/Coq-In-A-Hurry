
(*First Proof example *)
Lemma example2: forall a b: Prop, a /\ b -> b /\ a.
Proof.
    intros a b H.           (*Remove the universal introduction*)
    split.                  (*Split b /\ a and into seprate goals*)
    destruct H as [H1 H2].  (*Split a /\ b and into seprate hypothesis, H1 and H2*)
    exact H2.               (*H2 (b) is 'directly convertable' into goal b*)
    intuition.              (*Powerful auto prove nonsense, should use assumption.*)
Qed.

Lemma example3: forall a b: Prop, a \/ b -> b \/ a.
Proof.
    intros a b H.               (*Remove the universal and seprate the conclusion *)
    destruct H as [H1 | H2].    (*split the premise and conclusions to elim or*)
    right.                      (*look at right disjunct in conclusion*)                      
    assumption.                 (*H1 == right disjunct (a)*)
    left.                       (*look at left disjunct in conclusion*)  
    assumption.                 (*H2 == left disjunct (a)*)
Qed.

Check le_S.
Check le_n.

Lemma example4: 3 <= 5.
Proof.
    apply le_S.
    apply le_S.
    apply le_n.
Qed.

Require Import Arith.
Check Nat.le_trans.

Lemma example5 : forall x y, x <= 10 -> 10 <= y -> x <= y.
Proof.
    intros x y xle10 yle10.
    apply Nat.le_trans with (m := 10). (*Bind a var to a set value*)
    assumption.
    assumption.
Qed.

SearchRewrite (_ * (_ + _)).
Check Nat.mul_add_distr_l.

(*Hell*)
Lemma example6 : forall x y, (x + y) * (x + y) = x*x + 2*x*y + y*y.
Proof.
    intros x y.
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.add_assoc.
    rewrite <- Nat.add_assoc with (n := x * x).
    rewrite Nat.mul_comm with (n:= y) (m:=x).
    rewrite <- (Nat.mul_1_l (x * y)) at 1.
    rewrite <- Nat.mul_succ_l.
    rewrite Nat.mul_assoc.
    reflexivity.
Qed.


(*Proving properties about Nat.pred*)
Print Nat.pred.

Lemma pred_S_eq : forall x y, x = S y -> Nat.pred x = y.
Proof.
    intros x y H.
    unfold Nat.pred.
    rewrite H.
    reflexivity.
Qed.








