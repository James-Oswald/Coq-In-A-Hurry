

Require Import Arith.

Fixpoint sum_n n :=
    match n with
    | 0 => 0 
    | S p => p + sum_n p
    end.

(*My version*)
Lemma obvious : forall n, 2 * n = n + n.
Proof.
    intro N.
    rewrite BinInt.ZL0.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_1_l.
    reflexivity.
Qed.

Lemma sum_n_p : forall n, 2 * sum_n n + n = n * n.
Proof.
    induction n.

    (*Base Case*)
    unfold sum_n.
    rewrite Nat.mul_0_r.
    rewrite Nat.mul_0_r.
    rewrite Nat.add_0_r.
    reflexivity.

    (*inductive case*)
    unfold sum_n.
    fold sum_n.
    rewrite Nat.mul_add_distr_l.
    rewrite <- Nat.add_1_r with (n := n).
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_add_distr_r.
    rewrite <- IHn.
    rewrite Nat.mul_1_r.
    rewrite Nat.mul_1_r.
    rewrite Nat.mul_1_l.
    rewrite obvious.
    rewrite Nat.add_comm with (n := n + n) (m := 2 * sum_n n).
    rewrite <- Arith_prebase.plus_assoc_reverse_stt with (n := 2 * sum_n n).
    reflexivity.
Qed.

(*The books version (Cheating)*)
Lemma sum_n_p_book : forall n, 2 * sum_n n + n = n * n.
Proof.
    induction n.

    (*Base Case*)
    reflexivity. (*HOW*)

    (*inductive case*)
    assert (SnSn : S n * S n = n * n + 2 * n + 1).
    ring.
    rewrite SnSn.
    rewrite <- IHn.
    simpl.
    ring.
Qed.

Fixpoint evenb n :=
  match n with
    0 => true 
  | 1 => false
  | S (S p) => evenb p 
  end.

(*Book Version (I really hate this proof)*)
Lemma evenb_p : forall n, evenb n = true -> exists x, n = 2 * x.
Proof.
    (*Assert a stronger statement (Oh god how would you ever find this)*)
    assert (Main: forall n, (evenb n = true -> exists x, n = 2 * x) /\
    (evenb (S n) = true -> exists x, S n = 2 * x)).

    induction n.

    (*Base Case*)
    split.
    exists 0. (*Automatically applies intro*)
    ring.
    simpl. (*expands evenb 1 to false *)
    intros H. (*Move the contradition to the hyp*)
    discriminate. (*discard it*)

    (*Inductive Step*)
    split.
    destruct IHn as [_ IHn']. (*discard the non-S n case*)
    exact IHn'.
    simpl evenb.
    intros H.
    destruct IHn as [IHn' _].
    assert (H' : exists x, n = 2 * x).
    apply IHn'.
    exact H.
    destruct H' as [x q].
    exists (x + 1).
    rewrite q.
    ring.

    intros n ev.
    destruct (Main n) as [H _].
    apply H.
    exact ev.
Qed.

(*My version*)
(*
Lemma evenb_p_mine : forall n, evenb n = true -> exists x, n = 2 * x.
Proof.
    induction n.
    simpl evenb.
    exists 0.
    ring.

    destruct evenb.
    intuition.
Qed.
*)