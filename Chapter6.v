
Require Import Arith.
Require Import List.

Fixpoint insert n l :=
    match l with
    | nil => n::nil
    | a::tl => if n <=? a then n::l else a::insert n tl
    end.

Fixpoint sort l :=
    match l with
    | nil => nil
    | a::tl => insert a (sort tl)
    end.

Fixpoint count n l :=
    match l with
    | nil => 0
    | a::tl => let r := count n tl in if n =? a then 1 + r else r
    end.

(*Me proving that sort works*)
Lemma sort_example: sort (4::3::2::1::nil) = (1::2::3::4::nil).
Proof.
    unfold sort.
    simpl (insert 1 nil).
    simpl (insert 2 _).
    simpl (insert 3 _).
    simpl (insert 4 _).
    reflexivity.
Qed.

Lemma insert_incr : forall n l, count n (insert n l) = 1 + count n l.
Proof.
    intros n l.
    induction l.
    simpl count.
    rewrite Nat.eqb_refl.
    ring.

    simpl.
    case (n <=? a).
    simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
    simpl.
    case (n =? a).
    rewrite IHl.
    ring.
    rewrite IHl.
    ring.
Qed.

