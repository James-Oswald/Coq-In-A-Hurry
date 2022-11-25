
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
    
Lemma insert_incr : forall n l, count n (insert n l) = 1 + count n l.
Proof.
    intros n l.
    induction l.
    simpl.
