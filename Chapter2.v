Require Import List.
Require Import Arith.


(** Not actually an exersize I was just checking out how match works*)
Fixpoint odd n :=
  match n with
    0 => False
  | 1 => True
  | S (S p) => odd p 
  end.

(** Range Exersize*)
Fixpoint range (n:nat) :=
  match n with
    0 => nil
  | S p => (range p) ++ (p :: nil)
  end.

Compute range 5.

(** Sorting Exersize*)
Require Import Bool.

Definition endIsSorted (l : list nat) :=
  (orb ((length l) <? 2) ((nth 0 l 0) <=? (nth 1 l 0))).
  
Fixpoint isSorted (l: list nat) :=
  match l with
  | nil => true
  | _ :: tail => (andb (endIsSorted l) (isSorted tail))
  end.

Compute isSorted (1::2::3::nil).
Compute isSorted (1::4::3::nil).

(*Counting occurances in list Exersize*)

Fixpoint countOccurances (l : list nat) (n : nat) : nat :=
  match l with
  | nil => 0
  | head :: tail => if head =? n then 
      1 + (countOccurances tail n) else (countOccurances tail n)
  end.

Compute countOccurances (1::2::1::4::1::4::nil) 1.
Compute countOccurances (1::2::1::4::1::4::nil) 4.