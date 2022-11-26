
Require Import Arith.

Fixpoint nat_fact (n:nat) : nat :=
    match n with
    | O => 1 
    | S p => S p * nat_fact p 
    end.


Fixpoint fib (n:nat) : nat :=
    match n with
    | O => 0
    | S q => 
        match q with
        | O => 1
        | S p => fib p + fib q
        end
    end.

Require Import ZArith.

Open Scope Z_scope.

Definition fact_aux (n:Z) :=
Z.iter n (fun p => (fst p + 1, snd p * (fst p + 1))) (0, 1).

Definition Z_fact (n:Z) := snd (fact_aux n).
Compute Z_fact 100.

Close Scope Z_scope.


