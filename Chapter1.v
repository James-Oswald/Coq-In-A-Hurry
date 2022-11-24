

(*Technically we haven't learned how to do Definitions yet but I didn't want to type this twice so looked ahead*)
Definition sum5 (a1:nat) (a2:nat) (a3:nat) (a4:nat) (a5:nat) : nat :=
    a1 + a2 + a3 + a4 + a5.

Check sum5.

Compute sum5 1 1 1 1 1. (*5*)
Compute sum5 1 2 3 4 5. (*15*)