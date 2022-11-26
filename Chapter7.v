
Require Import Arith.

Inductive BinaryTree : Type :=
| Leaf : BinaryTree
| Node : BinaryTree->BinaryTree->BinaryTree.

Check Node (Node Leaf Leaf) Leaf.

Check Leaf.

Check Node Leaf Leaf.

Definition max (a:nat) (b:nat) : nat := 
    if a <=? b then b else a.

Fixpoint TreeDepth (tree : BinaryTree) : nat := 
    match tree with 
    | Leaf => 0
    | Node leftc rightc => (max (TreeDepth rightc) (TreeDepth leftc)) + 1
    end.

Compute TreeDepth Leaf.
Compute TreeDepth (Node Leaf Leaf).
Compute TreeDepth (Node Leaf (Node Leaf (Node Leaf Leaf))).

Inductive bin : Type :=
    L : bin
    | N : bin -> bin -> bin.

Fixpoint flatten_aux (t1 t2:bin) : bin :=
    match t1 with
    | L => N L t2
    | N t'1 t'2 => flatten_aux t'1 (flatten_aux t'2 t2)
    end.

Fixpoint flatten (t:bin) : bin :=
    match t with
    | L => L 
    | N t1 t2 => flatten_aux t1 (flatten t2)
    end.

Fixpoint size (t:bin) : nat :=
    match t with
    | L => 1 
    | N t1 t2 => 1 + size t1 + size t2
    end.

Compute flatten (N (N L L) (N (N L L) L)).

Definition example7 (t : bin): bool :=
match t with N L L => false | _ => true end.

(*My Proof*)
Lemma example7_size : forall t, example7 t = false -> size t = 3.
Proof.
    induction t.
    simpl example7.
    discriminate.
    case t1.
    case t2.
    simpl.
    intros h; reflexivity.
    intros b0 b1.
    simpl.
    discriminate.
    intros b0 b1.
    simpl.
    discriminate.
Qed.
    
(*Book Proof*)
Lemma example7_size_book : forall t, example7 t = false -> size t = 3.
Proof.
    intros t.
    destruct t.
    simpl.
    discriminate.
    destruct t1.
    destruct t2.
    simpl.
    auto.
    simpl; discriminate.
    simpl; discriminate.
Qed.

(*My Proof*)
Lemma flatten_aux_size :
forall t1 t2, size (flatten_aux t1 t2) = size t1 + size t2 + 1.
Proof.
    induction t1.
    intros t2.
    simpl.
    ring.

    intros t2.
    simpl.
    rewrite IHt1_1.
    rewrite IHt1_2.
    ring.
Qed.

(*Book Proof*)
Lemma flatten_aux_size_book :
forall t1 t2, size (flatten_aux t1 t2) = size t1 + size t2 + 1.
Proof.
    induction t1.
    intros t2.
    simpl.
    ring. (*Same as my base case nice*)

    intros t2; simpl.
    rewrite IHt1_1.
    rewrite IHt1_2.
    ring. (*Wow same proof I used!*)
Qed.

(*Exersize, My proof*)
Lemma flatten_size : forall t, size (flatten t) = size t.
Proof.
    induction t.
    simpl.
    reflexivity.
    simpl.
    rewrite flatten_aux_size.
    rewrite IHt2.
    ring.
Qed.

Lemma not_subterm_self_l : forall x y, ~ x = N x y.
Proof.
    induction x.
    intros y.
    discriminate. (*Unsure why this works since*)

    intros y.
    intros abs.
    injection abs.
    intros H1 H2.

    assert (IHx1' : x1 <> N x1 x2).
    apply IHx1.
    case IHx1'.
    exact H2.
Qed.



