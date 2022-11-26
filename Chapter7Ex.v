
Require Import Arith.

Check true.

Inductive Extype : Type :=
| Constant : Extype
| NaturalNode: nat -> Extype -> Extype -> Extype
| BoolNode: bool -> Extype -> Extype -> Extype -> Extype.

Check NaturalNode 5 Constant Constant.

Check BoolNode true (NaturalNode 5 Constant Constant) Constant Constant.

(*Other exersizes are in the Chapter7.v file since all the definitions are in there*)