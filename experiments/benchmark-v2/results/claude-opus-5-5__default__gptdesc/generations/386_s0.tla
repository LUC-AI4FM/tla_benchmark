---------------------------- MODULE test216 ----------------------------
EXTENDS Naturals

CONSTANT D

ASSUME D + 0 = 42

THEOREM D + 0 = 42

Foo == D + 0 = 42

INSTANCE test216b WITH E <- D, y <- 0

I == INSTANCE test216b WITH E <- D, y <- 0

(* There are no state variables, so the behavior is trivial. *)
Init == TRUE

Next == TRUE

Spec == Init /\ [][Next]_<<>>

Inv == Foo

THEOREM Spec => []Inv
=============================================================================