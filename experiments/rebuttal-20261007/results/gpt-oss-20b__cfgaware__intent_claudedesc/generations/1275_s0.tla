------------------------------ MODULE InitDemo ------------------------------
EXTENDS Integers

VARIABLE x

(* Initialization: choose i in 0..1 such that i < 1, then set x = i *)
Init == \E i \in 0..1 : (i < 1) /\ (x = i)

(* No changes after initialization *)
Next == x' = x

Spec == Init /\ [] Next

Inv == x < 1

THEOREM InvIsInvariant == Spec => [] Inv
END InitDemo