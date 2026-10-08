MODULE SmallSM
EXTENDS Naturals

CONSTANTS MyNat
VARIABLES x

(* State predicate *)
Inv == x \in MyNat

(* Initial condition *)
Init == x = 0 /\ Inv

(* Actions *)
A ==
    /\ x < 30
    /\ x' = x + 1

BandC ==
    /\ x > 0
    /\ x' = x - 1

DandE ==
    x' = x

Next == A \/ BandC \/ DandE

Spec == Init /\ Inv /\ [][Next]_x

END MODULE