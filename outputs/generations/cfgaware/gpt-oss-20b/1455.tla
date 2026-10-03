------------------------------ MODULE SubsetSpec ------------------------------
EXTENDS Naturals, Integers

VARIABLE b

(* Powerset of a set S *)
SUBSET(S) == { z : z \subseteq S }

Init == b = TRUE

Next ==
  /\ b' = (
          SUBSET({1,2}) \subseteq SUBSET({1,2,3})
          /\ ~( SUBSET({1,2,3}) \subseteq SUBSET({1,2}) )
          /\ SUBSET(1..5) \subseteq SUBSET(1..10)
          /\ ~( SUBSET(1..10) \subseteq SUBSET(1..5))
          /\ SUBSET(Nat) \subseteq SUBSET(Int)
          /\ ~( SUBSET(Int) \subseteq SUBSET(Nat))
        )

Spec == Init /\ [][Next]_<<b>>

Inv == b = TRUE

==============================================================================