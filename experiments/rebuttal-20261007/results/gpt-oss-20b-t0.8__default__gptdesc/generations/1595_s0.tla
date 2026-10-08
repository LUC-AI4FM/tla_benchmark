MODULE SimpleCounter
EXTENDS Naturals

VARIABLES x, pc

Init == 
    /\ x = 0
    /\ pc = "Inc"

Next ==
    \/ /\ pc = "Inc" /\ x < 10
       /\ x' = x + 1
       /\ pc' = IF x+1 < 10 THEN "Inc" ELSE "Done"
    \/ /\ pc = "Inc" /\ x >= 10
       /\ x' = x
       /\ pc' = "Done"
    \/ /\ pc = "Done"
       /\ x' = x
       /\ pc' = pc

vars == <<x, pc>>

SafetyInv ==
    /\ x \in Nat
    /\ pc \in {"Inc", "Done"}
    /\ x <= 10

AtFive == (x = 5)

FinishLoop == (pc = "Done")

PossibleCounts(n) == n \in 0..10

Termination == <> (pc = "Done")

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ Termination

END MODULE