---- MODULE StateMachine ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS InitX, InitY

VARIABLES x, y

Init == /\ x \in SUBSET {1, 2, 3}
        /\ y = InitY

Next == \/ /\ x' = {}
           /\ y' = y
          \/ /\ x' \subseteq y'
             /\ x' = x \cup {e} 
                \E e \notin x: TRUE

FullSet == x = {1, 2, 3}

GainThree == x' = x \cup {3} /\ 3 \notin x

Spec == Init /\ [][Next]_<<x, y>>

THEOREM TLCGet("States") = 8
THEOREM TLCGet("FullSet") = 1
THEOREM TLCGet("GainThree") = 1
====