---- MODULE CounterSystem ----

EXTENDS Naturals

CONSTANTS Step

VARIABLES outerX

MODULE InnerModule(x) ==
    VARIABLE x
    INIT x = 0
    NEXT x' = IF x < 3 THEN x + 1 ELSE x
    WF_vars == <<x>>
==

Init == outerX = 0

Next == \/ \E newOuterX \in {newOuterX \in Nat : /\ [][Step]_<<outerX>> 
                                                         /\ outerX' = newOuterX}
          \/ /\ [][~Step]_<<outerX>> 
             /\ outerX' = outerX

Spec == /\ Init
        /\ [][Next]_<<outerX>>
        /\ <><(outerX = 3)>_<<outerX>>

WF_vars == <<outerX>>

====