---------------------------- MODULE spec ----------------------------

EXTENDS Integers

CONSTANTS ValSet, SpecificVal, DesignatedConst

VARIABLES chosen, mapping

TypeOK ==
    /\ chosen \in ValSet
    /\ mapping \in [ValSet -> Int]

Init ==
    /\ chosen = 0
    /\ mapping = [x \in ValSet |-> 0]

Next ==
    /\ mapping' = CASE chosen = SpecificVal -> [mapping EXCEPT ![SpecificVal] = DesignatedConst]
                  [] OTHER -> mapping
    /\ chosen' = chosen

Spec == Init /\ [][Next]_<<chosen, mapping>>

=========================================================================