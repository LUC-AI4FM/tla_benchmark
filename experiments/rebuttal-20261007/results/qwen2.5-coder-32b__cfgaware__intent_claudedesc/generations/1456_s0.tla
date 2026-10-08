------------------------------- MODULE SubsetConstraint ------------------------------

CONSTANTS 
    Universe  \* The full three-element set

VARIABLES 
    X         \* A variable ranging over subsets of a small finite set
    Y         \* A constant variable fixed to the full three-element set

Init == /\ X \subseteq {1, 2}
        /\ Y = Universe

Next == /\ X' \subseteq Y
        /\ Y' = Y

TypeOK == /\ X \subseteq Universe
          /\ Y = Universe

Inv == /\ X \subseteq Universe
       /\ ENABLED (X' = {1} \/ X' = {2} \/ X' = {1, 2})

Spec == Init /\ [][Next]_<<X>>

THEOREM Spec => []TypeOK

THEOREM Spec => [](Inv)

(* TLC configuration *)
CONSTANTS _cell_
VARIABLES _trace_

InitTLC == Init
NextTLC == Next
StatePred1(s) == s.X = Universe
StatePred2(s, s') == \E x \notin s.X : x \in s'.X

SpecTLC == InitTLC /\ [][NextTLC]_<<X>>

PROPERTY SpecTLC => _POSSIBLE{StatePred1} = 1
PROPERTY SpecTLC => _POSSIBLE{StatePred2} = 3

=============================================================================