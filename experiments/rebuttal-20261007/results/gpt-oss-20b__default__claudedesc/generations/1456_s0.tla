MODULE SubsetTest
VARIABLES x, y

Init == /\ x \subseteq {1,2}
       /\ y = {1,2,3}

Next == /\ y' = y
        /\ x' \in SUBSET y'

TypeOK == x \subseteq {1,2,3}

Inv == y = {1,2,3} /\ \E x' : (x' \in SUBSET y) /\ (x' \subseteq {1})

FullSet == x = {1,2,3}
GainThree == Next /\ (3 \in x') /\ (3 \notin x)

\* @POSSIBLE FullSet
\* @POSSIBLE GainThree

Spec == Init /\ [][Next]_<<x,y>> /\ []TypeOK /\ []Inv